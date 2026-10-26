import V185TrunkScan23Chunk0434

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2572364 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2572364 : Nat := 118140960795 + 2572364 * 2 ^ 59
def prefixEnd_2572364 : Nat := 4983230072969 + 3 ^ 40 * 2572364 * 2
def baseEnd_2572364 : Nat := 1320859150322278847719919

theorem tailTrace_2572364 : CollatzResearch.WordTrace tailWord_2572364 prefixEnd_2572364 1320859150322278847719919 := by
  unfold tailWord_2572364
  simp only [CollatzResearch.WordTrace]
  refine ⟨46910911426386013819938073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62547881901848018426584097 46910911426386013819938073)
  ·
    refine ⟨35183183569789510364953555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46910911426386013819938073 35183183569789510364953555)
    ·
      refine ⟨52774775354684265547430333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35183183569789510364953555 52774775354684265547430333)
      ·
        refine ⟨19790540758006599580286375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52774775354684265547430333 19790540758006599580286375)
        ·
          refine ⟨29685811137009899370429563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19790540758006599580286375 29685811137009899370429563)
          ·
            refine ⟨44528716705514849055644345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29685811137009899370429563 44528716705514849055644345)
            ·
              refine ⟨33396537529136136791733259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44528716705514849055644345 33396537529136136791733259)
              ·
                refine ⟨50094806293704205187599889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33396537529136136791733259 50094806293704205187599889)
                ·
                  refine ⟨37571104720278153890699917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50094806293704205187599889 37571104720278153890699917)
                  ·
                    refine ⟨14089164270104307709012469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37571104720278153890699917 14089164270104307709012469)
                    ·
                      refine ⟨1320859150322278847719919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14089164270104307709012469 1320859150322278847719919)
                      ·
                        rfl

theorem cell23_2572364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2572364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572364 prefixEnd_2572364 := by exact prefixLift 2572364
  have htrace : WordTrace (prefixWord ++ tailWord_2572364) baseStart_2572364 baseEnd_2572364 := by
    simpa [prefixWord, tailWord_2572364, baseEnd_2572364] using wordTrace_append hprefix tailTrace_2572364
  have hstable : (prefixWord ++ tailWord_2572364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572364).length < 2 ^ (prefixWord ++ tailWord_2572364).sum := by decide
  have hdescent : baseEnd_2572364 < baseStart_2572364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572398 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2572398 : Nat := 118140960795 + 2572398 * 2 ^ 59
def prefixEnd_2572398 : Nat := 4983230072969 + 3 ^ 40 * 2572398 * 2
def baseEnd_2572398 : Nat := 1320876608664531714694763

theorem tailTrace_2572398 : CollatzResearch.WordTrace tailWord_2572398 prefixEnd_2572398 1320876608664531714694763 := by
  unfold tailWord_2572398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727882866831106430826731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62548708623099234297742565 11727882866831106430826731)
  ·
    refine ⟨17591824300246659646240097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727882866831106430826731 17591824300246659646240097)
    ·
      refine ⟨13193868225184994734680073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17591824300246659646240097 13193868225184994734680073)
      ·
        refine ⟨9895401168888746051010055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13193868225184994734680073 9895401168888746051010055)
        ·
          refine ⟨14843101753333119076515083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895401168888746051010055 14843101753333119076515083)
          ·
            refine ⟨22264652629999678614772625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14843101753333119076515083 22264652629999678614772625)
            ·
              refine ⟨16698489472499758961079469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22264652629999678614772625 16698489472499758961079469)
              ·
                refine ⟨6261933552187409610404801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16698489472499758961079469 6261933552187409610404801)
                ·
                  refine ⟨4696450164140557207803601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6261933552187409610404801 4696450164140557207803601)
                  ·
                    refine ⟨3522337623105417905852701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696450164140557207803601 3522337623105417905852701)
                    ·
                      refine ⟨1320876608664531714694763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3522337623105417905852701 1320876608664531714694763)
                      ·
                        rfl

theorem cell23_2572398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2572398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572398 prefixEnd_2572398 := by exact prefixLift 2572398
  have htrace : WordTrace (prefixWord ++ tailWord_2572398) baseStart_2572398 baseEnd_2572398 := by
    simpa [prefixWord, tailWord_2572398, baseEnd_2572398] using wordTrace_append hprefix tailTrace_2572398
  have hstable : (prefixWord ++ tailWord_2572398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572398).length < 2 ^ (prefixWord ++ tailWord_2572398).sum := by decide
  have hdescent : baseEnd_2572398 < baseStart_2572398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572448 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_2572448 : Nat := 118140960795 + 2572448 * 2 ^ 59
def prefixEnd_2572448 : Nat := 4983230072969 + 3 ^ 40 * 2572448 * 2
def baseEnd_2572448 : Nat := 440300760899085506356511

theorem tailTrace_2572448 : CollatzResearch.WordTrace tailWord_2572448 prefixEnd_2572448 440300760899085506356511 := by
  unfold tailWord_2572448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46912443292233854992966999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62549924389645139990622665 46912443292233854992966999)
  ·
    refine ⟨70368664938350782489450499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46912443292233854992966999 70368664938350782489450499)
    ·
      refine ⟨105552997407526173734175749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70368664938350782489450499 105552997407526173734175749)
      ·
        refine ⟨19791187013911157575157953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105552997407526173734175749 19791187013911157575157953)
        ·
          refine ⟨14843390260433368181368465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19791187013911157575157953 14843390260433368181368465)
          ·
            refine ⟨11132542695325026136026349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14843390260433368181368465 11132542695325026136026349)
            ·
              refine ⟨4174703510746884801009881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11132542695325026136026349 4174703510746884801009881)
              ·
                refine ⟨3131027633060163600757411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174703510746884801009881 3131027633060163600757411)
                ·
                  refine ⟨4696541449590245401136117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131027633060163600757411 4696541449590245401136117)
                  ·
                    refine ⟨440300760899085506356511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4696541449590245401136117 440300760899085506356511)
                    ·
                      rfl

theorem cell23_2572448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_2572448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572448 prefixEnd_2572448 := by exact prefixLift 2572448
  have htrace : WordTrace (prefixWord ++ tailWord_2572448) baseStart_2572448 baseEnd_2572448 := by
    simpa [prefixWord, tailWord_2572448, baseEnd_2572448] using wordTrace_append hprefix tailTrace_2572448
  have hstable : (prefixWord ++ tailWord_2572448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572448).length < 2 ^ (prefixWord ++ tailWord_2572448).sum := by decide
  have hdescent : baseEnd_2572448 < baseStart_2572448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572498 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2572498 : Nat := 118140960795 + 2572498 * 2 ^ 59
def prefixEnd_2572498 : Nat := 4983230072969 + 3 ^ 40 * 2572498 * 2
def baseEnd_2572498 : Nat := 1320927956729981323444303

theorem tailTrace_2572498 : CollatzResearch.WordTrace tailWord_2572498 prefixEnd_2572498 1320927956729981323444303 := by
  unfold tailWord_2572498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23456677558571642131313537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62551140156191045683502765 23456677558571642131313537)
  ·
    refine ⟨17592508168928731598485153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23456677558571642131313537 17592508168928731598485153)
    ·
      refine ⟨13194381126696548698863865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17592508168928731598485153 13194381126696548698863865)
      ·
        refine ⟨9895785845022411524147899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13194381126696548698863865 9895785845022411524147899)
        ·
          refine ⟨14843678767533617286221849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895785845022411524147899 14843678767533617286221849)
          ·
            refine ⟨11132759075650212964666387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14843678767533617286221849 11132759075650212964666387)
            ·
              refine ⟨16699138613475319446999581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11132759075650212964666387 16699138613475319446999581)
              ·
                refine ⟨6262176980053244792624843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16699138613475319446999581 6262176980053244792624843)
                ·
                  refine ⟨9393265470079867188937265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262176980053244792624843 9393265470079867188937265)
                  ·
                    refine ⟨7044949102559900391702949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9393265470079867188937265 7044949102559900391702949)
                    ·
                      refine ⟨1320927956729981323444303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7044949102559900391702949 1320927956729981323444303)
                      ·
                        rfl

theorem cell23_2572498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2572498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572498 prefixEnd_2572498 := by exact prefixLift 2572498
  have htrace : WordTrace (prefixWord ++ tailWord_2572498) baseStart_2572498 baseEnd_2572498 := by
    simpa [prefixWord, tailWord_2572498, baseEnd_2572498] using wordTrace_append hprefix tailTrace_2572498
  have hstable : (prefixWord ++ tailWord_2572498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572498).length < 2 ^ (prefixWord ++ tailWord_2572498).sum := by decide
  have hdescent : baseEnd_2572498 < baseStart_2572498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572519 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2572519 : Nat := 118140960795 + 2572519 * 2 ^ 59
def prefixEnd_2572519 : Nat := 4983230072969 + 3 ^ 40 * 2572519 * 2
def baseEnd_2572519 : Nat := 1320938739823725741281707

theorem tailTrace_2572519 : CollatzResearch.WordTrace tailWord_2572519 prefixEnd_2572519 1320938739823725741281707 := by
  unfold tailWord_2572519
  simp only [CollatzResearch.WordTrace]
  refine ⟨93827476167210489111768611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62551650778140326074512407 93827476167210489111768611)
  ·
    refine ⟨140741214250815733667652917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93827476167210489111768611 140741214250815733667652917)
    ·
      refine ⟨13194488836013975031342461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140741214250815733667652917 13194488836013975031342461)
      ·
        refine ⟨4947933313505240636753423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13194488836013975031342461 4947933313505240636753423)
        ·
          refine ⟨7421899970257860955130135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947933313505240636753423 7421899970257860955130135)
          ·
            refine ⟨11132849955386791432695203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421899970257860955130135 11132849955386791432695203)
            ·
              refine ⟨16699274933080187149042805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11132849955386791432695203 16699274933080187149042805)
              ·
                refine ⟨1565557024976267545222763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16699274933080187149042805 1565557024976267545222763)
                ·
                  refine ⟨2348335537464401317834145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565557024976267545222763 2348335537464401317834145)
                  ·
                    refine ⟨1761251653098300988375609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348335537464401317834145 1761251653098300988375609)
                    ·
                      refine ⟨1320938739823725741281707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761251653098300988375609 1320938739823725741281707)
                      ·
                        rfl

theorem cell23_2572519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2572519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572519 prefixEnd_2572519 := by exact prefixLift 2572519
  have htrace : WordTrace (prefixWord ++ tailWord_2572519) baseStart_2572519 baseEnd_2572519 := by
    simpa [prefixWord, tailWord_2572519, baseEnd_2572519] using wordTrace_append hprefix tailTrace_2572519
  have hstable : (prefixWord ++ tailWord_2572519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572519).length < 2 ^ (prefixWord ++ tailWord_2572519).sum := by decide
  have hdescent : baseEnd_2572519 < baseStart_2572519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572541 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2572541 : Nat := 118140960795 + 2572541 * 2 ^ 59
def prefixEnd_2572541 : Nat := 4983230072969 + 3 ^ 40 * 2572541 * 2
def baseEnd_2572541 : Nat := 1320950036398124655206605

theorem tailTrace_2572541 : CollatzResearch.WordTrace tailWord_2572541 prefixEnd_2572541 1320950036398124655206605 := by
  unfold tailWord_2572541
  simp only [CollatzResearch.WordTrace]
  refine ⟨93828278573130786869069477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62552185715420524579379651 93828278573130786869069477)
  ·
    refine ⟨17592802232462022537950527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93828278573130786869069477 17592802232462022537950527)
    ·
      refine ⟨26389203348693033806925791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17592802232462022537950527 26389203348693033806925791)
      ·
        refine ⟨39583805023039550710388687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26389203348693033806925791 39583805023039550710388687)
        ·
          refine ⟨59375707534559326065583031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39583805023039550710388687 59375707534559326065583031)
          ·
            refine ⟨89063561301838989098374547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59375707534559326065583031 89063561301838989098374547)
            ·
              refine ⟨133595341952758483647561821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89063561301838989098374547 133595341952758483647561821)
              ·
                refine ⟨50098253232284431367835683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133595341952758483647561821 50098253232284431367835683)
                ·
                  refine ⟨75147379848426647051753525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50098253232284431367835683 75147379848426647051753525)
                  ·
                    refine ⟨7045066860789998161101893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75147379848426647051753525 7045066860789998161101893)
                    ·
                      refine ⟨1320950036398124655206605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045066860789998161101893 1320950036398124655206605)
                      ·
                        rfl

theorem cell23_2572541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2572541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572541 prefixEnd_2572541 := by exact prefixLift 2572541
  have htrace : WordTrace (prefixWord ++ tailWord_2572541) baseStart_2572541 baseEnd_2572541 := by
    simpa [prefixWord, tailWord_2572541, baseEnd_2572541] using wordTrace_append hprefix tailTrace_2572541
  have hstable : (prefixWord ++ tailWord_2572541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572541).length < 2 ^ (prefixWord ++ tailWord_2572541).sum := by decide
  have hdescent : baseEnd_2572541 < baseStart_2572541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572571 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_2572571 : Nat := 118140960795 + 2572571 * 2 ^ 59
def prefixEnd_2572571 : Nat := 4983230072969 + 3 ^ 40 * 2572571 * 2
def baseEnd_2572571 : Nat := 1320965440817759537831467

theorem tailTrace_2572571 : CollatzResearch.WordTrace tailWord_2572571 prefixEnd_2572571 1320965440817759537831467 := by
  unfold tailWord_2572571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93829372763022101992661567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62552915175348067995107711 93829372763022101992661567)
  ·
    refine ⟨140744059144533152988992351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93829372763022101992661567 140744059144533152988992351)
    ·
      refine ⟨211116088716799729483488527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140744059144533152988992351 211116088716799729483488527)
      ·
        refine ⟨316674133075199594225232791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211116088716799729483488527 316674133075199594225232791)
        ·
          refine ⟨475011199612799391337849187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316674133075199594225232791 475011199612799391337849187)
          ·
            refine ⟨712516799419199087006773781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475011199612799391337849187 712516799419199087006773781)
            ·
              refine ⟨33399224972774957203442521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 712516799419199087006773781 33399224972774957203442521)
              ·
                refine ⟨25049418729581217902581891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33399224972774957203442521 25049418729581217902581891)
                ·
                  refine ⟨37574128094371826853872837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049418729581217902581891 37574128094371826853872837)
                  ·
                    refine ⟨7045149017694717535101157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37574128094371826853872837 7045149017694717535101157)
                    ·
                      refine ⟨1320965440817759537831467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045149017694717535101157 1320965440817759537831467)
                      ·
                        rfl

theorem cell23_2572571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_2572571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572571 prefixEnd_2572571 := by exact prefixLift 2572571
  have htrace : WordTrace (prefixWord ++ tailWord_2572571) baseStart_2572571 baseEnd_2572571 := by
    simpa [prefixWord, tailWord_2572571, baseEnd_2572571] using wordTrace_append hprefix tailTrace_2572571
  have hstable : (prefixWord ++ tailWord_2572571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572571).length < 2 ^ (prefixWord ++ tailWord_2572571).sum := by decide
  have hdescent : baseEnd_2572571 < baseStart_2572571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572578 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2572578 : Nat := 118140960795 + 2572578 * 2 ^ 59
def prefixEnd_2572578 : Nat := 4983230072969 + 3 ^ 40 * 2572578 * 2
def baseEnd_2572578 : Nat := 1320969035182341010443935

theorem tailTrace_2572578 : CollatzResearch.WordTrace tailWord_2572578 prefixEnd_2572578 1320969035182341010443935 := by
  unfold tailWord_2572578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23457407018499185547041597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62553085382664494792110925 23457407018499185547041597)
  ·
    refine ⟨8796527631937194580140599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23457407018499185547041597 8796527631937194580140599)
    ·
      refine ⟨13194791447905791870210899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796527631937194580140599 13194791447905791870210899)
      ·
        refine ⟨19792187171858687805316349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194791447905791870210899 19792187171858687805316349)
        ·
          refine ⟨7422070189447007926993631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19792187171858687805316349 7422070189447007926993631)
          ·
            refine ⟨11133105284170511890490447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7422070189447007926993631 11133105284170511890490447)
            ·
              refine ⟨16699657926255767835735671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11133105284170511890490447 16699657926255767835735671)
              ·
                refine ⟨25049486889383651753603507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699657926255767835735671 25049486889383651753603507)
                ·
                  refine ⟨37574230334075477630405261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049486889383651753603507 37574230334075477630405261)
                  ·
                    refine ⟨14090336375278304111401973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37574230334075477630405261 14090336375278304111401973)
                    ·
                      refine ⟨1320969035182341010443935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14090336375278304111401973 1320969035182341010443935)
                      ·
                        rfl

theorem cell23_2572578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2572578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572578 prefixEnd_2572578 := by exact prefixLift 2572578
  have htrace : WordTrace (prefixWord ++ tailWord_2572578) baseStart_2572578 baseEnd_2572578 := by
    simpa [prefixWord, tailWord_2572578, baseEnd_2572578] using wordTrace_append hprefix tailTrace_2572578
  have hstable : (prefixWord ++ tailWord_2572578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572578).length < 2 ^ (prefixWord ++ tailWord_2572578).sum := by decide
  have hdescent : baseEnd_2572578 < baseStart_2572578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572611 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 7]
def baseStart_2572611 : Nat := 118140960795 + 2572611 * 2 ^ 59
def prefixEnd_2572611 : Nat := 4983230072969 + 3 ^ 40 * 2572611 * 2
def baseEnd_2572611 : Nat := 440328660014646460443761

theorem tailTrace_2572611 : CollatzResearch.WordTrace tailWord_2572611 prefixEnd_2572611 440328660014646460443761 := by
  unfold tailWord_2572611
  simp only [CollatzResearch.WordTrace]
  refine ⟨93830831682877188824117687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62553887788584792549411791 93830831682877188824117687)
  ·
    refine ⟨140746247524315783236176531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93830831682877188824117687 140746247524315783236176531)
    ·
      refine ⟨211119371286473674854264797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140746247524315783236176531 211119371286473674854264797)
      ·
        refine ⟨79169764232427628070349299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211119371286473674854264797 79169764232427628070349299)
        ·
          refine ⟨118754646348641442105523949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79169764232427628070349299 118754646348641442105523949)
          ·
            refine ⟨44532992380740540789571481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118754646348641442105523949 44532992380740540789571481)
            ·
              refine ⟨33399744285555405592178611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44532992380740540789571481 33399744285555405592178611)
              ·
                refine ⟨50099616428333108388267917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33399744285555405592178611 50099616428333108388267917)
                ·
                  refine ⟨18787356160624915645600469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50099616428333108388267917 18787356160624915645600469)
                  ·
                    refine ⟨440328660014646460443761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18787356160624915645600469 440328660014646460443761)
                    ·
                      rfl

theorem cell23_2572611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_2572611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572611 prefixEnd_2572611 := by exact prefixLift 2572611
  have htrace : WordTrace (prefixWord ++ tailWord_2572611) baseStart_2572611 baseEnd_2572611 := by
    simpa [prefixWord, tailWord_2572611, baseEnd_2572611] using wordTrace_append hprefix tailTrace_2572611
  have hstable : (prefixWord ++ tailWord_2572611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572611).length < 2 ^ (prefixWord ++ tailWord_2572611).sum := by decide
  have hdescent : baseEnd_2572611 < baseStart_2572611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572682 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2572682 : Nat := 118140960795 + 2572682 * 2 ^ 59
def prefixEnd_2572682 : Nat := 4983230072969 + 3 ^ 40 * 2572682 * 2
def baseEnd_2572682 : Nat := 1321022437170408603543457

theorem tailTrace_2572682 : CollatzResearch.WordTrace tailWord_2572682 prefixEnd_2572682 1321022437170408603543457 := by
  unfold tailWord_2572682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23458355316404991987488075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62555614177079978633301533 23458355316404991987488075)
  ·
    refine ⟨35187532974607487981232113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23458355316404991987488075 35187532974607487981232113)
    ·
      refine ⟨26390649730955615985924085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35187532974607487981232113 26390649730955615985924085)
      ·
        refine ⟨2474123412277088998680383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26390649730955615985924085 2474123412277088998680383)
        ·
          refine ⟨3711185118415633498020575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474123412277088998680383 3711185118415633498020575)
          ·
            refine ⟨5566777677623450247030863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711185118415633498020575 5566777677623450247030863)
            ·
              refine ⟨8350166516435175370546295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566777677623450247030863 8350166516435175370546295)
              ·
                refine ⟨12525249774652763055819443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350166516435175370546295 12525249774652763055819443)
                ·
                  refine ⟨18787874661979144583729165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12525249774652763055819443 18787874661979144583729165)
                  ·
                    refine ⟨7045452998242179218898437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18787874661979144583729165 7045452998242179218898437)
                    ·
                      refine ⟨1321022437170408603543457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045452998242179218898437 1321022437170408603543457)
                      ·
                        rfl

theorem cell23_2572682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2572682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572682 prefixEnd_2572682 := by exact prefixLift 2572682
  have htrace : WordTrace (prefixWord ++ tailWord_2572682) baseStart_2572682 baseEnd_2572682 := by
    simpa [prefixWord, tailWord_2572682, baseEnd_2572682] using wordTrace_append hprefix tailTrace_2572682
  have hstable : (prefixWord ++ tailWord_2572682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572682).length < 2 ^ (prefixWord ++ tailWord_2572682).sum := by decide
  have hdescent : baseEnd_2572682 < baseStart_2572682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572708 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2572708 : Nat := 118140960795 + 2572708 * 2 ^ 59
def prefixEnd_2572708 : Nat := 4983230072969 + 3 ^ 40 * 2572708 * 2
def baseEnd_2572708 : Nat := 1321035787667425501818337

theorem tailTrace_2572708 : CollatzResearch.WordTrace tailWord_2572708 prefixEnd_2572708 1321035787667425501818337 := by
  unfold tailWord_2572708
  simp only [CollatzResearch.WordTrace]
  refine ⟨46917184781762887195199389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62556246375683849593599185 46917184781762887195199389)
  ·
    refine ⟨17593944293161082698199771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46917184781762887195199389 17593944293161082698199771)
    ·
      refine ⟨26390916439741624047299657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17593944293161082698199771 26390916439741624047299657)
      ·
        refine ⟨19793187329806218035474743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26390916439741624047299657 19793187329806218035474743)
        ·
          refine ⟨29689780994709327053212115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19793187329806218035474743 29689780994709327053212115)
          ·
            refine ⟨44534671492063990579818173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29689780994709327053212115 44534671492063990579818173)
            ·
              refine ⟨16700501809523996467431815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44534671492063990579818173 16700501809523996467431815)
              ·
                refine ⟨25050752714285994701147723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16700501809523996467431815 25050752714285994701147723)
                ·
                  refine ⟨37576129071428992051721585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25050752714285994701147723 37576129071428992051721585)
                  ·
                    refine ⟨28182096803571744038791189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37576129071428992051721585 28182096803571744038791189)
                    ·
                      refine ⟨1321035787667425501818337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28182096803571744038791189 1321035787667425501818337)
                      ·
                        rfl

theorem cell23_2572708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2572708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572708 prefixEnd_2572708 := by exact prefixLift 2572708
  have htrace : WordTrace (prefixWord ++ tailWord_2572708) baseStart_2572708 baseEnd_2572708 := by
    simpa [prefixWord, tailWord_2572708, baseEnd_2572708] using wordTrace_append hprefix tailTrace_2572708
  have hstable : (prefixWord ++ tailWord_2572708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572708).length < 2 ^ (prefixWord ++ tailWord_2572708).sum := by decide
  have hdescent : baseEnd_2572708 < baseStart_2572708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572768 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2572768 : Nat := 118140960795 + 2572768 * 2 ^ 59
def prefixEnd_2572768 : Nat := 4983230072969 + 3 ^ 40 * 2572768 * 2
def baseEnd_2572768 : Nat := 1321066596506695267068061

theorem tailTrace_2572768 : CollatzResearch.WordTrace tailWord_2572768 prefixEnd_2572768 1321066596506695267068061 := by
  unfold tailWord_2572768
  simp only [CollatzResearch.WordTrace]
  refine ⟨46918278971654202318791479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62557705295538936425055305 46918278971654202318791479)
  ·
    refine ⟨70377418457481303478187219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46918278971654202318791479 70377418457481303478187219)
    ·
      refine ⟨105566127686221955217280829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70377418457481303478187219 105566127686221955217280829)
      ·
        refine ⟨39587297882333233206480311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105566127686221955217280829 39587297882333233206480311)
        ·
          refine ⟨59380946823499849809720467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39587297882333233206480311 59380946823499849809720467)
          ·
            refine ⟨89071420235249774714580701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59380946823499849809720467 89071420235249774714580701)
            ·
              refine ⟨33401782588218665517967763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89071420235249774714580701 33401782588218665517967763)
              ·
                refine ⟨50102673882327998276951645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33401782588218665517967763 50102673882327998276951645)
                ·
                  refine ⟨18788502705872999353856867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50102673882327998276951645 18788502705872999353856867)
                  ·
                    refine ⟨28182754058809499030785301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18788502705872999353856867 28182754058809499030785301)
                    ·
                      refine ⟨1321066596506695267068061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28182754058809499030785301 1321066596506695267068061)
                      ·
                        rfl

theorem cell23_2572768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2572768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572768 prefixEnd_2572768 := by exact prefixLift 2572768
  have htrace : WordTrace (prefixWord ++ tailWord_2572768) baseStart_2572768 baseEnd_2572768 := by
    simpa [prefixWord, tailWord_2572768, baseEnd_2572768] using wordTrace_append hprefix tailTrace_2572768
  have hstable : (prefixWord ++ tailWord_2572768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572768).length < 2 ^ (prefixWord ++ tailWord_2572768).sum := by decide
  have hdescent : baseEnd_2572768 < baseStart_2572768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572775 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2572775 : Nat := 118140960795 + 2572775 * 2 ^ 59
def prefixEnd_2572775 : Nat := 4983230072969 + 3 ^ 40 * 2572775 * 2
def baseEnd_2572775 : Nat := 1321070190871276739680529

theorem tailTrace_2572775 : CollatzResearch.WordTrace tailWord_2572775 prefixEnd_2572775 1321070190871276739680529 := by
  unfold tailWord_2572775
  simp only [CollatzResearch.WordTrace]
  refine ⟨93836813254283044833087779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62557875502855363222058519 93836813254283044833087779)
  ·
    refine ⟨140755219881424567249631669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93836813254283044833087779 140755219881424567249631669)
    ·
      refine ⟨13195801863883553179652969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140755219881424567249631669 13195801863883553179652969)
      ·
        refine ⟨9896851397912664884739727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13195801863883553179652969 9896851397912664884739727)
        ·
          refine ⟨14845277096868997327109591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896851397912664884739727 14845277096868997327109591)
          ·
            refine ⟨22267915645303495990664387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14845277096868997327109591 22267915645303495990664387)
            ·
              refine ⟨33401873467955243985996581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22267915645303495990664387 33401873467955243985996581)
              ·
                refine ⟨6262851275241608247374359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33401873467955243985996581 6262851275241608247374359)
                ·
                  refine ⟨9394276912862412371061539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262851275241608247374359 9394276912862412371061539)
                  ·
                    refine ⟨14091415369293618556592309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9394276912862412371061539 14091415369293618556592309)
                    ·
                      refine ⟨1321070190871276739680529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14091415369293618556592309 1321070190871276739680529)
                      ·
                        rfl

theorem cell23_2572775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2572775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572775 prefixEnd_2572775 := by exact prefixLift 2572775
  have htrace : WordTrace (prefixWord ++ tailWord_2572775) baseStart_2572775 baseEnd_2572775 := by
    simpa [prefixWord, tailWord_2572775, baseEnd_2572775] using wordTrace_append hprefix tailTrace_2572775
  have hstable : (prefixWord ++ tailWord_2572775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572775).length < 2 ^ (prefixWord ++ tailWord_2572775).sum := by decide
  have hdescent : baseEnd_2572775 < baseStart_2572775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572785 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_2572785 : Nat := 118140960795 + 2572785 * 2 ^ 59
def prefixEnd_2572785 : Nat := 4983230072969 + 3 ^ 40 * 2572785 * 2
def baseEnd_2572785 : Nat := 1321075325677821700555483

theorem tailTrace_2572785 : CollatzResearch.WordTrace tailWord_2572785 prefixEnd_2572785 1321075325677821700555483 := by
  unfold tailWord_2572785
  simp only [CollatzResearch.WordTrace]
  refine ⟨93837177984246816540951809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62558118656164544360634539 93837177984246816540951809)
  ·
    refine ⟨70377883488185112405713857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93837177984246816540951809 70377883488185112405713857)
    ·
      refine ⟨52783412616138834304285393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70377883488185112405713857 52783412616138834304285393)
      ·
        refine ⟨39587559462104125728214045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52783412616138834304285393 39587559462104125728214045)
        ·
          refine ⟨14845334798289047148080267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39587559462104125728214045 14845334798289047148080267)
          ·
            refine ⟨22268002197433570722120401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14845334798289047148080267 22268002197433570722120401)
            ·
              refine ⟨16701001648075178041590301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22268002197433570722120401 16701001648075178041590301)
              ·
                refine ⟨6262875618028191765596363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16701001648075178041590301 6262875618028191765596363)
                ·
                  refine ⟨9394313427042287648394545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262875618028191765596363 9394313427042287648394545)
                  ·
                    refine ⟨7045735070281715736295909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9394313427042287648394545 7045735070281715736295909)
                    ·
                      refine ⟨1321075325677821700555483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045735070281715736295909 1321075325677821700555483)
                      ·
                        rfl

theorem cell23_2572785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_2572785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572785 prefixEnd_2572785 := by exact prefixLift 2572785
  have htrace : WordTrace (prefixWord ++ tailWord_2572785) baseStart_2572785 baseEnd_2572785 := by
    simpa [prefixWord, tailWord_2572785, baseEnd_2572785] using wordTrace_append hprefix tailTrace_2572785
  have hstable : (prefixWord ++ tailWord_2572785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572785).length < 2 ^ (prefixWord ++ tailWord_2572785).sum := by decide
  have hdescent : baseEnd_2572785 < baseStart_2572785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572786 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_2572786 : Nat := 118140960795 + 2572786 * 2 ^ 59
def prefixEnd_2572786 : Nat := 4983230072969 + 3 ^ 40 * 2572786 * 2
def baseEnd_2572786 : Nat := 440358613052825398880993

theorem tailTrace_2572786 : CollatzResearch.WordTrace tailWord_2572786 prefixEnd_2572786 440358613052825398880993 := by
  unfold tailWord_2572786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23459303614310798427934553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62558142971495462474492141 23459303614310798427934553)
  ·
    refine ⟨17594477710733098820950915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23459303614310798427934553 17594477710733098820950915)
    ·
      refine ⟨26391716566099648231426373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17594477710733098820950915 26391716566099648231426373)
      ·
        refine ⟨4948446856143684043392445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26391716566099648231426373 4948446856143684043392445)
        ·
          refine ⟨1855667571053881516272167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4948446856143684043392445 1855667571053881516272167)
          ·
            refine ⟨2783501356580822274408251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855667571053881516272167 2783501356580822274408251)
            ·
              refine ⟨4175252034871233411612377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783501356580822274408251 4175252034871233411612377)
              ·
                refine ⟨3131439026153425058709283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4175252034871233411612377 3131439026153425058709283)
                ·
                  refine ⟨4697158539230137588063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131439026153425058709283 4697158539230137588063925)
                  ·
                    refine ⟨440358613052825398880993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4697158539230137588063925 440358613052825398880993)
                    ·
                      rfl

theorem cell23_2572786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_2572786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572786 prefixEnd_2572786 := by exact prefixLift 2572786
  have htrace : WordTrace (prefixWord ++ tailWord_2572786) baseStart_2572786 baseEnd_2572786 := by
    simpa [prefixWord, tailWord_2572786, baseEnd_2572786] using wordTrace_append hprefix tailTrace_2572786
  have hstable : (prefixWord ++ tailWord_2572786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572786).length < 2 ^ (prefixWord ++ tailWord_2572786).sum := by decide
  have hdescent : baseEnd_2572786 < baseStart_2572786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572789 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2572789 : Nat := 118140960795 + 2572789 * 2 ^ 59
def prefixEnd_2572789 : Nat := 4983230072969 + 3 ^ 40 * 2572789 * 2
def baseEnd_2572789 : Nat := 1321077379600439684905465

theorem tailTrace_2572789 : CollatzResearch.WordTrace tailWord_2572789 prefixEnd_2572789 1321077379600439684905465 := by
  unfold tailWord_2572789
  simp only [CollatzResearch.WordTrace]
  refine ⟨93837323876232325224097421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62558215917488216816064947 93837323876232325224097421)
  ·
    refine ⟨35188996453587121959036533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93837323876232325224097421 35188996453587121959036533)
    ·
      refine ⟨3298968417523792683659675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35188996453587121959036533 3298968417523792683659675)
      ·
        refine ⟨4948452626285689025489513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298968417523792683659675 4948452626285689025489513)
        ·
          refine ⟨3711339469714266769117135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948452626285689025489513 3711339469714266769117135)
          ·
            refine ⟨5567009204571400153675703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711339469714266769117135 5567009204571400153675703)
            ·
              refine ⟨8350513806857100230513555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567009204571400153675703 8350513806857100230513555)
              ·
                refine ⟨12525770710285650345770333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350513806857100230513555 12525770710285650345770333)
                ·
                  refine ⟨4697164016357118879663875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12525770710285650345770333 4697164016357118879663875)
                  ·
                    refine ⟨7045746024535678319495813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697164016357118879663875 7045746024535678319495813)
                    ·
                      refine ⟨1321077379600439684905465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045746024535678319495813 1321077379600439684905465)
                      ·
                        rfl

theorem cell23_2572789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2572789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572789 prefixEnd_2572789 := by exact prefixLift 2572789
  have htrace : WordTrace (prefixWord ++ tailWord_2572789) baseStart_2572789 baseEnd_2572789 := by
    simpa [prefixWord, tailWord_2572789, baseEnd_2572789] using wordTrace_append hprefix tailTrace_2572789
  have hstable : (prefixWord ++ tailWord_2572789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572789).length < 2 ^ (prefixWord ++ tailWord_2572789).sum := by decide
  have hdescent : baseEnd_2572789 < baseStart_2572789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572805 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_2572805 : Nat := 118140960795 + 2572805 * 2 ^ 59
def prefixEnd_2572805 : Nat := 4983230072969 + 3 ^ 40 * 2572805 * 2
def baseEnd_2572805 : Nat := 1321085595290911622305391

theorem tailTrace_2572805 : CollatzResearch.WordTrace tailWord_2572805 prefixEnd_2572805 1321085595290911622305391 := by
  unfold tailWord_2572805
  simp only [CollatzResearch.WordTrace]
  refine ⟨93837907444174359956679869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62558604962782906637786579 93837907444174359956679869)
  ·
    refine ⟨35189215291565384983754951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93837907444174359956679869 35189215291565384983754951)
    ·
      refine ⟨52783822937348077475632427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35189215291565384983754951 52783822937348077475632427)
      ·
        refine ⟨79175734406022116213448641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52783822937348077475632427 79175734406022116213448641)
        ·
          refine ⟨59381800804516587160086481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79175734406022116213448641 59381800804516587160086481)
          ·
            refine ⟨44536350603387440370064861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59381800804516587160086481 44536350603387440370064861)
            ·
              refine ⟨16701131476270290138774323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44536350603387440370064861 16701131476270290138774323)
              ·
                refine ⟨25051697214405435208161485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16701131476270290138774323 25051697214405435208161485)
                ·
                  refine ⟨9394386455402038203060557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25051697214405435208161485 9394386455402038203060557)
                  ·
                    refine ⟨3522894920775764326147709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9394386455402038203060557 3522894920775764326147709)
                    ·
                      refine ⟨1321085595290911622305391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3522894920775764326147709 1321085595290911622305391)
                      ·
                        rfl

theorem cell23_2572805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_2572805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572805 prefixEnd_2572805 := by exact prefixLift 2572805
  have htrace : WordTrace (prefixWord ++ tailWord_2572805) baseStart_2572805 baseEnd_2572805 := by
    simpa [prefixWord, tailWord_2572805, baseEnd_2572805] using wordTrace_append hprefix tailTrace_2572805
  have hstable : (prefixWord ++ tailWord_2572805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572805).length < 2 ^ (prefixWord ++ tailWord_2572805).sum := by decide
  have hdescent : baseEnd_2572805 < baseStart_2572805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572875 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_2572875 : Nat := 118140960795 + 2572875 * 2 ^ 59
def prefixEnd_2572875 : Nat := 4983230072969 + 3 ^ 40 * 2572875 * 2
def baseEnd_2572875 : Nat := 1321121538936726348430069

theorem tailTrace_2572875 : CollatzResearch.WordTrace tailWord_2572875 prefixEnd_2572875 1321121538936726348430069 := by
  unfold tailWord_2572875
  simp only [CollatzResearch.WordTrace]
  refine ⟨93840460553920761911728079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62560307035947174607818719 93840460553920761911728079)
  ·
    refine ⟨140760690830881142867592119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93840460553920761911728079 140760690830881142867592119)
    ·
      refine ⟨211141036246321714301388179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140760690830881142867592119 211141036246321714301388179)
      ·
        refine ⟨316711554369482571452082269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211141036246321714301388179 316711554369482571452082269)
        ·
          refine ⟨118766832888555964294530851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316711554369482571452082269 118766832888555964294530851)
          ·
            refine ⟨178150249332833946441796277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118766832888555964294530851 178150249332833946441796277)
            ·
              refine ⟨16701585874953182478918401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178150249332833946441796277 16701585874953182478918401)
              ·
                refine ⟨12526189406214886859188801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16701585874953182478918401 12526189406214886859188801)
                ·
                  refine ⟨9394642054661165144391601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12526189406214886859188801 9394642054661165144391601)
                  ·
                    refine ⟨7045981540995873858293701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9394642054661165144391601 7045981540995873858293701)
                    ·
                      refine ⟨1321121538936726348430069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7045981540995873858293701 1321121538936726348430069)
                      ·
                        rfl

theorem cell23_2572875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_2572875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572875 prefixEnd_2572875 := by exact prefixLift 2572875
  have htrace : WordTrace (prefixWord ++ tailWord_2572875) baseStart_2572875 baseEnd_2572875 := by
    simpa [prefixWord, tailWord_2572875, baseEnd_2572875] using wordTrace_append hprefix tailTrace_2572875
  have hstable : (prefixWord ++ tailWord_2572875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572875).length < 2 ^ (prefixWord ++ tailWord_2572875).sum := by decide
  have hdescent : baseEnd_2572875 < baseStart_2572875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572885 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 7]
def baseStart_2572885 : Nat := 118140960795 + 2572885 * 2 ^ 59
def prefixEnd_2572885 : Nat := 4983230072969 + 3 ^ 40 * 2572885 * 2
def baseEnd_2572885 : Nat := 146791852638141256589447

theorem tailTrace_2572885 : CollatzResearch.WordTrace tailWord_2572885 prefixEnd_2572885 146791852638141256589447 := by
  unfold tailWord_2572885
  simp only [CollatzResearch.WordTrace]
  refine ⟨93840825283884533619592109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62560550189256355746394739 93840825283884533619592109)
  ·
    refine ⟨35190309481456700107347041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93840825283884533619592109 35190309481456700107347041)
    ·
      refine ⟨26392732111092525080510281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35190309481456700107347041 26392732111092525080510281)
      ·
        refine ⟨19794549083319393810382711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26392732111092525080510281 19794549083319393810382711)
        ·
          refine ⟨29691823624979090715574067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19794549083319393810382711 29691823624979090715574067)
          ·
            refine ⟨44537735437468636073361101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29691823624979090715574067 44537735437468636073361101)
            ·
              refine ⟨16701650789050738527510413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44537735437468636073361101 16701650789050738527510413)
              ·
                refine ⟨6263119045894026947816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16701650789050738527510413 6263119045894026947816405)
                ·
                  refine ⟨146791852638141256589447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6263119045894026947816405 146791852638141256589447)
                  ·
                    rfl

theorem cell23_2572885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_2572885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572885 prefixEnd_2572885 := by exact prefixLift 2572885
  have htrace : WordTrace (prefixWord ++ tailWord_2572885) baseStart_2572885 baseEnd_2572885 := by
    simpa [prefixWord, tailWord_2572885, baseEnd_2572885] using wordTrace_append hprefix tailTrace_2572885
  have hstable : (prefixWord ++ tailWord_2572885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572885).length < 2 ^ (prefixWord ++ tailWord_2572885).sum := by decide
  have hdescent : baseEnd_2572885 < baseStart_2572885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572932 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2572932 : Nat := 118140960795 + 2572932 * 2 ^ 59
def prefixEnd_2572932 : Nat := 4983230072969 + 3 ^ 40 * 2572932 * 2
def baseEnd_2572932 : Nat := 440383602444677541805769

theorem tailTrace_2572932 : CollatzResearch.WordTrace tailWord_2572932 prefixEnd_2572932 440383602444677541805769 := by
  unfold tailWord_2572932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46921269757357130323276525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62561693009809507097702033 46921269757357130323276525)
  ·
    refine ⟨17595476159008923871228697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46921269757357130323276525 17595476159008923871228697)
    ·
      refine ⟨13196607119256692903421523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17595476159008923871228697 13196607119256692903421523)
      ·
        refine ⟨19794910678885039355132285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13196607119256692903421523 19794910678885039355132285)
        ·
          refine ⟨7423091504581889758174607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19794910678885039355132285 7423091504581889758174607)
          ·
            refine ⟨11134637256872834637261911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423091504581889758174607 11134637256872834637261911)
            ·
              refine ⟨16701955885309251955892867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11134637256872834637261911 16701955885309251955892867)
              ·
                refine ⟨25052933827963877933839301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16701955885309251955892867 25052933827963877933839301)
                ·
                  refine ⟨4697425092743227112594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25052933827963877933839301 4697425092743227112594869)
                  ·
                    refine ⟨440383602444677541805769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4697425092743227112594869 440383602444677541805769)
                    ·
                      rfl

theorem cell23_2572932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2572932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572932 prefixEnd_2572932 := by exact prefixLift 2572932
  have htrace : WordTrace (prefixWord ++ tailWord_2572932) baseStart_2572932 baseEnd_2572932 := by
    simpa [prefixWord, tailWord_2572932, baseEnd_2572932] using wordTrace_append hprefix tailTrace_2572932
  have hstable : (prefixWord ++ tailWord_2572932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572932).length < 2 ^ (prefixWord ++ tailWord_2572932).sum := by decide
  have hdescent : baseEnd_2572932 < baseStart_2572932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572942 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2572942 : Nat := 118140960795 + 2572942 * 2 ^ 59
def prefixEnd_2572942 : Nat := 4983230072969 + 3 ^ 40 * 2572942 * 2
def baseEnd_2572942 : Nat := 1321155942140577586292261

theorem tailTrace_2572942 : CollatzResearch.WordTrace tailWord_2572942 prefixEnd_2572942 1321155942140577586292261 := by
  unfold tailWord_2572942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730363030584754044302135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62561936163118688236278053 11730363030584754044302135)
  ·
    refine ⟨17595544545877131066453203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11730363030584754044302135 17595544545877131066453203)
    ·
      refine ⟨26393316818815696599679805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595544545877131066453203 26393316818815696599679805)
      ·
        refine ⟨9897493807055886224879927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26393316818815696599679805 9897493807055886224879927)
        ·
          refine ⟨14846240710583829337319891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897493807055886224879927 14846240710583829337319891)
          ·
            refine ⟨22269361065875744005979837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14846240710583829337319891 22269361065875744005979837)
            ·
              refine ⟨8351010399703404002242439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22269361065875744005979837 8351010399703404002242439)
              ·
                refine ⟨12526515599555106003363659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351010399703404002242439 12526515599555106003363659)
                ·
                  refine ⟨18789773399332659005045489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12526515599555106003363659 18789773399332659005045489)
                  ·
                    refine ⟨14092330049499494253784117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18789773399332659005045489 14092330049499494253784117)
                    ·
                      refine ⟨1321155942140577586292261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14092330049499494253784117 1321155942140577586292261)
                      ·
                        rfl

theorem cell23_2572942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2572942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572942 prefixEnd_2572942 := by exact prefixLift 2572942
  have htrace : WordTrace (prefixWord ++ tailWord_2572942) baseStart_2572942 baseEnd_2572942 := by
    simpa [prefixWord, tailWord_2572942, baseEnd_2572942] using wordTrace_append hprefix tailTrace_2572942
  have hstable : (prefixWord ++ tailWord_2572942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572942).length < 2 ^ (prefixWord ++ tailWord_2572942).sum := by decide
  have hdescent : baseEnd_2572942 < baseStart_2572942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572952 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2572952 : Nat := 118140960795 + 2572952 * 2 ^ 59
def prefixEnd_2572952 : Nat := 4983230072969 + 3 ^ 40 * 2572952 * 2
def baseEnd_2572952 : Nat := 1321161076947122547167215

theorem tailTrace_2572952 : CollatzResearch.WordTrace tailWord_2572952 prefixEnd_2572952 1321161076947122547167215 := by
  unfold tailWord_2572952
  simp only [CollatzResearch.WordTrace]
  refine ⟨46921634487320902031140555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62562179316427869374854073 46921634487320902031140555)
  ·
    refine ⟨70382451730981353046710833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46921634487320902031140555 70382451730981353046710833)
    ·
      refine ⟨52786838798236014785033125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70382451730981353046710833 52786838798236014785033125)
      ·
        refine ⟨9897532274669252772193711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52786838798236014785033125 9897532274669252772193711)
        ·
          refine ⟨14846298412003879158290567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897532274669252772193711 14846298412003879158290567)
          ·
            refine ⟨22269447618005818737435851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14846298412003879158290567 22269447618005818737435851)
            ·
              refine ⟨33404171427008728106153777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22269447618005818737435851 33404171427008728106153777)
              ·
                refine ⟨25053128570256546079615333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33404171427008728106153777 25053128570256546079615333)
                ·
                  refine ⟨4697461606923102389927875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25053128570256546079615333 4697461606923102389927875)
                  ·
                    refine ⟨7046192410384653584891813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697461606923102389927875 7046192410384653584891813)
                    ·
                      refine ⟨1321161076947122547167215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7046192410384653584891813 1321161076947122547167215)
                      ·
                        rfl

theorem cell23_2572952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2572952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572952 prefixEnd_2572952 := by exact prefixLift 2572952
  have htrace : WordTrace (prefixWord ++ tailWord_2572952) baseStart_2572952 baseEnd_2572952 := by
    simpa [prefixWord, tailWord_2572952, baseEnd_2572952] using wordTrace_append hprefix tailTrace_2572952
  have hstable : (prefixWord ++ tailWord_2572952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572952).length < 2 ^ (prefixWord ++ tailWord_2572952).sum := by decide
  have hdescent : baseEnd_2572952 < baseStart_2572952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572965 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2572965 : Nat := 118140960795 + 2572965 * 2 ^ 59
def prefixEnd_2572965 : Nat := 4983230072969 + 3 ^ 40 * 2572965 * 2
def baseEnd_2572965 : Nat := 1321167752195630996304655

theorem tailTrace_2572965 : CollatzResearch.WordTrace tailWord_2572965 prefixEnd_2572965 1321167752195630996304655 := by
  unfold tailWord_2572965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93843743123594707282504349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62562495415729804855002899 93843743123594707282504349)
  ·
    refine ⟨35191403671348015230939131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93843743123594707282504349 35191403671348015230939131)
    ·
      refine ⟨52787105507022022846408697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35191403671348015230939131 52787105507022022846408697)
      ·
        refine ⟨39590329130266517134806523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52787105507022022846408697 39590329130266517134806523)
        ·
          refine ⟨59385493695399775702209785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39590329130266517134806523 59385493695399775702209785)
          ·
            refine ⟨44539120271549831776657339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59385493695399775702209785 44539120271549831776657339)
            ·
              refine ⟨66808680407324747664986009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44539120271549831776657339 66808680407324747664986009)
              ·
                refine ⟨50106510305493560748739507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66808680407324747664986009 50106510305493560748739507)
                ·
                  refine ⟨75159765458240341123109261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50106510305493560748739507 75159765458240341123109261)
                  ·
                    refine ⟨28184912046840127921165973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75159765458240341123109261 28184912046840127921165973)
                    ·
                      refine ⟨1321167752195630996304655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28184912046840127921165973 1321167752195630996304655)
                      ·
                        rfl

theorem cell23_2572965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2572965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572965 prefixEnd_2572965 := by exact prefixLift 2572965
  have htrace : WordTrace (prefixWord ++ tailWord_2572965) baseStart_2572965 baseEnd_2572965 := by
    simpa [prefixWord, tailWord_2572965, baseEnd_2572965] using wordTrace_append hprefix tailTrace_2572965
  have hstable : (prefixWord ++ tailWord_2572965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572965).length < 2 ^ (prefixWord ++ tailWord_2572965).sum := by decide
  have hdescent : baseEnd_2572965 < baseStart_2572965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572989 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2572989 : Nat := 118140960795 + 2572989 * 2 ^ 59
def prefixEnd_2572989 : Nat := 4983230072969 + 3 ^ 40 * 2572989 * 2
def baseEnd_2572989 : Nat := 1321180075731338902404545

theorem tailTrace_2572989 : CollatzResearch.WordTrace tailWord_2572989 prefixEnd_2572989 1321180075731338902404545 := by
  unfold tailWord_2572989
  simp only [CollatzResearch.WordTrace]
  refine ⟨93844618475507759381378021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62563078983671839587585347 93844618475507759381378021)
  ·
    refine ⟨17595865964157704884008379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93844618475507759381378021 17595865964157704884008379)
    ·
      refine ⟨26393798946236557326012569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595865964157704884008379 26393798946236557326012569)
      ·
        refine ⟨19795349209677417994509427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26393798946236557326012569 19795349209677417994509427)
        ·
          refine ⟨29693023814516126991764141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19795349209677417994509427 29693023814516126991764141)
          ·
            refine ⟨11134883930443547621911553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29693023814516126991764141 11134883930443547621911553)
            ·
              refine ⟨8351162947832660716433665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11134883930443547621911553 8351162947832660716433665)
              ·
                refine ⟨6263372210874495537325249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8351162947832660716433665 6263372210874495537325249)
                ·
                  refine ⟨4697529158155871652993937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263372210874495537325249 4697529158155871652993937)
                  ·
                    refine ⟨3523146868616903739745453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4697529158155871652993937 3523146868616903739745453)
                    ·
                      refine ⟨1321180075731338902404545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523146868616903739745453 1321180075731338902404545)
                      ·
                        rfl

theorem cell23_2572989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2572989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572989 prefixEnd_2572989 := by exact prefixLift 2572989
  have htrace : WordTrace (prefixWord ++ tailWord_2572989) baseStart_2572989 baseEnd_2572989 := by
    simpa [prefixWord, tailWord_2572989, baseEnd_2572989] using wordTrace_append hprefix tailTrace_2572989
  have hstable : (prefixWord ++ tailWord_2572989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572989).length < 2 ^ (prefixWord ++ tailWord_2572989).sum := by decide
  have hdescent : baseEnd_2572989 < baseStart_2572989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572992 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 6]
def baseStart_2572992 : Nat := 118140960795 + 2572992 * 2 ^ 59
def prefixEnd_2572992 : Nat := 4983230072969 + 3 ^ 40 * 2572992 * 2
def baseEnd_2572992 : Nat := 146797957352589154518559

theorem tailTrace_2572992 : CollatzResearch.WordTrace tailWord_2572992 prefixEnd_2572992 146797957352589154518559 := by
  unfold tailWord_2572992
  simp only [CollatzResearch.WordTrace]
  refine ⟨46922363947248445446868615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62563151929664593929158153 46922363947248445446868615)
  ·
    refine ⟨70383545920872668170302923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46922363947248445446868615 70383545920872668170302923)
    ·
      refine ⟨105575318881309002255454385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70383545920872668170302923 105575318881309002255454385)
      ·
        refine ⟨79181489160981751691590789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105575318881309002255454385 79181489160981751691590789)
        ·
          refine ⟨14846529217684078442173273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79181489160981751691590789 14846529217684078442173273)
          ·
            refine ⟨11134896913263058831629955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846529217684078442173273 11134896913263058831629955)
            ·
              refine ⟨16702345369894588247444933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11134896913263058831629955 16702345369894588247444933)
              ·
                refine ⟨3131689756855235296395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16702345369894588247444933 3131689756855235296395925)
                ·
                  refine ⟨146797957352589154518559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3131689756855235296395925 146797957352589154518559)
                  ·
                    rfl

theorem cell23_2572992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_2572992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572992 prefixEnd_2572992 := by exact prefixLift 2572992
  have htrace : WordTrace (prefixWord ++ tailWord_2572992) baseStart_2572992 baseEnd_2572992 := by
    simpa [prefixWord, tailWord_2572992, baseEnd_2572992] using wordTrace_append hprefix tailTrace_2572992
  have hstable : (prefixWord ++ tailWord_2572992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572992).length < 2 ^ (prefixWord ++ tailWord_2572992).sum := by decide
  have hdescent : baseEnd_2572992 < baseStart_2572992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573039 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 1, 5]
def baseStart_2573039 : Nat := 118140960795 + 2573039 * 2 ^ 59
def prefixEnd_2573039 : Nat := 4983230072969 + 3 ^ 40 * 2573039 * 2
def baseEnd_2573039 : Nat := 440401916588021235593105

theorem tailTrace_2573039 : CollatzResearch.WordTrace tailWord_2573039 prefixEnd_2573039 440401916588021235593105 := by
  unfold tailWord_2573039
  simp only [CollatzResearch.WordTrace]
  refine ⟨93846442125326617920698171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62564294750217745280465447 93846442125326617920698171)
  ·
    refine ⟨140769663187989926881047257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93846442125326617920698171 140769663187989926881047257)
    ·
      refine ⟨105577247390992445160785443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140769663187989926881047257 105577247390992445160785443)
      ·
        refine ⟨158365871086488667741178165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105577247390992445160785443 158365871086488667741178165)
        ·
          refine ⟨14846800414358312600735453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158365871086488667741178165 14846800414358312600735453)
          ·
            refine ⟨5567550155384367225275795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14846800414358312600735453 5567550155384367225275795)
            ·
              refine ⟨8351325233076550837913693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567550155384367225275795 8351325233076550837913693)
              ·
                refine ⟨3131746962403706564217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8351325233076550837913693 3131746962403706564217635)
                ·
                  refine ⟨4697620443605559846326453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131746962403706564217635 4697620443605559846326453)
                  ·
                    refine ⟨440401916588021235593105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4697620443605559846326453 440401916588021235593105)
                    ·
                      rfl

theorem cell23_2573039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_2573039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573039 prefixEnd_2573039 := by exact prefixLift 2573039
  have htrace : WordTrace (prefixWord ++ tailWord_2573039) baseStart_2573039 baseEnd_2573039 := by
    simpa [prefixWord, tailWord_2573039, baseEnd_2573039] using wordTrace_append hprefix tailTrace_2573039
  have hstable : (prefixWord ++ tailWord_2573039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573039).length < 2 ^ (prefixWord ++ tailWord_2573039).sum := by decide
  have hdescent : baseEnd_2573039 < baseStart_2573039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573046 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2573046 : Nat := 118140960795 + 2573046 * 2 ^ 59
def prefixEnd_2573046 : Nat := 4983230072969 + 3 ^ 40 * 2573046 * 2
def baseEnd_2573046 : Nat := 1321209344128645179391783

theorem tailTrace_2573046 : CollatzResearch.WordTrace tailWord_2573046 prefixEnd_2573046 1321209344128645179391783 := by
  unfold tailWord_2573046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865418589768828632262687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62564464957534172077468661 5865418589768828632262687)
  ·
    refine ⟨8798127884653242948394031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5865418589768828632262687 8798127884653242948394031)
    ·
      refine ⟨13197191826979864422591047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8798127884653242948394031 13197191826979864422591047)
      ·
        refine ⟨19795787740469796633886571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13197191826979864422591047 19795787740469796633886571)
        ·
          refine ⟨29693681610704694950829857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19795787740469796633886571 29693681610704694950829857)
          ·
            refine ⟨22270261208028521213122393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29693681610704694950829857 22270261208028521213122393)
            ·
              refine ⟨16702695906021390909841795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22270261208028521213122393 16702695906021390909841795)
              ·
                refine ⟨25054043859032086364762693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16702695906021390909841795 25054043859032086364762693)
                ·
                  refine ⟨4697633223568516193393005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25054043859032086364762693 4697633223568516193393005)
                  ·
                    refine ⟨1761612458838193572522377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4697633223568516193393005 1761612458838193572522377)
                    ·
                      refine ⟨1321209344128645179391783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761612458838193572522377 1321209344128645179391783)
                      ·
                        rfl

theorem cell23_2573046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2573046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573046 prefixEnd_2573046 := by exact prefixLift 2573046
  have htrace : WordTrace (prefixWord ++ tailWord_2573046) baseStart_2573046 baseEnd_2573046 := by
    simpa [prefixWord, tailWord_2573046, baseEnd_2573046] using wordTrace_append hprefix tailTrace_2573046
  have hstable : (prefixWord ++ tailWord_2573046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573046).length < 2 ^ (prefixWord ++ tailWord_2573046).sum := by decide
  have hdescent : baseEnd_2573046 < baseStart_2573046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573082 : List Nat := [3, 1, 1, 3, 2, 1, 3, 9]
def baseStart_2573082 : Nat := 118140960795 + 2573082 * 2 ^ 59
def prefixEnd_2573082 : Nat := 4983230072969 + 3 ^ 40 * 2573082 * 2
def baseEnd_2573082 : Nat := 48934364053044705131171

theorem tailTrace_2573082 : CollatzResearch.WordTrace tailWord_2573082 prefixEnd_2573082 48934364053044705131171 := by
  unfold tailWord_2573082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462002616042709066128375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62565340309447224176342333 23462002616042709066128375)
  ·
    refine ⟨35193003924064063599192563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23462002616042709066128375 35193003924064063599192563)
    ·
      refine ⟨52789505886096095398788845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193003924064063599192563 52789505886096095398788845)
      ·
        refine ⟨19796064707286035774545817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52789505886096095398788845 19796064707286035774545817)
        ·
          refine ⟨14847048530464526830909363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19796064707286035774545817 14847048530464526830909363)
          ·
            refine ⟨22270572795696790246364045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14847048530464526830909363 22270572795696790246364045)
            ·
              refine ⟨8351464798386296342386517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22270572795696790246364045 8351464798386296342386517)
              ·
                refine ⟨48934364053044705131171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8351464798386296342386517 48934364053044705131171)
                ·
                  rfl

theorem cell23_2573082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_2573082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573082 prefixEnd_2573082 := by exact prefixLift 2573082
  have htrace : WordTrace (prefixWord ++ tailWord_2573082) baseStart_2573082 baseEnd_2573082 := by
    simpa [prefixWord, tailWord_2573082, baseEnd_2573082] using wordTrace_append hprefix tailTrace_2573082
  have hstable : (prefixWord ++ tailWord_2573082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573082).length < 2 ^ (prefixWord ++ tailWord_2573082).sum := by decide
  have hdescent : baseEnd_2573082 < baseStart_2573082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573096 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2573096 : Nat := 118140960795 + 2573096 * 2 ^ 59
def prefixEnd_2573096 : Nat := 4983230072969 + 3 ^ 40 * 2573096 * 2
def baseEnd_2573096 : Nat := 1321235018161369983766553

theorem tailTrace_2573096 : CollatzResearch.WordTrace tailWord_2573096 prefixEnd_2573096 1321235018161369983766553 := by
  unfold tailWord_2573096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46924260543060058327761571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62565680724080077770348761 46924260543060058327761571)
  ·
    refine ⟨70386390814590087491642357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46924260543060058327761571 70386390814590087491642357)
    ·
      refine ⟨6598724138867820702341471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70386390814590087491642357 6598724138867820702341471)
      ·
        refine ⟨9898086208301731053512207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598724138867820702341471 9898086208301731053512207)
        ·
          refine ⟨14847129312452596580268311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9898086208301731053512207 14847129312452596580268311)
          ·
            refine ⟨22270693968678894870402467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14847129312452596580268311 22270693968678894870402467)
            ·
              refine ⟨33406040953018342305603701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22270693968678894870402467 33406040953018342305603701)
              ·
                refine ⟨3131816339345469591150347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33406040953018342305603701 3131816339345469591150347)
                ·
                  refine ⟨4697724509018204386725521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131816339345469591150347 4697724509018204386725521)
                  ·
                    refine ⟨3523293381763653290044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4697724509018204386725521 3523293381763653290044141)
                    ·
                      refine ⟨1321235018161369983766553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523293381763653290044141 1321235018161369983766553)
                      ·
                        rfl

theorem cell23_2573096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2573096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573096 prefixEnd_2573096 := by exact prefixLift 2573096
  have htrace : WordTrace (prefixWord ++ tailWord_2573096) baseStart_2573096 baseEnd_2573096 := by
    simpa [prefixWord, tailWord_2573096, baseEnd_2573096] using wordTrace_append hprefix tailTrace_2573096
  have hstable : (prefixWord ++ tailWord_2573096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573096).length < 2 ^ (prefixWord ++ tailWord_2573096).sum := by decide
  have hdescent : baseEnd_2573096 < baseStart_2573096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573112 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_2573112 : Nat := 118140960795 + 2573112 * 2 ^ 59
def prefixEnd_2573112 : Nat := 4983230072969 + 3 ^ 40 * 2573112 * 2
def baseEnd_2573112 : Nat := 440414411283947307055493

theorem tailTrace_2573112 : CollatzResearch.WordTrace tailWord_2573112 prefixEnd_2573112 440414411283947307055493 := by
  unfold tailWord_2573112
  simp only [CollatzResearch.WordTrace]
  refine ⟨46924552327031075694052795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62566069769374767592070393 46924552327031075694052795)
  ·
    refine ⟨70386828490546613541079193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46924552327031075694052795 70386828490546613541079193)
    ·
      refine ⟨52790121367909960155809395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70386828490546613541079193 52790121367909960155809395)
      ·
        refine ⟨79185182051864940233714093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52790121367909960155809395 79185182051864940233714093)
        ·
          refine ⟨29694443269449352587642785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79185182051864940233714093 29694443269449352587642785)
          ·
            refine ⟨22270832452087014440732089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29694443269449352587642785 22270832452087014440732089)
            ·
              refine ⟨16703124339065260830549067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22270832452087014440732089 16703124339065260830549067)
              ·
                refine ⟨25054686508597891245823601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16703124339065260830549067 25054686508597891245823601)
                ·
                  refine ⟨18791014881448418434367701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25054686508597891245823601 18791014881448418434367701)
                  ·
                    refine ⟨440414411283947307055493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18791014881448418434367701 440414411283947307055493)
                    ·
                      rfl

theorem cell23_2573112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_2573112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573112 prefixEnd_2573112 := by exact prefixLift 2573112
  have htrace : WordTrace (prefixWord ++ tailWord_2573112) baseStart_2573112 baseEnd_2573112 := by
    simpa [prefixWord, tailWord_2573112, baseEnd_2573112] using wordTrace_append hprefix tailTrace_2573112
  have hstable : (prefixWord ++ tailWord_2573112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573112).length < 2 ^ (prefixWord ++ tailWord_2573112).sum := by decide
  have hdescent : baseEnd_2573112 < baseStart_2573112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573169 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_2573169 : Nat := 118140960795 + 2573169 * 2 ^ 59
def prefixEnd_2573169 : Nat := 4983230072969 + 3 ^ 40 * 2573169 * 2
def baseEnd_2573169 : Nat := 1321272502249148198153717

theorem tailTrace_2573169 : CollatzResearch.WordTrace tailWord_2573169 prefixEnd_2573169 1321272502249148198153717 := by
  unfold tailWord_2573169
  simp only [CollatzResearch.WordTrace]
  refine ⟨93851183614855650122930561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62567455743237100081953707 93851183614855650122930561)
  ·
    refine ⟨70388387711141737592197921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93851183614855650122930561 70388387711141737592197921)
    ·
      refine ⟨52791290783356303194148441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70388387711141737592197921 52791290783356303194148441)
      ·
        refine ⟨39593468087517227395611331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52791290783356303194148441 39593468087517227395611331)
        ·
          refine ⟨59390202131275841093416997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39593468087517227395611331 59390202131275841093416997)
          ·
            refine ⟨11135662899614220205015687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59390202131275841093416997 11135662899614220205015687)
            ·
              refine ⟨16703494349421330307523531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11135662899614220205015687 16703494349421330307523531)
              ·
                refine ⟨25055241524131995461285297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16703494349421330307523531 25055241524131995461285297)
                ·
                  refine ⟨18791431143098996595963973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25055241524131995461285297 18791431143098996595963973)
                  ·
                    refine ⟨3523393339331061861743245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18791431143098996595963973 3523393339331061861743245)
                    ·
                      refine ⟨1321272502249148198153717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523393339331061861743245 1321272502249148198153717)
                      ·
                        rfl

theorem cell23_2573169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_2573169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573169 prefixEnd_2573169 := by exact prefixLift 2573169
  have htrace : WordTrace (prefixWord ++ tailWord_2573169) baseStart_2573169 baseEnd_2573169 := by
    simpa [prefixWord, tailWord_2573169, baseEnd_2573169] using wordTrace_append hprefix tailTrace_2573169
  have hstable : (prefixWord ++ tailWord_2573169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573169).length < 2 ^ (prefixWord ++ tailWord_2573169).sum := by decide
  have hdescent : baseEnd_2573169 < baseStart_2573169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573183 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 2, 2, 2]
def baseStart_2573183 : Nat := 118140960795 + 2573183 * 2 ^ 59
def prefixEnd_2573183 : Nat := 4983230072969 + 3 ^ 40 * 2573183 * 2
def baseEnd_2573183 : Nat := 1321279690978311143378653

theorem tailTrace_2573183 : CollatzResearch.WordTrace tailWord_2573183 prefixEnd_2573183 1321279690978311143378653 := by
  unfold tailWord_2573183
  simp only [CollatzResearch.WordTrace]
  refine ⟨93851694236804930513940203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62567796157869953675960135 93851694236804930513940203)
  ·
    refine ⟨140777541355207395770910305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93851694236804930513940203 140777541355207395770910305)
    ·
      refine ⟨105583156016405546828182729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140777541355207395770910305 105583156016405546828182729)
      ·
        refine ⟨79187367012304160121137047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105583156016405546828182729 79187367012304160121137047)
        ·
          refine ⟨118781050518456240181705571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79187367012304160121137047 118781050518456240181705571)
          ·
            refine ⟨178171575777684360272558357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118781050518456240181705571 178171575777684360272558357)
            ·
              refine ⟨8351792614578954387776173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 178171575777684360272558357 8351792614578954387776173)
              ·
                refine ⟨3131922230467107895416065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8351792614578954387776173 3131922230467107895416065)
                ·
                  refine ⟨2348941672850330921562049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131922230467107895416065 2348941672850330921562049)
                  ·
                    refine ⟨1761706254637748191171537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348941672850330921562049 1761706254637748191171537)
                    ·
                      refine ⟨1321279690978311143378653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761706254637748191171537 1321279690978311143378653)
                      ·
                        rfl

theorem cell23_2573183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_2573183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573183 prefixEnd_2573183 := by exact prefixLift 2573183
  have htrace : WordTrace (prefixWord ++ tailWord_2573183) baseStart_2573183 baseEnd_2573183 := by
    simpa [prefixWord, tailWord_2573183, baseEnd_2573183] using wordTrace_append hprefix tailTrace_2573183
  have hstable : (prefixWord ++ tailWord_2573183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573183).length < 2 ^ (prefixWord ++ tailWord_2573183).sum := by decide
  have hdescent : baseEnd_2573183 < baseStart_2573183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573189 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 7]
def baseStart_2573189 : Nat := 118140960795 + 2573189 * 2 ^ 59
def prefixEnd_2573189 : Nat := 4983230072969 + 3 ^ 40 * 2573189 * 2
def baseEnd_2573189 : Nat := 146809196873582013322625

theorem tailTrace_2573189 : CollatzResearch.WordTrace tailWord_2573189 prefixEnd_2573189 146809196873582013322625 := by
  unfold tailWord_2573189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93851913074783193538658621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62567942049855462359105747 93851913074783193538658621)
  ·
    refine ⟨35194467403043697576996983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93851913074783193538658621 35194467403043697576996983)
    ·
      refine ⟨52791701104565546365495475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35194467403043697576996983 52791701104565546365495475)
      ·
        refine ⟨79187551656848319548243213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52791701104565546365495475 79187551656848319548243213)
        ·
          refine ⟨29695331871318119830591205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79187551656848319548243213 29695331871318119830591205)
          ·
            refine ⟨5567874725872147468235851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29695331871318119830591205 5567874725872147468235851)
            ·
              refine ⟨8351812088808221202353777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567874725872147468235851 8351812088808221202353777)
              ·
                refine ⟨6263859066606165901765333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8351812088808221202353777 6263859066606165901765333)
                ·
                  refine ⟨146809196873582013322625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6263859066606165901765333 146809196873582013322625)
                  ·
                    rfl

theorem cell23_2573189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_2573189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573189 prefixEnd_2573189 := by exact prefixLift 2573189
  have htrace : WordTrace (prefixWord ++ tailWord_2573189) baseStart_2573189 baseEnd_2573189 := by
    simpa [prefixWord, tailWord_2573189, baseEnd_2573189] using wordTrace_append hprefix tailTrace_2573189
  have hstable : (prefixWord ++ tailWord_2573189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573189).length < 2 ^ (prefixWord ++ tailWord_2573189).sum := by decide
  have hdescent : baseEnd_2573189 < baseStart_2573189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573217 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2573217 : Nat := 118140960795 + 2573217 * 2 ^ 59
def prefixEnd_2573217 : Nat := 4983230072969 + 3 ^ 40 * 2573217 * 2
def baseEnd_2573217 : Nat := 1321297149320564010353497

theorem tailTrace_2573217 : CollatzResearch.WordTrace tailWord_2573217 prefixEnd_2573217 1321297149320564010353497 := by
  unfold tailWord_2573217
  simp only [CollatzResearch.WordTrace]
  refine ⟨93852934318681754320677905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62568622879121169547118603 93852934318681754320677905)
  ·
    refine ⟨70389700739011315740508429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93852934318681754320677905 70389700739011315740508429)
    ·
      refine ⟨26396137777129243402690661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70389700739011315740508429 26396137777129243402690661)
      ·
        refine ⟨4949275833211733138004499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26396137777129243402690661 4949275833211733138004499)
        ·
          refine ⟨7423913749817599707006749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949275833211733138004499 7423913749817599707006749)
          ·
            refine ⟨2783967656181599890127531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7423913749817599707006749 2783967656181599890127531)
            ·
              refine ⟨4175951484272399835191297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783967656181599890127531 4175951484272399835191297)
              ·
                refine ⟨3131963613204299876393473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4175951484272399835191297 3131963613204299876393473)
                ·
                  refine ⟨2348972709903224907295105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131963613204299876393473 2348972709903224907295105)
                  ·
                    refine ⟨1761729532427418680471329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348972709903224907295105 1761729532427418680471329)
                    ·
                      refine ⟨1321297149320564010353497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761729532427418680471329 1321297149320564010353497)
                      ·
                        rfl

theorem cell23_2573217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2573217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573217 prefixEnd_2573217 := by exact prefixLift 2573217
  have htrace : WordTrace (prefixWord ++ tailWord_2573217) baseStart_2573217 baseEnd_2573217 := by
    simpa [prefixWord, tailWord_2573217, baseEnd_2573217] using wordTrace_append hprefix tailTrace_2573217
  have hstable : (prefixWord ++ tailWord_2573217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573217).length < 2 ^ (prefixWord ++ tailWord_2573217).sum := by decide
  have hdescent : baseEnd_2573217 < baseStart_2573217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573219 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 2, 5]
def baseStart_2573219 : Nat := 118140960795 + 2573219 * 2 ^ 59
def prefixEnd_2573219 : Nat := 4983230072969 + 3 ^ 40 * 2573219 * 2
def baseEnd_2573219 : Nat := 440432725427291000842829

theorem tailTrace_2573219 : CollatzResearch.WordTrace tailWord_2573219 prefixEnd_2573219 440432725427291000842829 := by
  unfold tailWord_2573219
  simp only [CollatzResearch.WordTrace]
  refine ⟨93853007264674508662250711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62568671509783005774833807 93853007264674508662250711)
  ·
    refine ⟨140779510897011762993376067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93853007264674508662250711 140779510897011762993376067)
    ·
      refine ⟨211169266345517644490064101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140779510897011762993376067 211169266345517644490064101)
      ·
        refine ⟨39594237439784558341887019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211169266345517644490064101 39594237439784558341887019)
        ·
          refine ⟨59391356159676837512830529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39594237439784558341887019 59391356159676837512830529)
          ·
            refine ⟨44543517119757628134622897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59391356159676837512830529 44543517119757628134622897)
            ·
              refine ⟨33407637839818221100967173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44543517119757628134622897 33407637839818221100967173)
              ·
                refine ⟨6263932094965916456431345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33407637839818221100967173 6263932094965916456431345)
                ·
                  refine ⟨4697949071224437342323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263932094965916456431345 4697949071224437342323509)
                  ·
                    refine ⟨440432725427291000842829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4697949071224437342323509 440432725427291000842829)
                    ·
                      rfl

theorem cell23_2573219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].length) (baseStart_2573219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573219 prefixEnd_2573219 := by exact prefixLift 2573219
  have htrace : WordTrace (prefixWord ++ tailWord_2573219) baseStart_2573219 baseEnd_2573219 := by
    simpa [prefixWord, tailWord_2573219, baseEnd_2573219] using wordTrace_append hprefix tailTrace_2573219
  have hstable : (prefixWord ++ tailWord_2573219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573219).length < 2 ^ (prefixWord ++ tailWord_2573219).sum := by decide
  have hdescent : baseEnd_2573219 < baseStart_2573219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573239 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2573239 : Nat := 118140960795 + 2573239 * 2 ^ 59
def prefixEnd_2573239 : Nat := 4983230072969 + 3 ^ 40 * 2573239 * 2
def baseEnd_2573239 : Nat := 1321308445894962924278395

theorem tailTrace_2573239 : CollatzResearch.WordTrace tailWord_2573239 prefixEnd_2573239 1321308445894962924278395 := by
  unfold tailWord_2573239
  simp only [CollatzResearch.WordTrace]
  refine ⟨93853736724602052077978771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62569157816401368051985847 93853736724602052077978771)
  ·
    refine ⟨140780605086903078116968157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93853736724602052077978771 140780605086903078116968157)
    ·
      refine ⟨52792726907588654293863059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140780605086903078116968157 52792726907588654293863059)
      ·
        refine ⟨79189090361382981440794589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52792726907588654293863059 79189090361382981440794589)
        ·
          refine ⟨29695908885518618040297971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79189090361382981440794589 29695908885518618040297971)
          ·
            refine ⟨44543863328277927060446957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29695908885518618040297971 44543863328277927060446957)
            ·
              refine ⟨16703948748104222647667609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44543863328277927060446957 16703948748104222647667609)
              ·
                refine ⟨12527961561078166985750707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16703948748104222647667609 12527961561078166985750707)
                ·
                  refine ⟨18791942341617250478626061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12527961561078166985750707 18791942341617250478626061)
                  ·
                    refine ⟨7046978378106468929484773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18791942341617250478626061 7046978378106468929484773)
                    ·
                      refine ⟨1321308445894962924278395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7046978378106468929484773 1321308445894962924278395)
                      ·
                        rfl

theorem cell23_2573239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2573239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573239 prefixEnd_2573239 := by exact prefixLift 2573239
  have htrace : WordTrace (prefixWord ++ tailWord_2573239) baseStart_2573239 baseEnd_2573239 := by
    simpa [prefixWord, tailWord_2573239, baseEnd_2573239] using wordTrace_append hprefix tailTrace_2573239
  have hstable : (prefixWord ++ tailWord_2573239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573239).length < 2 ^ (prefixWord ++ tailWord_2573239).sum := by decide
  have hdescent : baseEnd_2573239 < baseStart_2573239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573356 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_2573356 : Nat := 118140960795 + 2573356 * 2 ^ 59
def prefixEnd_2573356 : Nat := 4983230072969 + 3 ^ 40 * 2573356 * 2
def baseEnd_2573356 : Nat := 440456174377179655505119

theorem tailTrace_2573356 : CollatzResearch.WordTrace tailWord_2573356 prefixEnd_2573356 440456174377179655505119 := by
  unfold tailWord_2573356
  simp only [CollatzResearch.WordTrace]
  refine ⟨46929002032589090529993961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62572002710118787373325281 46929002032589090529993961)
  ·
    refine ⟨35196751524441817897495471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46929002032589090529993961 35196751524441817897495471)
    ·
      refine ⟨52795127286662726846243207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35196751524441817897495471 52795127286662726846243207)
      ·
        refine ⟨79192690929994090269364811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52795127286662726846243207 79192690929994090269364811)
        ·
          refine ⟨118789036394991135404047217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79192690929994090269364811 118789036394991135404047217)
          ·
            refine ⟨89091777296243351553035413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118789036394991135404047217 89091777296243351553035413)
            ·
              refine ⟨4176177060761407104048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89091777296243351553035413 4176177060761407104048535)
              ·
                refine ⟨6264265591142110656072803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176177060761407104048535 6264265591142110656072803)
                ·
                  refine ⟨9396398386713165984109205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264265591142110656072803 9396398386713165984109205)
                  ·
                    refine ⟨440456174377179655505119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9396398386713165984109205 440456174377179655505119)
                    ·
                      rfl

theorem cell23_2573356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_2573356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573356 prefixEnd_2573356 := by exact prefixLift 2573356
  have htrace : WordTrace (prefixWord ++ tailWord_2573356) baseStart_2573356 baseEnd_2573356 := by
    simpa [prefixWord, tailWord_2573356, baseEnd_2573356] using wordTrace_append hprefix tailTrace_2573356
  have hstable : (prefixWord ++ tailWord_2573356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573356).length < 2 ^ (prefixWord ++ tailWord_2573356).sum := by decide
  have hdescent : baseEnd_2573356 < baseStart_2573356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_2573359 : Nat := 118140960795 + 2573359 * 2 ^ 59
def prefixEnd_2573359 : Nat := 4983230072969 + 3 ^ 40 * 2573359 * 2
def baseEnd_2573359 : Nat := 1321370063573502454777843

theorem tailTrace_2573359 : CollatzResearch.WordTrace tailWord_2573359 prefixEnd_2573359 1321370063573502454777843 := by
  unfold tailWord_2573359
  simp only [CollatzResearch.WordTrace]
  refine ⟨93858113484167312572347131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62572075656111541714898087 93858113484167312572347131)
  ·
    refine ⟨140787170226250968858520697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93858113484167312572347131 140787170226250968858520697)
    ·
      refine ⟨105590377669688226643890523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140787170226250968858520697 105590377669688226643890523)
      ·
        refine ⟨158385566504532339965835785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105590377669688226643890523 158385566504532339965835785)
        ·
          refine ⟨118789174878399254974376839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158385566504532339965835785 118789174878399254974376839)
          ·
            refine ⟨178183762317598882461565259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118789174878399254974376839 178183762317598882461565259)
            ·
              refine ⟨267275643476398323692347889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178183762317598882461565259 267275643476398323692347889)
              ·
                refine ⟨200456732607298742769260917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267275643476398323692347889 200456732607298742769260917)
                ·
                  refine ⟨18792818681934257134618211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200456732607298742769260917 18792818681934257134618211)
                  ·
                    refine ⟨28189228022901385701927317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18792818681934257134618211 28189228022901385701927317)
                    ·
                      refine ⟨1321370063573502454777843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28189228022901385701927317 1321370063573502454777843)
                      ·
                        rfl

theorem cell23_2573359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_2573359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573359 prefixEnd_2573359 := by exact prefixLift 2573359
  have htrace : WordTrace (prefixWord ++ tailWord_2573359) baseStart_2573359 baseEnd_2573359 := by
    simpa [prefixWord, tailWord_2573359, baseEnd_2573359] using wordTrace_append hprefix tailTrace_2573359
  have hstable : (prefixWord ++ tailWord_2573359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573359).length < 2 ^ (prefixWord ++ tailWord_2573359).sum := by decide
  have hdescent : baseEnd_2573359 < baseStart_2573359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573374 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2573374 : Nat := 118140960795 + 2573374 * 2 ^ 59
def prefixEnd_2573374 : Nat := 4983230072969 + 3 ^ 40 * 2573374 * 2
def baseEnd_2573374 : Nat := 1321377765783319896090275

theorem tailTrace_2573374 : CollatzResearch.WordTrace tailWord_2573374 prefixEnd_2573374 1321377765783319896090275 := by
  unfold tailWord_2573374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732332572389121266767897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62572440386075313422762117 11732332572389121266767897)
  ·
    refine ⟨8799249429291840950075923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11732332572389121266767897 8799249429291840950075923)
    ·
      refine ⟨13198874143937761425113885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799249429291840950075923 13198874143937761425113885)
      ·
        refine ⟨4949577803976660534417707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13198874143937761425113885 4949577803976660534417707)
        ·
          refine ⟨7424366705964990801626561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949577803976660534417707 7424366705964990801626561)
          ·
            refine ⟨5568275029473743101219921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7424366705964990801626561 5568275029473743101219921)
            ·
              refine ⟨4176206272105307325914941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568275029473743101219921 4176206272105307325914941)
              ·
                refine ⟨1566077352039490247218103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176206272105307325914941 1566077352039490247218103)
                ·
                  refine ⟨2349116028059235370827155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566077352039490247218103 2349116028059235370827155)
                  ·
                    refine ⟨3523674042088853056240733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349116028059235370827155 3523674042088853056240733)
                    ·
                      refine ⟨1321377765783319896090275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523674042088853056240733 1321377765783319896090275)
                      ·
                        rfl

theorem cell23_2573374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2573374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573374 prefixEnd_2573374 := by exact prefixLift 2573374
  have htrace : WordTrace (prefixWord ++ tailWord_2573374) baseStart_2573374 baseEnd_2573374 := by
    simpa [prefixWord, tailWord_2573374, baseEnd_2573374] using wordTrace_append hprefix tailTrace_2573374
  have hstable : (prefixWord ++ tailWord_2573374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573374).length < 2 ^ (prefixWord ++ tailWord_2573374).sum := by decide
  have hdescent : baseEnd_2573374 < baseStart_2573374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573376 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_2573376 : Nat := 118140960795 + 2573376 * 2 ^ 59
def prefixEnd_2573376 : Nat := 4983230072969 + 3 ^ 40 * 2573376 * 2
def baseEnd_2573376 : Nat := 1321378792744628888265265

theorem tailTrace_2573376 : CollatzResearch.WordTrace tailWord_2573376 prefixEnd_2573376 1321378792744628888265265 := by
  unfold tailWord_2573376
  simp only [CollatzResearch.WordTrace]
  refine ⟨46929366762552862237857991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62572489016737149650477321 46929366762552862237857991)
  ·
    refine ⟨70394050143829293356786987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46929366762552862237857991 70394050143829293356786987)
    ·
      refine ⟨105591075215743940035180481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70394050143829293356786987 105591075215743940035180481)
      ·
        refine ⟨79193306411807955026385361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105591075215743940035180481 79193306411807955026385361)
        ·
          refine ⟨59394979808855966269789021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79193306411807955026385361 59394979808855966269789021)
          ·
            refine ⟨22273117428320987351170883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59394979808855966269789021 22273117428320987351170883)
            ·
              refine ⟨33409676142481481026756325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22273117428320987351170883 33409676142481481026756325)
              ·
                refine ⟨6264314276715277692516811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33409676142481481026756325 6264314276715277692516811)
                ·
                  refine ⟨9396471415072916538775217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264314276715277692516811 9396471415072916538775217)
                  ·
                    refine ⟨7047353561304687404081413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9396471415072916538775217 7047353561304687404081413)
                    ·
                      refine ⟨1321378792744628888265265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7047353561304687404081413 1321378792744628888265265)
                      ·
                        rfl

theorem cell23_2573376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_2573376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573376 prefixEnd_2573376 := by exact prefixLift 2573376
  have htrace : WordTrace (prefixWord ++ tailWord_2573376) baseStart_2573376 baseEnd_2573376 := by
    simpa [prefixWord, tailWord_2573376, baseEnd_2573376] using wordTrace_append hprefix tailTrace_2573376
  have hstable : (prefixWord ++ tailWord_2573376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573376).length < 2 ^ (prefixWord ++ tailWord_2573376).sum := by decide
  have hdescent : baseEnd_2573376 < baseStart_2573376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573377 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2573377 : Nat := 118140960795 + 2573377 * 2 ^ 59
def prefixEnd_2573377 : Nat := 4983230072969 + 3 ^ 40 * 2573377 * 2
def baseEnd_2573377 : Nat := 440459768741761128117587

theorem tailTrace_2573377 : CollatzResearch.WordTrace tailWord_2573377 prefixEnd_2573377 440459768741761128117587 := by
  unfold tailWord_2573377
  simp only [CollatzResearch.WordTrace]
  refine ⟨93858769998102101646502385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62572513332068067764334923 93858769998102101646502385)
  ·
    refine ⟨70394077498576576234876789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93858769998102101646502385 70394077498576576234876789)
    ·
      refine ⟨6599444765491554022019699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70394077498576576234876789 6599444765491554022019699)
      ·
        refine ⟨9899167148237331033029549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599444765491554022019699 9899167148237331033029549)
        ·
          refine ⟨3712187680588999137386081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9899167148237331033029549 3712187680588999137386081)
          ·
            refine ⟨2784140760441749353039561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712187680588999137386081 2784140760441749353039561)
            ·
              refine ⟨2088105570331312014779671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784140760441749353039561 2088105570331312014779671)
              ·
                refine ⟨3132158355496968022169507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088105570331312014779671 3132158355496968022169507)
                ·
                  refine ⟨4698237533245452033254261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132158355496968022169507 4698237533245452033254261)
                  ·
                    refine ⟨440459768741761128117587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4698237533245452033254261 440459768741761128117587)
                    ·
                      rfl

theorem cell23_2573377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2573377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573377 prefixEnd_2573377 := by exact prefixLift 2573377
  have htrace : WordTrace (prefixWord ++ tailWord_2573377) baseStart_2573377 baseEnd_2573377 := by
    simpa [prefixWord, tailWord_2573377, baseEnd_2573377] using wordTrace_append hprefix tailTrace_2573377
  have hstable : (prefixWord ++ tailWord_2573377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573377).length < 2 ^ (prefixWord ++ tailWord_2573377).sum := by decide
  have hdescent : baseEnd_2573377 < baseStart_2573377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573397 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2573397 : Nat := 118140960795 + 2573397 * 2 ^ 59
def prefixEnd_2573397 : Nat := 4983230072969 + 3 ^ 40 * 2573397 * 2
def baseEnd_2573397 : Nat := 1321389575838373306102669

theorem tailTrace_2573397 : CollatzResearch.WordTrace tailWord_2573397 prefixEnd_2573397 1321389575838373306102669 := by
  unfold tailWord_2573397
  simp only [CollatzResearch.WordTrace]
  refine ⟨93859499458029645062230445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62572999638686430041486963 93859499458029645062230445)
  ·
    refine ⟨35197312296761116898336417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93859499458029645062230445 35197312296761116898336417)
    ·
      refine ⟨26397984222570837673752313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35197312296761116898336417 26397984222570837673752313)
      ·
        refine ⟨19798488166928128255314235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26397984222570837673752313 19798488166928128255314235)
        ·
          refine ⟨29697732250392192382971353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19798488166928128255314235 29697732250392192382971353)
          ·
            refine ⟨22273299187794144287228515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29697732250392192382971353 22273299187794144287228515)
            ·
              refine ⟨33409948781691216430842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22273299187794144287228515 33409948781691216430842773)
              ·
                refine ⟨1566091349141775770195755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33409948781691216430842773 1566091349141775770195755)
                ·
                  refine ⟨2349137023712663655293633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566091349141775770195755 2349137023712663655293633)
                  ·
                    refine ⟨1761852767784497741470225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349137023712663655293633 1761852767784497741470225)
                    ·
                      refine ⟨1321389575838373306102669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761852767784497741470225 1321389575838373306102669)
                      ·
                        rfl

theorem cell23_2573397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2573397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573397 prefixEnd_2573397 := by exact prefixLift 2573397
  have htrace : WordTrace (prefixWord ++ tailWord_2573397) baseStart_2573397 baseEnd_2573397 := by
    simpa [prefixWord, tailWord_2573397, baseEnd_2573397] using wordTrace_append hprefix tailTrace_2573397
  have hstable : (prefixWord ++ tailWord_2573397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573397).length < 2 ^ (prefixWord ++ tailWord_2573397).sum := by decide
  have hdescent : baseEnd_2573397 < baseStart_2573397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573410 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2573410 : Nat := 118140960795 + 2573410 * 2 ^ 59
def prefixEnd_2573410 : Nat := 4983230072969 + 3 ^ 40 * 2573410 * 2
def baseEnd_2573410 : Nat := 1321396251086881755240109

theorem tailTrace_2573410 : CollatzResearch.WordTrace tailWord_2573410 prefixEnd_2573410 1321396251086881755240109 := by
  unfold tailWord_2573410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464993401745637070613421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62573315737988365521635789 23464993401745637070613421)
  ·
    refine ⟨8799372525654613901480033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23464993401745637070613421 8799372525654613901480033)
    ·
      refine ⟨6599529394240960426110025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8799372525654613901480033 6599529394240960426110025)
      ·
        refine ⟨4949647045680720319582519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6599529394240960426110025 4949647045680720319582519)
        ·
          refine ⟨7424470568521080479373779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949647045680720319582519 7424470568521080479373779)
          ·
            refine ⟨11136705852781620719060669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424470568521080479373779 11136705852781620719060669)
            ·
              refine ⟨4176264694793107769647751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11136705852781620719060669 4176264694793107769647751)
              ·
                refine ⟨6264397042189661654471627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176264694793107769647751 6264397042189661654471627)
                ·
                  refine ⟨9396595563284492481707441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264397042189661654471627 9396595563284492481707441)
                  ·
                    refine ⟨7047446672463369361280581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9396595563284492481707441 7047446672463369361280581)
                    ·
                      refine ⟨1321396251086881755240109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7047446672463369361280581 1321396251086881755240109)
                      ·
                        rfl

theorem cell23_2573410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2573410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573410 prefixEnd_2573410 := by exact prefixLift 2573410
  have htrace : WordTrace (prefixWord ++ tailWord_2573410) baseStart_2573410 baseEnd_2573410 := by
    simpa [prefixWord, tailWord_2573410, baseEnd_2573410] using wordTrace_append hprefix tailTrace_2573410
  have hstable : (prefixWord ++ tailWord_2573410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573410).length < 2 ^ (prefixWord ++ tailWord_2573410).sum := by decide
  have hdescent : baseEnd_2573410 < baseStart_2573410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573426 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2573426 : Nat := 118140960795 + 2573426 * 2 ^ 59
def prefixEnd_2573426 : Nat := 4983230072969 + 3 ^ 40 * 2573426 * 2
def baseEnd_2573426 : Nat := 1321404466777353692640035

theorem tailTrace_2573426 : CollatzResearch.WordTrace tailWord_2573426 prefixEnd_2573426 1321404466777353692640035 := by
  unfold tailWord_2573426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23465139293731145753759033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62573704783283055343357421 23465139293731145753759033)
  ·
    refine ⟨17598854470298359315319275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23465139293731145753759033 17598854470298359315319275)
    ·
      refine ⟨26398281705447538972978913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17598854470298359315319275 26398281705447538972978913)
      ·
        refine ⟨19798711279085654229734185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26398281705447538972978913 19798711279085654229734185)
        ·
          refine ⟨14849033459314240672300639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19798711279085654229734185 14849033459314240672300639)
          ·
            refine ⟨22273550188971361008450959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14849033459314240672300639 22273550188971361008450959)
            ·
              refine ⟨33410325283457041512676439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22273550188971361008450959 33410325283457041512676439)
              ·
                refine ⟨50115487925185562269014659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33410325283457041512676439 50115487925185562269014659)
                ·
                  refine ⟨75173231887778343403521989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50115487925185562269014659 75173231887778343403521989)
                  ·
                    refine ⟨14094980978958439388160373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75173231887778343403521989 14094980978958439388160373)
                    ·
                      refine ⟨1321404466777353692640035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14094980978958439388160373 1321404466777353692640035)
                      ·
                        rfl

theorem cell23_2573426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2573426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573426 prefixEnd_2573426 := by exact prefixLift 2573426
  have htrace : WordTrace (prefixWord ++ tailWord_2573426) baseStart_2573426 baseEnd_2573426 := by
    simpa [prefixWord, tailWord_2573426, baseEnd_2573426] using wordTrace_append hprefix tailTrace_2573426
  have hstable : (prefixWord ++ tailWord_2573426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573426).length < 2 ^ (prefixWord ++ tailWord_2573426).sum := by decide
  have hdescent : baseEnd_2573426 < baseStart_2573426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573430 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2573430 : Nat := 118140960795 + 2573430 * 2 ^ 59
def prefixEnd_2573430 : Nat := 4983230072969 + 3 ^ 40 * 2573430 * 2
def baseEnd_2573430 : Nat := 1321406520699971676990017

theorem tailTrace_2573430 : CollatzResearch.WordTrace tailWord_2573430 prefixEnd_2573430 1321406520699971676990017 := by
  unfold tailWord_2573430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866293941681880731136359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62573802044606727798787829 5866293941681880731136359)
  ·
    refine ⟨8799440912522821096704539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866293941681880731136359 8799440912522821096704539)
    ·
      refine ⟨13199161368784231645056809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799440912522821096704539 13199161368784231645056809)
      ·
        refine ⟨9899371026588173733792607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13199161368784231645056809 9899371026588173733792607)
        ·
          refine ⟨14849056539882260600688911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899371026588173733792607 14849056539882260600688911)
          ·
            refine ⟨22273584809823390901033367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14849056539882260600688911 22273584809823390901033367)
            ·
              refine ⟨33410377214735086351550051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22273584809823390901033367 33410377214735086351550051)
              ·
                refine ⟨50115565822102629527325077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33410377214735086351550051 50115565822102629527325077)
                ·
                  refine ⟨2349167147911060759093363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50115565822102629527325077 2349167147911060759093363)
                  ·
                    refine ⟨3523750721866591138640045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349167147911060759093363 3523750721866591138640045)
                    ·
                      refine ⟨1321406520699971676990017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523750721866591138640045 1321406520699971676990017)
                      ·
                        rfl

theorem cell23_2573430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2573430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573430 prefixEnd_2573430 := by exact prefixLift 2573430
  have htrace : WordTrace (prefixWord ++ tailWord_2573430) baseStart_2573430 baseEnd_2573430 := by
    simpa [prefixWord, tailWord_2573430, baseEnd_2573430] using wordTrace_append hprefix tailTrace_2573430
  have hstable : (prefixWord ++ tailWord_2573430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573430).length < 2 ^ (prefixWord ++ tailWord_2573430).sum := by decide
  have hdescent : baseEnd_2573430 < baseStart_2573430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573440 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2]
def baseStart_2573440 : Nat := 118140960795 + 2573440 * 2 ^ 59
def prefixEnd_2573440 : Nat := 4983230072969 + 3 ^ 40 * 2573440 * 2
def baseEnd_2573440 : Nat := 1321411655506516637864971

theorem tailTrace_2573440 : CollatzResearch.WordTrace tailWord_2573440 prefixEnd_2573440 1321411655506516637864971 := by
  unfold tailWord_2573440
  simp only [CollatzResearch.WordTrace]
  refine ⟨46930533898436931703022887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62574045197915908937363849 46930533898436931703022887)
  ·
    refine ⟨70395800847655397554534331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46930533898436931703022887 70395800847655397554534331)
    ·
      refine ⟨105593701271483096331801497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70395800847655397554534331 105593701271483096331801497)
      ·
        refine ⟨79195275953612322248851123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105593701271483096331801497 79195275953612322248851123)
        ·
          refine ⟨118792913930418483373276685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79195275953612322248851123 118792913930418483373276685)
          ·
            refine ⟨44547342723906931264978757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118792913930418483373276685 44547342723906931264978757)
            ·
              refine ⟨8352626760732549612183517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44547342723906931264978757 8352626760732549612183517)
              ·
                refine ⟨3132235035274706104568819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8352626760732549612183517 3132235035274706104568819)
                ·
                  refine ⟨4698352552912059156853229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132235035274706104568819 4698352552912059156853229)
                  ·
                    refine ⟨1761882207342022183819961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4698352552912059156853229 1761882207342022183819961)
                    ·
                      refine ⟨1321411655506516637864971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761882207342022183819961 1321411655506516637864971)
                      ·
                        rfl

theorem cell23_2573440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_2573440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573440 prefixEnd_2573440 := by exact prefixLift 2573440
  have htrace : WordTrace (prefixWord ++ tailWord_2573440) baseStart_2573440 baseEnd_2573440 := by
    simpa [prefixWord, tailWord_2573440, baseEnd_2573440] using wordTrace_append hprefix tailTrace_2573440
  have hstable : (prefixWord ++ tailWord_2573440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573440).length < 2 ^ (prefixWord ++ tailWord_2573440).sum := by decide
  have hdescent : baseEnd_2573440 < baseStart_2573440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573464 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2573464 : Nat := 118140960795 + 2573464 * 2 ^ 59
def prefixEnd_2573464 : Nat := 4983230072969 + 3 ^ 40 * 2573464 * 2
def baseEnd_2573464 : Nat := 1321423979042224543964861

theorem tailTrace_2573464 : CollatzResearch.WordTrace tailWord_2573464 prefixEnd_2573464 1321423979042224543964861 := by
  unfold tailWord_2573464
  simp only [CollatzResearch.WordTrace]
  refine ⟨46930971574393457752459723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62574628765857943669946297 46930971574393457752459723)
  ·
    refine ⟨70396457361590186628689585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46930971574393457752459723 70396457361590186628689585)
    ·
      refine ⟨52797343021192639971517189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70396457361590186628689585 52797343021192639971517189)
      ·
        refine ⟨9899501816473619994659473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52797343021192639971517189 9899501816473619994659473)
        ·
          refine ⟨7424626362355214995994605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9899501816473619994659473 7424626362355214995994605)
          ·
            refine ⟨2784234885883205623497977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7424626362355214995994605 2784234885883205623497977)
            ·
              refine ⟨2088176164412404217623483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784234885883205623497977 2088176164412404217623483)
              ·
                refine ⟨3132264246618606326435225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088176164412404217623483 3132264246618606326435225)
                ·
                  refine ⟨2349198184963954744826419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132264246618606326435225 2349198184963954744826419)
                  ·
                    refine ⟨3523797277445932117239629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349198184963954744826419 3523797277445932117239629)
                    ·
                      refine ⟨1321423979042224543964861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3523797277445932117239629 1321423979042224543964861)
                      ·
                        rfl

theorem cell23_2573464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2573464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573464 prefixEnd_2573464 := by exact prefixLift 2573464
  have htrace : WordTrace (prefixWord ++ tailWord_2573464) baseStart_2573464 baseEnd_2573464 := by
    simpa [prefixWord, tailWord_2573464, baseEnd_2573464] using wordTrace_append hprefix tailTrace_2573464
  have hstable : (prefixWord ++ tailWord_2573464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573464).length < 2 ^ (prefixWord ++ tailWord_2573464).sum := by decide
  have hdescent : baseEnd_2573464 < baseStart_2573464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573504 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2]
def baseStart_2573504 : Nat := 118140960795 + 2573504 * 2 ^ 59
def prefixEnd_2573504 : Nat := 4983230072969 + 3 ^ 40 * 2573504 * 2
def baseEnd_2573504 : Nat := 1321444518268404387464677

theorem tailTrace_2573504 : CollatzResearch.WordTrace tailWord_2573504 prefixEnd_2573504 1321444518268404387464677 := by
  unfold tailWord_2573504
  simp only [CollatzResearch.WordTrace]
  refine ⟨46931701034321001168187783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62575601379094668224250377 46931701034321001168187783)
  ·
    refine ⟨70397551551481501752281675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46931701034321001168187783 70397551551481501752281675)
    ·
      refine ⟨105596327327222252628422513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70397551551481501752281675 105596327327222252628422513)
      ·
        refine ⟨79197245495416689471316885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105596327327222252628422513 79197245495416689471316885)
        ·
          refine ⟨3712370882597657318967979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79197245495416689471316885 3712370882597657318967979)
          ·
            refine ⟨5568556323896485978451969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712370882597657318967979 5568556323896485978451969)
            ·
              refine ⟨4176417242922364483838977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568556323896485978451969 4176417242922364483838977)
              ·
                refine ⟨3132312932191773362879233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4176417242922364483838977 3132312932191773362879233)
                ·
                  refine ⟨2349234699143830022159425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132312932191773362879233 2349234699143830022159425)
                  ·
                    refine ⟨1761926024357872516619569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349234699143830022159425 1761926024357872516619569)
                    ·
                      refine ⟨1321444518268404387464677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761926024357872516619569 1321444518268404387464677)
                      ·
                        rfl

theorem cell23_2573504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_2573504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573504 prefixEnd_2573504 := by exact prefixLift 2573504
  have htrace : WordTrace (prefixWord ++ tailWord_2573504) baseStart_2573504 baseEnd_2573504 := by
    simpa [prefixWord, tailWord_2573504, baseEnd_2573504] using wordTrace_append hprefix tailTrace_2573504
  have hstable : (prefixWord ++ tailWord_2573504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573504).length < 2 ^ (prefixWord ++ tailWord_2573504).sum := by decide
  have hdescent : baseEnd_2573504 < baseStart_2573504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573553 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_2573553 : Nat := 118140960795 + 2573553 * 2 ^ 59
def prefixEnd_2573553 : Nat := 4983230072969 + 3 ^ 40 * 2573553 * 2
def baseEnd_2573553 : Nat := 440489892940158231917317

theorem tailTrace_2573553 : CollatzResearch.WordTrace tailWord_2573553 prefixEnd_2573553 440489892940158231917317 := by
  unfold tailWord_2573553
  simp only [CollatzResearch.WordTrace]
  refine ⟨93865189245464483704909313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62576792830309655803272875 93865189245464483704909313)
  ·
    refine ⟨70398891934098362778681985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93865189245464483704909313 70398891934098362778681985)
    ·
      refine ⟨52799168950573772084011489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70398891934098362778681985 52799168950573772084011489)
      ·
        refine ⟨39599376712930329063008617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52799168950573772084011489 39599376712930329063008617)
        ·
          refine ⟨29699532534697746797256463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39599376712930329063008617 29699532534697746797256463)
          ·
            refine ⟨44549298802046620195884695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29699532534697746797256463 44549298802046620195884695)
            ·
              refine ⟨66823948203069930293827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44549298802046620195884695 66823948203069930293827043)
              ·
                refine ⟨100235922304604895440740565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66823948203069930293827043 100235922304604895440740565)
                ·
                  refine ⟨2349279429014177236892357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100235922304604895440740565 2349279429014177236892357)
                  ·
                    refine ⟨440489892940158231917317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349279429014177236892357 440489892940158231917317)
                    ·
                      rfl

theorem cell23_2573553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_2573553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573553 prefixEnd_2573553 := by exact prefixLift 2573553
  have htrace : WordTrace (prefixWord ++ tailWord_2573553) baseStart_2573553 baseEnd_2573553 := by
    simpa [prefixWord, tailWord_2573553, baseEnd_2573553] using wordTrace_append hprefix tailTrace_2573553
  have hstable : (prefixWord ++ tailWord_2573553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573553).length < 2 ^ (prefixWord ++ tailWord_2573553).sum := by decide
  have hdescent : baseEnd_2573553 < baseStart_2573553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573630 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2573630 : Nat := 118140960795 + 2573630 * 2 ^ 59
def prefixEnd_2573630 : Nat := 4983230072969 + 3 ^ 40 * 2573630 * 2
def baseEnd_2573630 : Nat := 440503072276956964829699

theorem tailTrace_2573630 : CollatzResearch.WordTrace tailWord_2573630 prefixEnd_2573630 440503072276956964829699 := by
  unfold tailWord_2573630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733499708273190731932793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62578665110790350570308229 11733499708273190731932793)
  ·
    refine ⟨8800124781204893048949595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11733499708273190731932793 8800124781204893048949595)
    ·
      refine ⟨13200187171807339573424393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800124781204893048949595 13200187171807339573424393)
      ·
        refine ⟨9900140378855504680068295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13200187171807339573424393 9900140378855504680068295)
        ·
          refine ⟨14850210568283257020102443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900140378855504680068295 14850210568283257020102443)
          ·
            refine ⟨22275315852424885530153665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14850210568283257020102443 22275315852424885530153665)
            ·
              refine ⟨16706486889318664147615249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22275315852424885530153665 16706486889318664147615249)
              ·
                refine ⟨12529865166988998110711437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16706486889318664147615249 12529865166988998110711437)
                ·
                  refine ⟨4698699437620874291516789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12529865166988998110711437 4698699437620874291516789)
                  ·
                    refine ⟨440503072276956964829699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4698699437620874291516789 440503072276956964829699)
                    ·
                      rfl

theorem cell23_2573630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2573630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573630 prefixEnd_2573630 := by exact prefixLift 2573630
  have htrace : WordTrace (prefixWord ++ tailWord_2573630) baseStart_2573630 baseEnd_2573630 := by
    simpa [prefixWord, tailWord_2573630, baseEnd_2573630] using wordTrace_append hprefix tailTrace_2573630
  have hstable : (prefixWord ++ tailWord_2573630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573630).length < 2 ^ (prefixWord ++ tailWord_2573630).sum := by decide
  have hdescent : baseEnd_2573630 < baseStart_2573630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573677 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2573677 : Nat := 118140960795 + 2573677 * 2 ^ 59
def prefixEnd_2573677 : Nat := 4983230072969 + 3 ^ 40 * 2573677 * 2
def baseEnd_2573677 : Nat := 440511116807210736867127

theorem tailTrace_2573677 : CollatzResearch.WordTrace tailWord_2573677 prefixEnd_2573677 440511116807210736867127 := by
  unfold tailWord_2573677
  simp only [CollatzResearch.WordTrace]
  refine ⟨93869711897015252882423285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62579807931343501921615523 93869711897015252882423285)
  ·
    refine ⟨8800285490345179957727183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93869711897015252882423285 8800285490345179957727183)
    ·
      refine ⟨13200428235517769936590775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800285490345179957727183 13200428235517769936590775)
      ·
        refine ⟨19800642353276654904886163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13200428235517769936590775 19800642353276654904886163)
        ·
          refine ⟨29700963529914982357329245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19800642353276654904886163 29700963529914982357329245)
          ·
            refine ⟨11137861323718118383998467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29700963529914982357329245 11137861323718118383998467)
            ·
              refine ⟨16706791985577177575997701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11137861323718118383998467 16706791985577177575997701)
              ·
                refine ⟨3132523497295720795499569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16706791985577177575997701 3132523497295720795499569)
                ·
                  refine ⟨2349392622971790596624677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132523497295720795499569 2349392622971790596624677)
                  ·
                    refine ⟨440511116807210736867127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349392622971790596624677 440511116807210736867127)
                    ·
                      rfl

theorem cell23_2573677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2573677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573677 prefixEnd_2573677 := by exact prefixLift 2573677
  have htrace : WordTrace (prefixWord ++ tailWord_2573677) baseStart_2573677 baseEnd_2573677 := by
    simpa [prefixWord, tailWord_2573677, baseEnd_2573677] using wordTrace_append hprefix tailTrace_2573677
  have hstable : (prefixWord ++ tailWord_2573677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573677).length < 2 ^ (prefixWord ++ tailWord_2573677).sum := by decide
  have hdescent : baseEnd_2573677 < baseStart_2573677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573678 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2573678 : Nat := 118140960795 + 2573678 * 2 ^ 59
def prefixEnd_2573678 : Nat := 4983230072969 + 3 ^ 40 * 2573678 * 2
def baseEnd_2573678 : Nat := 1321533863902286706688877

theorem tailTrace_2573678 : CollatzResearch.WordTrace tailWord_2573678 prefixEnd_2573678 1321533863902286706688877 := by
  unfold tailWord_2573678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733718546251453756651211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62579832246674420035473125 11733718546251453756651211)
  ·
    refine ⟨17600577819377180634976817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11733718546251453756651211 17600577819377180634976817)
    ·
      refine ⟨13200433364532885476232613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17600577819377180634976817 13200433364532885476232613)
      ·
        refine ⟨2475081255849916026793615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13200433364532885476232613 2475081255849916026793615)
        ·
          refine ⟨3712621883774874040190423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475081255849916026793615 3712621883774874040190423)
          ·
            refine ⟨5568932825662311060285635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712621883774874040190423 5568932825662311060285635)
            ·
              refine ⟨8353399238493466590428453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568932825662311060285635 8353399238493466590428453)
              ·
                refine ⟨1566262357217524985705335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8353399238493466590428453 1566262357217524985705335)
                ·
                  refine ⟨2349393535826287478558003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566262357217524985705335 2349393535826287478558003)
                  ·
                    refine ⟨3524090303739431217837005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349393535826287478558003 3524090303739431217837005)
                    ·
                      refine ⟨1321533863902286706688877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3524090303739431217837005 1321533863902286706688877)
                      ·
                        rfl

theorem cell23_2573678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2573678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573678 prefixEnd_2573678 := by exact prefixLift 2573678
  have htrace : WordTrace (prefixWord ++ tailWord_2573678) baseStart_2573678 baseEnd_2573678 := by
    simpa [prefixWord, tailWord_2573678, baseEnd_2573678] using wordTrace_append hprefix tailTrace_2573678
  have hstable : (prefixWord ++ tailWord_2573678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573678).length < 2 ^ (prefixWord ++ tailWord_2573678).sum := by decide
  have hdescent : baseEnd_2573678 < baseStart_2573678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573713 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_2573713 : Nat := 118140960795 + 2573713 * 2 ^ 59
def prefixEnd_2573713 : Nat := 4983230072969 + 3 ^ 40 * 2573713 * 2
def baseEnd_2573713 : Nat := 1321551835725194069751215

theorem tailTrace_2573713 : CollatzResearch.WordTrace tailWord_2573713 prefixEnd_2573713 1321551835725194069751215 := by
  unfold tailWord_2573713
  simp only [CollatzResearch.WordTrace]
  refine ⟨93871024924884831030733793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62580683283256554020489195 93871024924884831030733793)
  ·
    refine ⟨70403268693663623273050345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93871024924884831030733793 70403268693663623273050345)
    ·
      refine ⟨52802451520247717454787759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70403268693663623273050345 52802451520247717454787759)
      ·
        refine ⟨79203677280371576182181639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52802451520247717454787759 79203677280371576182181639)
        ·
          refine ⟨118805515920557364273272459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79203677280371576182181639 118805515920557364273272459)
          ·
            refine ⟨178208273880836046409908689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118805515920557364273272459 178208273880836046409908689)
            ·
              refine ⟨133656205410627034807431517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178208273880836046409908689 133656205410627034807431517)
              ·
                refine ⟨50121077028985138052786819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133656205410627034807431517 50121077028985138052786819)
                ·
                  refine ⟨75181615543477707079180229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50121077028985138052786819 75181615543477707079180229)
                  ·
                    refine ⟨14096552914402070077346293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75181615543477707079180229 14096552914402070077346293)
                    ·
                      refine ⟨1321551835725194069751215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14096552914402070077346293 1321551835725194069751215)
                      ·
                        rfl

theorem cell23_2573713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_2573713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573713 prefixEnd_2573713 := by exact prefixLift 2573713
  have htrace : WordTrace (prefixWord ++ tailWord_2573713) baseStart_2573713 baseEnd_2573713 := by
    simpa [prefixWord, tailWord_2573713, baseEnd_2573713] using wordTrace_append hprefix tailTrace_2573713
  have hstable : (prefixWord ++ tailWord_2573713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573713).length < 2 ^ (prefixWord ++ tailWord_2573713).sum := by decide
  have hdescent : baseEnd_2573713 < baseStart_2573713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573760 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_2573760 : Nat := 118140960795 + 2573760 * 2 ^ 59
def prefixEnd_2573760 : Nat := 4983230072969 + 3 ^ 40 * 2573760 * 2
def baseEnd_2573760 : Nat := 1321575969315955385863499

theorem tailTrace_2573760 : CollatzResearch.WordTrace tailWord_2573760 prefixEnd_2573760 1321575969315955385863499 := by
  unfold tailWord_2573760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46936369577857279028847367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62581826103809705371796489 46936369577857279028847367)
  ·
    refine ⟨70404554366785918543271051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46936369577857279028847367 70404554366785918543271051)
    ·
      refine ⟨105606831550178877814906577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70404554366785918543271051 105606831550178877814906577)
      ·
        refine ⟨79205123662634158361179933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105606831550178877814906577 79205123662634158361179933)
        ·
          refine ⟨29701921373487809385442475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79205123662634158361179933 29701921373487809385442475)
          ·
            refine ⟨44552882060231714078163713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29701921373487809385442475 44552882060231714078163713)
            ·
              refine ⟨33414661545173785558622785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44552882060231714078163713 33414661545173785558622785)
              ·
                refine ⟨25060996158880339168967089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33414661545173785558622785 25060996158880339168967089)
                ·
                  refine ⟨18795747119160254376725317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25060996158880339168967089 18795747119160254376725317)
                  ·
                    refine ⟨3524202584842547695635997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18795747119160254376725317 3524202584842547695635997)
                    ·
                      refine ⟨1321575969315955385863499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3524202584842547695635997 1321575969315955385863499)
                      ·
                        rfl

theorem cell23_2573760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_2573760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573760 prefixEnd_2573760 := by exact prefixLift 2573760
  have htrace : WordTrace (prefixWord ++ tailWord_2573760) baseStart_2573760 baseEnd_2573760 := by
    simpa [prefixWord, tailWord_2573760, baseEnd_2573760] using wordTrace_append hprefix tailTrace_2573760
  have hstable : (prefixWord ++ tailWord_2573760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573760).length < 2 ^ (prefixWord ++ tailWord_2573760).sum := by decide
  have hdescent : baseEnd_2573760 < baseStart_2573760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573774 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_2573774 : Nat := 118140960795 + 2573774 * 2 ^ 59
def prefixEnd_2573774 : Nat := 4983230072969 + 3 ^ 40 * 2573774 * 2
def baseEnd_2573774 : Nat := 1321583158045118331088435

theorem tailTrace_2573774 : CollatzResearch.WordTrace tailWord_2573774 prefixEnd_2573774 1321583158045118331088435 := by
  unfold tailWord_2573774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11734156222207979806088047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62582166518442558965802917 11734156222207979806088047)
  ·
    refine ⟨17601234333311969709132071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11734156222207979806088047 17601234333311969709132071)
    ·
      refine ⟨26401851499967954563698107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17601234333311969709132071 26401851499967954563698107)
      ·
        refine ⟨39602777249951931845547161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26401851499967954563698107 39602777249951931845547161)
        ·
          refine ⟨29702082937463948884160371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39602777249951931845547161 29702082937463948884160371)
          ·
            refine ⟨44553124406195923326240557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29702082937463948884160371 44553124406195923326240557)
            ·
              refine ⟨16707421652323471247340209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44553124406195923326240557 16707421652323471247340209)
              ·
                refine ⟨12530566239242603435505157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16707421652323471247340209 12530566239242603435505157)
                ·
                  refine ⟨2349481169857988144157217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12530566239242603435505157 2349481169857988144157217)
                  ·
                    refine ⟨1762110877393491108117913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349481169857988144157217 1762110877393491108117913)
                    ·
                      refine ⟨1321583158045118331088435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762110877393491108117913 1321583158045118331088435)
                      ·
                        rfl

theorem cell23_2573774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_2573774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573774 prefixEnd_2573774 := by exact prefixLift 2573774
  have htrace : WordTrace (prefixWord ++ tailWord_2573774) baseStart_2573774 baseEnd_2573774 := by
    simpa [prefixWord, tailWord_2573774, baseEnd_2573774] using wordTrace_append hprefix tailTrace_2573774
  have hstable : (prefixWord ++ tailWord_2573774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573774).length < 2 ^ (prefixWord ++ tailWord_2573774).sum := by decide
  have hdescent : baseEnd_2573774 < baseStart_2573774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573797 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 7]
def baseStart_2573797 : Nat := 118140960795 + 2573797 * 2 ^ 59
def prefixEnd_2573797 : Nat := 4983230072969 + 3 ^ 40 * 2573797 * 2
def baseEnd_2573797 : Nat := 146843885344463526788981

theorem tailTrace_2573797 : CollatzResearch.WordTrace tailWord_2573797 prefixEnd_2573797 146843885344463526788981 := by
  unfold tailWord_2573797
  simp only [CollatzResearch.WordTrace]
  refine ⟨93874088656580513376791645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62582725771053675584527763 93874088656580513376791645)
  ·
    refine ⟨35202783246217692516296867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93874088656580513376791645 35202783246217692516296867)
    ·
      refine ⟨52804174869326538774445301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35202783246217692516296867 52804174869326538774445301)
      ·
        refine ⟨4950391393999363010104247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52804174869326538774445301 4950391393999363010104247)
        ·
          refine ⟨7425587090999044515156371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950391393999363010104247 7425587090999044515156371)
          ·
            refine ⟨11138380636498566772734557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7425587090999044515156371 11138380636498566772734557)
            ·
              refine ⟨4176892738686962539775459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11138380636498566772734557 4176892738686962539775459)
              ·
                refine ⟨6265339108030443809663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176892738686962539775459 6265339108030443809663189)
                ·
                  refine ⟨146843885344463526788981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6265339108030443809663189 146843885344463526788981)
                  ·
                    rfl

theorem cell23_2573797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_2573797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573797 prefixEnd_2573797 := by exact prefixLift 2573797
  have htrace : WordTrace (prefixWord ++ tailWord_2573797) baseStart_2573797 baseEnd_2573797 := by
    simpa [prefixWord, tailWord_2573797, baseEnd_2573797] using wordTrace_append hprefix tailTrace_2573797
  have hstable : (prefixWord ++ tailWord_2573797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573797).length < 2 ^ (prefixWord ++ tailWord_2573797).sum := by decide
  have hdescent : baseEnd_2573797 < baseStart_2573797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573808 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2]
def baseStart_2573808 : Nat := 118140960795 + 2573808 * 2 ^ 59
def prefixEnd_2573808 : Nat := 4983230072969 + 3 ^ 40 * 2573808 * 2
def baseEnd_2573808 : Nat := 1321600616387371198063279

theorem tailTrace_2573808 : CollatzResearch.WordTrace tailWord_2573808 prefixEnd_2573808 1321600616387371198063279 := by
  unfold tailWord_2573808
  simp only [CollatzResearch.WordTrace]
  refine ⟨46937244929770331127721039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62582993239693774836961385 46937244929770331127721039)
  ·
    refine ⟨70405867394655496691581559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46937244929770331127721039 70405867394655496691581559)
    ·
      refine ⟨105608801091983245037372339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70405867394655496691581559 105608801091983245037372339)
      ·
        refine ⟨158413201637974867556058509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105608801091983245037372339 158413201637974867556058509)
        ·
          refine ⟨59404950614240575333521941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158413201637974867556058509 59404950614240575333521941)
          ·
            refine ⟨2784607060042526968758841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59404950614240575333521941 2784607060042526968758841)
            ·
              refine ⟨2088455295031895226569131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784607060042526968758841 2088455295031895226569131)
              ·
                refine ⟨3132682942547842839853697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088455295031895226569131 3132682942547842839853697)
                ·
                  refine ⟨2349512206910882129890273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132682942547842839853697 2349512206910882129890273)
                  ·
                    refine ⟨1762134155183161597417705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349512206910882129890273 1762134155183161597417705)
                    ·
                      refine ⟨1321600616387371198063279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762134155183161597417705 1321600616387371198063279)
                      ·
                        rfl

theorem cell23_2573808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2].length) (baseStart_2573808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573808 prefixEnd_2573808 := by exact prefixLift 2573808
  have htrace : WordTrace (prefixWord ++ tailWord_2573808) baseStart_2573808 baseEnd_2573808 := by
    simpa [prefixWord, tailWord_2573808, baseEnd_2573808] using wordTrace_append hprefix tailTrace_2573808
  have hstable : (prefixWord ++ tailWord_2573808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573808).length < 2 ^ (prefixWord ++ tailWord_2573808).sum := by decide
  have hdescent : baseEnd_2573808 < baseStart_2573808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573848 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 5]
def baseStart_2573848 : Nat := 118140960795 + 2573848 * 2 ^ 59
def prefixEnd_2573848 : Nat := 4983230072969 + 3 ^ 40 * 2573848 * 2
def baseEnd_2573848 : Nat := 146846795068172337951455

theorem tailTrace_2573848 : CollatzResearch.WordTrace tailWord_2573848 prefixEnd_2573848 146846795068172337951455 := by
  unfold tailWord_2573848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46937974389697874543449099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62583965852930499391265465 46937974389697874543449099)
  ·
    refine ⟨70406961584546811815173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46937974389697874543449099 70406961584546811815173649)
    ·
      refine ⟨52805221188410108861380237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70406961584546811815173649 52805221188410108861380237)
      ·
        refine ⟨19801957945653790823017589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52805221188410108861380237 19801957945653790823017589)
        ·
          refine ⟨1856433557405042889657899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19801957945653790823017589 1856433557405042889657899)
          ·
            refine ⟨2784650336107564334486849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856433557405042889657899 2784650336107564334486849)
            ·
              refine ⟨2088487752080673250865137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784650336107564334486849 2088487752080673250865137)
              ·
                refine ⟨1566365814060504938148853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088487752080673250865137 1566365814060504938148853)
                ·
                  refine ⟨146846795068172337951455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566365814060504938148853 146846795068172337951455)
                  ·
                    rfl

theorem cell23_2573848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 5].length) (baseStart_2573848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573848 prefixEnd_2573848 := by exact prefixLift 2573848
  have htrace : WordTrace (prefixWord ++ tailWord_2573848) baseStart_2573848 baseEnd_2573848 := by
    simpa [prefixWord, tailWord_2573848, baseEnd_2573848] using wordTrace_append hprefix tailTrace_2573848
  have hstable : (prefixWord ++ tailWord_2573848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573848).length < 2 ^ (prefixWord ++ tailWord_2573848).sum := by decide
  have hdescent : baseEnd_2573848 < baseStart_2573848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573850 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2573850 : Nat := 118140960795 + 2573850 * 2 ^ 59
def prefixEnd_2573850 : Nat := 4983230072969 + 3 ^ 40 * 2573850 * 2
def baseEnd_2573850 : Nat := 1321622182574860033738085

theorem tailTrace_2573850 : CollatzResearch.WordTrace tailWord_2573850 prefixEnd_2573850 1321622182574860033738085 := by
  unfold tailWord_2573850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23469005431347125857117751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62584014483592335618980669 23469005431347125857117751)
  ·
    refine ⟨35203508147020688785676627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23469005431347125857117751 35203508147020688785676627)
    ·
      refine ⟨52805262220531033178514941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35203508147020688785676627 52805262220531033178514941)
      ·
        refine ⟨19801973332699137441943103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52805262220531033178514941 19801973332699137441943103)
        ·
          refine ⟨29702959999048706162914655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19801973332699137441943103 29702959999048706162914655)
          ·
            refine ⟨44554439998573059244371983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29702959999048706162914655 44554439998573059244371983)
            ·
              refine ⟨66831659997859588866557975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44554439998573059244371983 66831659997859588866557975)
              ·
                refine ⟨100247489996789383299836963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66831659997859588866557975 100247489996789383299836963)
                ·
                  refine ⟨150371234995184074949755445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100247489996789383299836963 150371234995184074949755445)
                  ·
                    refine ⟨14097303280798507026539573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150371234995184074949755445 14097303280798507026539573)
                    ·
                      refine ⟨1321622182574860033738085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14097303280798507026539573 1321622182574860033738085)
                      ·
                        rfl

theorem cell23_2573850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2573850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573850 prefixEnd_2573850 := by exact prefixLift 2573850
  have htrace : WordTrace (prefixWord ++ tailWord_2573850) baseStart_2573850 baseEnd_2573850 := by
    simpa [prefixWord, tailWord_2573850, baseEnd_2573850] using wordTrace_append hprefix tailTrace_2573850
  have hstable : (prefixWord ++ tailWord_2573850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573850).length < 2 ^ (prefixWord ++ tailWord_2573850).sum := by decide
  have hdescent : baseEnd_2573850 < baseStart_2573850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573878 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2573878 : Nat := 118140960795 + 2573878 * 2 ^ 59
def prefixEnd_2573878 : Nat := 4983230072969 + 3 ^ 40 * 2573878 * 2
def baseEnd_2573878 : Nat := 440545520011061974729319

theorem tailTrace_2573878 : CollatzResearch.WordTrace tailWord_2573878 prefixEnd_2573878 440545520011061974729319 := by
  unfold tailWord_2573878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867315185580441513155643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62584695312858042806993525 5867315185580441513155643)
  ·
    refine ⟨8800972778370662269733465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5867315185580441513155643 8800972778370662269733465)
    ·
      refine ⟨6600729583777996702300099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8800972778370662269733465 6600729583777996702300099)
      ·
        refine ⟨9901094375666995053450149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600729583777996702300099 9901094375666995053450149)
        ·
          refine ⟨1856455195437561572521903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9901094375666995053450149 1856455195437561572521903)
          ·
            refine ⟨2784682793156342358782855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856455195437561572521903 2784682793156342358782855)
            ·
              refine ⟨4177024189734513538174283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784682793156342358782855 4177024189734513538174283)
              ·
                refine ⟨6265536284601770307261425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177024189734513538174283 6265536284601770307261425)
                ·
                  refine ⟨4699152213451327730446069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265536284601770307261425 4699152213451327730446069)
                  ·
                    refine ⟨440545520011061974729319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4699152213451327730446069 440545520011061974729319)
                    ·
                      rfl

theorem cell23_2573878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2573878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573878 prefixEnd_2573878 := by exact prefixLift 2573878
  have htrace : WordTrace (prefixWord ++ tailWord_2573878) baseStart_2573878 baseEnd_2573878 := by
    simpa [prefixWord, tailWord_2573878, baseEnd_2573878] using wordTrace_append hprefix tailTrace_2573878
  have hstable : (prefixWord ++ tailWord_2573878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573878).length < 2 ^ (prefixWord ++ tailWord_2573878).sum := by decide
  have hdescent : baseEnd_2573878 < baseStart_2573878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573884 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2573884 : Nat := 118140960795 + 2573884 * 2 ^ 59
def prefixEnd_2573884 : Nat := 4983230072969 + 3 ^ 40 * 2573884 * 2
def baseEnd_2573884 : Nat := 1321639640917112900712929

theorem tailTrace_2573884 : CollatzResearch.WordTrace tailWord_2573884 prefixEnd_2573884 1321639640917112900712929 := by
  unfold tailWord_2573884
  simp only [CollatzResearch.WordTrace]
  refine ⟨46938630903632663617604353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62584841204843551490139137 46938630903632663617604353)
  ·
    refine ⟨35203973177724497713203265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46938630903632663617604353 35203973177724497713203265)
    ·
      refine ⟨26402979883293373284902449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35203973177724497713203265 26402979883293373284902449)
      ·
        refine ⟨19802234912470029963676837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26402979883293373284902449 19802234912470029963676837)
        ·
          refine ⟨3712919046088130618189407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19802234912470029963676837 3712919046088130618189407)
          ·
            refine ⟨5569378569132195927284111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712919046088130618189407 5569378569132195927284111)
            ·
              refine ⟨8354067853698293890926167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569378569132195927284111 8354067853698293890926167)
              ·
                refine ⟨12531101780547440836389251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354067853698293890926167 12531101780547440836389251)
                ·
                  refine ⟨18796652670821161254583877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12531101780547440836389251 18796652670821161254583877)
                  ·
                    refine ⟨3524372375778967735234477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18796652670821161254583877 3524372375778967735234477)
                    ·
                      refine ⟨1321639640917112900712929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3524372375778967735234477 1321639640917112900712929)
                      ·
                        rfl

theorem cell23_2573884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2573884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573884 prefixEnd_2573884 := by exact prefixLift 2573884
  have htrace : WordTrace (prefixWord ++ tailWord_2573884) baseStart_2573884 baseEnd_2573884 := by
    simpa [prefixWord, tailWord_2573884, baseEnd_2573884] using wordTrace_append hprefix tailTrace_2573884
  have hstable : (prefixWord ++ tailWord_2573884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573884).length < 2 ^ (prefixWord ++ tailWord_2573884).sum := by decide
  have hdescent : baseEnd_2573884 < baseStart_2573884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 9, 2]
def baseStart_2573907 : Nat := 118140960795 + 2573907 * 2 ^ 59
def prefixEnd_2573907 : Nat := 4983230072969 + 3 ^ 40 * 2573907 * 2
def baseEnd_2573907 : Nat := 1321651450972166310725323

theorem tailTrace_2573907 : CollatzResearch.WordTrace tailWord_2573907 prefixEnd_2573907 1321651450972166310725323 := by
  unfold tailWord_2573907
  simp only [CollatzResearch.WordTrace]
  refine ⟨93878100686182002163295975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62585400457454668108863983 93878100686182002163295975)
  ·
    refine ⟨140817151029273003244943963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93878100686182002163295975 140817151029273003244943963)
    ·
      refine ⟨211225726543909504867415945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140817151029273003244943963 211225726543909504867415945)
      ·
        refine ⟨158419294907932128650561959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211225726543909504867415945 158419294907932128650561959)
        ·
          refine ⟨237628942361898192975842939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158419294907932128650561959 237628942361898192975842939)
          ·
            refine ⟨356443413542847289463764409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237628942361898192975842939 356443413542847289463764409)
            ·
              refine ⟨267332560157135467097823307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356443413542847289463764409 267332560157135467097823307)
              ·
                refine ⟨400998840235703200646734961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267332560157135467097823307 400998840235703200646734961)
                ·
                  refine ⟨300749130176777400485051221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400998840235703200646734961 300749130176777400485051221)
                  ·
                    refine ⟨1762201934629555080967097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 300749130176777400485051221 1762201934629555080967097)
                    ·
                      refine ⟨1321651450972166310725323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762201934629555080967097 1321651450972166310725323)
                      ·
                        rfl

theorem cell23_2573907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9, 2].length) (baseStart_2573907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573907 prefixEnd_2573907 := by exact prefixLift 2573907
  have htrace : WordTrace (prefixWord ++ tailWord_2573907) baseStart_2573907 baseEnd_2573907 := by
    simpa [prefixWord, tailWord_2573907, baseEnd_2573907] using wordTrace_append hprefix tailTrace_2573907
  have hstable : (prefixWord ++ tailWord_2573907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573907).length < 2 ^ (prefixWord ++ tailWord_2573907).sum := by decide
  have hdescent : baseEnd_2573907 < baseStart_2573907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573924 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_2573924 : Nat := 118140960795 + 2573924 * 2 ^ 59
def prefixEnd_2573924 : Nat := 4983230072969 + 3 ^ 40 * 2573924 * 2
def baseEnd_2573924 : Nat := 1321660180143292744212745

theorem tailTrace_2573924 : CollatzResearch.WordTrace tailWord_2573924 prefixEnd_2573924 1321660180143292744212745 := by
  unfold tailWord_2573924
  simp only [CollatzResearch.WordTrace]
  refine ⟨46939360363560207033332413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62585813818080276044443217 46939360363560207033332413)
  ·
    refine ⟨17602260136335077637499655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46939360363560207033332413 17602260136335077637499655)
    ·
      refine ⟨26403390204502616456249483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17602260136335077637499655 26403390204502616456249483)
      ·
        refine ⟨39605085306753924684374225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26403390204502616456249483 39605085306753924684374225)
        ·
          refine ⟨29703813980065443513280669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39605085306753924684374225 29703813980065443513280669)
          ·
            refine ⟨11138930242524541317480251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29703813980065443513280669 11138930242524541317480251)
            ·
              refine ⟨16708395363786811976220377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138930242524541317480251 16708395363786811976220377)
              ·
                refine ⟨12531296522840108982165283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16708395363786811976220377 12531296522840108982165283)
                ·
                  refine ⟨18796944784260163473247925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12531296522840108982165283 18796944784260163473247925)
                  ·
                    refine ⟨1762213573524390325616993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18796944784260163473247925 1762213573524390325616993)
                    ·
                      refine ⟨1321660180143292744212745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762213573524390325616993 1321660180143292744212745)
                      ·
                        rfl

theorem cell23_2573924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_2573924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573924 prefixEnd_2573924 := by exact prefixLift 2573924
  have htrace : WordTrace (prefixWord ++ tailWord_2573924) baseStart_2573924 baseEnd_2573924 := by
    simpa [prefixWord, tailWord_2573924, baseEnd_2573924] using wordTrace_append hprefix tailTrace_2573924
  have hstable : (prefixWord ++ tailWord_2573924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573924).length < 2 ^ (prefixWord ++ tailWord_2573924).sum := by decide
  have hdescent : baseEnd_2573924 < baseStart_2573924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573937 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_2573937 : Nat := 118140960795 + 2573937 * 2 ^ 59
def prefixEnd_2573937 : Nat := 4983230072969 + 3 ^ 40 * 2573937 * 2
def baseEnd_2573937 : Nat := 1321666855391801193350185

theorem tailTrace_2573937 : CollatzResearch.WordTrace tailWord_2573937 prefixEnd_2573937 1321666855391801193350185 := by
  unfold tailWord_2573937
  simp only [CollatzResearch.WordTrace]
  refine ⟨93879194876073317286888065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62586129917382211524592043 93879194876073317286888065)
  ·
    refine ⟨70409396157054987965166049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93879194876073317286888065 70409396157054987965166049)
    ·
      refine ⟨52807047117791240973874537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70409396157054987965166049 52807047117791240973874537)
      ·
        refine ⟨39605285338343430730405903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52807047117791240973874537 39605285338343430730405903)
        ·
          refine ⟨59407928007515146095608855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39605285338343430730405903 59407928007515146095608855)
          ·
            refine ⟨89111892011272719143413283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59407928007515146095608855 89111892011272719143413283)
            ·
              refine ⟨133667838016909078715119925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89111892011272719143413283 133667838016909078715119925)
              ·
                refine ⟨12531359814085226129542493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133667838016909078715119925 12531359814085226129542493)
                ·
                  refine ⟨4699259930281959798578435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12531359814085226129542493 4699259930281959798578435)
                  ·
                    refine ⟨7048889895422939697867653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699259930281959798578435 7048889895422939697867653)
                    ·
                      refine ⟨1321666855391801193350185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7048889895422939697867653 1321666855391801193350185)
                      ·
                        rfl

theorem cell23_2573937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_2573937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573937 prefixEnd_2573937 := by exact prefixLift 2573937
  have htrace : WordTrace (prefixWord ++ tailWord_2573937) baseStart_2573937 baseEnd_2573937 := by
    simpa [prefixWord, tailWord_2573937, baseEnd_2573937] using wordTrace_append hprefix tailTrace_2573937
  have hstable : (prefixWord ++ tailWord_2573937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573937).length < 2 ^ (prefixWord ++ tailWord_2573937).sum := by decide
  have hdescent : baseEnd_2573937 < baseStart_2573937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573941 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2573941 : Nat := 118140960795 + 2573941 * 2 ^ 59
def prefixEnd_2573941 : Nat := 4983230072969 + 3 ^ 40 * 2573941 * 2
def baseEnd_2573941 : Nat := 1321668909314419177700167

theorem tailTrace_2573941 : CollatzResearch.WordTrace tailWord_2573941 prefixEnd_2573941 1321668909314419177700167 := by
  unfold tailWord_2573941
  simp only [CollatzResearch.WordTrace]
  refine ⟨93879340768058825970033677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62586227178705883980022451 93879340768058825970033677)
  ·
    refine ⟨35204752788022059738762629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93879340768058825970033677 35204752788022059738762629)
    ·
      refine ⟨6600891147754136201017993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35204752788022059738762629 6600891147754136201017993)
      ·
        refine ⟨4950668360815602150763495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6600891147754136201017993 4950668360815602150763495)
        ·
          refine ⟨7426002541223403226145243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950668360815602150763495 7426002541223403226145243)
          ·
            refine ⟨11139003811835104839217865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426002541223403226145243 11139003811835104839217865)
            ·
              refine ⟨8354252858876328629413399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11139003811835104839217865 8354252858876328629413399)
              ·
                refine ⟨12531379288314492944120099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354252858876328629413399 12531379288314492944120099)
                ·
                  refine ⟨18797068932471739416180149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12531379288314492944120099 18797068932471739416180149)
                  ·
                    refine ⟨1762225212419225570266889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18797068932471739416180149 1762225212419225570266889)
                    ·
                      refine ⟨1321668909314419177700167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762225212419225570266889 1321668909314419177700167)
                      ·
                        rfl

theorem cell23_2573941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2573941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573941 prefixEnd_2573941 := by exact prefixLift 2573941
  have htrace : WordTrace (prefixWord ++ tailWord_2573941) baseStart_2573941 baseEnd_2573941 := by
    simpa [prefixWord, tailWord_2573941, baseEnd_2573941] using wordTrace_append hprefix tailTrace_2573941
  have hstable : (prefixWord ++ tailWord_2573941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573941).length < 2 ^ (prefixWord ++ tailWord_2573941).sum := by decide
  have hdescent : baseEnd_2573941 < baseStart_2573941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573947 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 6, 4]
def baseStart_2573947 : Nat := 118140960795 + 2573947 * 2 ^ 59
def prefixEnd_2573947 : Nat := 4983230072969 + 3 ^ 40 * 2573947 * 2
def baseEnd_2573947 : Nat := 440557330066115384741713

theorem tailTrace_2573947 : CollatzResearch.WordTrace tailWord_2573947 prefixEnd_2573947 440557330066115384741713 := by
  unfold tailWord_2573947
  simp only [CollatzResearch.WordTrace]
  refine ⟨93879559606037088994752095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62586373070691392663168063 93879559606037088994752095)
  ·
    refine ⟨140819339409055633492128143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93879559606037088994752095 140819339409055633492128143)
    ·
      refine ⟨211229009113583450238192215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140819339409055633492128143 211229009113583450238192215)
      ·
        refine ⟨316843513670375175357288323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211229009113583450238192215 316843513670375175357288323)
        ·
          refine ⟨475265270505562763035932485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316843513670375175357288323 475265270505562763035932485)
          ·
            refine ⟨89112238219793018069237341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475265270505562763035932485 89112238219793018069237341)
            ·
              refine ⟨33417089332422381775964003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89112238219793018069237341 33417089332422381775964003)
              ·
                refine ⟨50125633998633572663946005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33417089332422381775964003 50125633998633572663946005)
                ·
                  refine ⟨2349639093685948718622469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50125633998633572663946005 2349639093685948718622469)
                  ·
                    refine ⟨440557330066115384741713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349639093685948718622469 440557330066115384741713)
                    ·
                      rfl

theorem cell23_2573947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 4].length) (baseStart_2573947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573947 prefixEnd_2573947 := by exact prefixLift 2573947
  have htrace : WordTrace (prefixWord ++ tailWord_2573947) baseStart_2573947 baseEnd_2573947 := by
    simpa [prefixWord, tailWord_2573947, baseEnd_2573947] using wordTrace_append hprefix tailTrace_2573947
  have hstable : (prefixWord ++ tailWord_2573947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573947).length < 2 ^ (prefixWord ++ tailWord_2573947).sum := by decide
  have hdescent : baseEnd_2573947 < baseStart_2573947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573964 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_2573964 : Nat := 118140960795 + 2573964 * 2 ^ 59
def prefixEnd_2573964 : Nat := 4983230072969 + 3 ^ 40 * 2573964 * 2
def baseEnd_2573964 : Nat := 440560239789824195904187

theorem tailTrace_2573964 : CollatzResearch.WordTrace tailWord_2573964 prefixEnd_2573964 440560239789824195904187 := by
  unfold tailWord_2573964
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940089823487750449060473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62586786431317000598747297 46940089823487750449060473)
  ·
    refine ⟨35205067367615812836795355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46940089823487750449060473 35205067367615812836795355)
    ·
      refine ⟨52807601051423719255193033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35205067367615812836795355 52807601051423719255193033)
      ·
        refine ⟨39605700788567789441394775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52807601051423719255193033 39605700788567789441394775)
        ·
          refine ⟨59408551182851684162092163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39605700788567789441394775 59408551182851684162092163)
          ·
            refine ⟨89112826774277526243138245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59408551182851684162092163 89112826774277526243138245)
            ·
              refine ⟨16708655020177036170588421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89112826774277526243138245 16708655020177036170588421)
              ·
                refine ⟨3132872816283194281985329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16708655020177036170588421 3132872816283194281985329)
                ·
                  refine ⟨2349654612212395711488997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132872816283194281985329 2349654612212395711488997)
                  ·
                    refine ⟨440560239789824195904187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349654612212395711488997 440560239789824195904187)
                    ·
                      rfl

theorem cell23_2573964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_2573964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573964 prefixEnd_2573964 := by exact prefixLift 2573964
  have htrace : WordTrace (prefixWord ++ tailWord_2573964) baseStart_2573964 baseEnd_2573964 := by
    simpa [prefixWord, tailWord_2573964, baseEnd_2573964] using wordTrace_append hprefix tailTrace_2573964
  have hstable : (prefixWord ++ tailWord_2573964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573964).length < 2 ^ (prefixWord ++ tailWord_2573964).sum := by decide
  have hdescent : baseEnd_2573964 < baseStart_2573964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573992 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2573992 : Nat := 118140960795 + 2573992 * 2 ^ 59
def prefixEnd_2573992 : Nat := 4983230072969 + 3 ^ 40 * 2573992 * 2
def baseEnd_2573992 : Nat := 1321695096827798478162433

theorem tailTrace_2573992 : CollatzResearch.WordTrace tailWord_2573992 prefixEnd_2573992 1321695096827798478162433 := by
  unfold tailWord_2573992
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940600445437030840070115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62587467260582707786760153 46940600445437030840070115)
  ·
    refine ⟨70410900668155546260105173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46940600445437030840070115 70410900668155546260105173)
    ·
      refine ⟨1650255484409895615471215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70410900668155546260105173 1650255484409895615471215)
      ·
        refine ⟨2475383226614843423206823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650255484409895615471215 2475383226614843423206823)
        ·
          refine ⟨3713074839922265134810235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475383226614843423206823 3713074839922265134810235)
          ·
            refine ⟨5569612259883397702215353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713074839922265134810235 5569612259883397702215353)
            ·
              refine ⟨4177209194912548276661515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569612259883397702215353 4177209194912548276661515)
              ·
                refine ⟨6265813792368822414992273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177209194912548276661515 6265813792368822414992273)
                ·
                  refine ⟨4699360344276616811244205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265813792368822414992273 4699360344276616811244205)
                  ·
                    refine ⟨1762260129103731304216577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4699360344276616811244205 1762260129103731304216577)
                    ·
                      refine ⟨1321695096827798478162433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762260129103731304216577 1321695096827798478162433)
                      ·
                        rfl

theorem cell23_2573992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2573992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2573992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2573992 prefixEnd_2573992 := by exact prefixLift 2573992
  have htrace : WordTrace (prefixWord ++ tailWord_2573992) baseStart_2573992 baseEnd_2573992 := by
    simpa [prefixWord, tailWord_2573992, baseEnd_2573992] using wordTrace_append hprefix tailTrace_2573992
  have hstable : (prefixWord ++ tailWord_2573992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573992).length < 2 ^ (prefixWord ++ tailWord_2573992).sum := by decide
  have hdescent : baseEnd_2573992 < baseStart_2573992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574057 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_2574057 : Nat := 118140960795 + 2574057 * 2 ^ 59
def prefixEnd_2574057 : Nat := 4983230072969 + 3 ^ 40 * 2574057 * 2
def baseEnd_2574057 : Nat := 1321728473070340723849633

theorem tailTrace_2574057 : CollatzResearch.WordTrace tailWord_2574057 prefixEnd_2574057 1321728473070340723849633 := by
  unfold tailWord_2574057
  simp only [CollatzResearch.WordTrace]
  refine ⟨93883571635638577781256425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62589047757092385187504283 93883571635638577781256425)
  ·
    refine ⟨70412678726728933335942319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93883571635638577781256425 70412678726728933335942319)
    ·
      refine ⟨105619018090093400003913479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70412678726728933335942319 105619018090093400003913479)
      ·
        refine ⟨158428527135140100005870219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105619018090093400003913479 158428527135140100005870219)
        ·
          refine ⟨237642790702710150008805329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158428527135140100005870219 237642790702710150008805329)
          ·
            refine ⟨178232093027032612506603997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237642790702710150008805329 178232093027032612506603997)
            ·
              refine ⟨66837034885137229689976499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178232093027032612506603997 66837034885137229689976499)
              ·
                refine ⟨100255552327705844534964749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66837034885137229689976499 100255552327705844534964749)
                ·
                  refine ⟨37595832122889691700611781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100255552327705844534964749 37595832122889691700611781)
                  ·
                    refine ⟨7049218523041817193864709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37595832122889691700611781 7049218523041817193864709)
                    ·
                      refine ⟨1321728473070340723849633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7049218523041817193864709 1321728473070340723849633)
                      ·
                        rfl

theorem cell23_2574057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_2574057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574057 prefixEnd_2574057 := by exact prefixLift 2574057
  have htrace : WordTrace (prefixWord ++ tailWord_2574057) baseStart_2574057 baseEnd_2574057 := by
    simpa [prefixWord, tailWord_2574057, baseEnd_2574057] using wordTrace_append hprefix tailTrace_2574057
  have hstable : (prefixWord ++ tailWord_2574057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574057).length < 2 ^ (prefixWord ++ tailWord_2574057).sum := by decide
  have hdescent : baseEnd_2574057 < baseStart_2574057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574065 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_2574065 : Nat := 118140960795 + 2574065 * 2 ^ 59
def prefixEnd_2574065 : Nat := 4983230072969 + 3 ^ 40 * 2574065 * 2
def baseEnd_2574065 : Nat := 1321732580915576692549597

theorem tailTrace_2574065 : CollatzResearch.WordTrace tailWord_2574065 prefixEnd_2574065 1321732580915576692549597 := by
  unfold tailWord_2574065
  simp only [CollatzResearch.WordTrace]
  refine ⟨93883863419609595147547649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62589242279739730098365099 93883863419609595147547649)
  ·
    refine ⟨70412897564707196360660737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93883863419609595147547649 70412897564707196360660737)
    ·
      refine ⟨52809673173530397270495553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70412897564707196360660737 52809673173530397270495553)
      ·
        refine ⟨39607254880147797952871665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52809673173530397270495553 39607254880147797952871665)
        ·
          refine ⟨29705441160110848464653749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39607254880147797952871665 29705441160110848464653749)
          ·
            refine ⟨2784885108760392043561289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29705441160110848464653749 2784885108760392043561289)
            ·
              refine ⟨2088663831570294032670967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784885108760392043561289 2088663831570294032670967)
              ·
                refine ⟨3132995747355441049006451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088663831570294032670967 3132995747355441049006451)
                ·
                  refine ⟨4699493621033161573509677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132995747355441049006451 4699493621033161573509677)
                  ·
                    refine ⟨1762310107887435590066129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4699493621033161573509677 1762310107887435590066129)
                    ·
                      refine ⟨1321732580915576692549597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762310107887435590066129 1321732580915576692549597)
                      ·
                        rfl

theorem cell23_2574065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_2574065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574065 prefixEnd_2574065 := by exact prefixLift 2574065
  have htrace : WordTrace (prefixWord ++ tailWord_2574065) baseStart_2574065 baseEnd_2574065 := by
    simpa [prefixWord, tailWord_2574065, baseEnd_2574065] using wordTrace_append hprefix tailTrace_2574065
  have hstable : (prefixWord ++ tailWord_2574065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574065).length < 2 ^ (prefixWord ++ tailWord_2574065).sum := by decide
  have hdescent : baseEnd_2574065 < baseStart_2574065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574077 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2574077 : Nat := 118140960795 + 2574077 * 2 ^ 59
def prefixEnd_2574077 : Nat := 4983230072969 + 3 ^ 40 * 2574077 * 2
def baseEnd_2574077 : Nat := 1321738742683430645599541

theorem tailTrace_2574077 : CollatzResearch.WordTrace tailWord_2574077 prefixEnd_2574077 1321738742683430645599541 := by
  unfold tailWord_2574077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93884301095566121196984485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62589534063710747464656323 93884301095566121196984485)
  ·
    refine ⟨17603306455418647724434591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93884301095566121196984485 17603306455418647724434591)
    ·
      refine ⟨26404959683127971586651887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17603306455418647724434591 26404959683127971586651887)
      ·
        refine ⟨39607439524691957379977831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26404959683127971586651887 39607439524691957379977831)
        ·
          refine ⟨59411159287037936069966747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39607439524691957379977831 59411159287037936069966747)
          ·
            refine ⟨89116738930556904104950121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59411159287037936069966747 89116738930556904104950121)
            ·
              refine ⟨66837554197917678078712591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89116738930556904104950121 66837554197917678078712591)
              ·
                refine ⟨100256331296876517118068887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66837554197917678078712591 100256331296876517118068887)
                ·
                  refine ⟨150384496945314775677103331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100256331296876517118068887 150384496945314775677103331)
                  ·
                    refine ⟨225576745417972163515654997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150384496945314775677103331 225576745417972163515654997)
                    ·
                      refine ⟨1321738742683430645599541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 225576745417972163515654997 1321738742683430645599541)
                      ·
                        rfl

theorem cell23_2574077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2574077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574077 prefixEnd_2574077 := by exact prefixLift 2574077
  have htrace : WordTrace (prefixWord ++ tailWord_2574077) baseStart_2574077 baseEnd_2574077 := by
    simpa [prefixWord, tailWord_2574077, baseEnd_2574077] using wordTrace_append hprefix tailTrace_2574077
  have hstable : (prefixWord ++ tailWord_2574077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574077).length < 2 ^ (prefixWord ++ tailWord_2574077).sum := by decide
  have hdescent : baseEnd_2574077 < baseStart_2574077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574084 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 7]
def baseStart_2574084 : Nat := 118140960795 + 2574084 * 2 ^ 59
def prefixEnd_2574084 : Nat := 4983230072969 + 3 ^ 40 * 2574084 * 2
def baseEnd_2574084 : Nat := 146860259672001346468001

theorem tailTrace_2574084 : CollatzResearch.WordTrace tailWord_2574084 prefixEnd_2574084 146860259672001346468001 := by
  unfold tailWord_2574084
  simp only [CollatzResearch.WordTrace]
  refine ⟨46942278203270380696244653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62589704271027174261659537 46942278203270380696244653)
  ·
    refine ⟨17603354326226392761091745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46942278203270380696244653 17603354326226392761091745)
    ·
      refine ⟨13202515744669794570818809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17603354326226392761091745 13202515744669794570818809)
      ·
        refine ⟨9901886808502345928114107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13202515744669794570818809 9901886808502345928114107)
        ·
          refine ⟨14852830212753518892171161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9901886808502345928114107 14852830212753518892171161)
          ·
            refine ⟨11139622659565139169128371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14852830212753518892171161 11139622659565139169128371)
            ·
              refine ⟨16709433989347708753692557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11139622659565139169128371 16709433989347708753692557)
              ·
                refine ⟨6266037746005390782634709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16709433989347708753692557 6266037746005390782634709)
                ·
                  refine ⟨146860259672001346468001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6266037746005390782634709 146860259672001346468001)
                  ·
                    rfl

theorem cell23_2574084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_2574084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574084 prefixEnd_2574084 := by exact prefixLift 2574084
  have htrace : WordTrace (prefixWord ++ tailWord_2574084) baseStart_2574084 baseEnd_2574084 := by
    simpa [prefixWord, tailWord_2574084, baseEnd_2574084] using wordTrace_append hprefix tailTrace_2574084
  have hstable : (prefixWord ++ tailWord_2574084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574084).length < 2 ^ (prefixWord ++ tailWord_2574084).sum := by decide
  have hdescent : baseEnd_2574084 < baseStart_2574084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574086 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2574086 : Nat := 118140960795 + 2574086 * 2 ^ 59
def prefixEnd_2574086 : Nat := 4983230072969 + 3 ^ 40 * 2574086 * 2
def baseEnd_2574086 : Nat := 1321743364009321110387001

theorem tailTrace_2574086 : CollatzResearch.WordTrace tailWord_2574086 prefixEnd_2574086 1321743364009321110387001 := by
  unfold tailWord_2574086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933894667266672366689441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62589752901689010489374741 2933894667266672366689441)
  ·
    refine ⟨2200421000450004275017081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2933894667266672366689441 2200421000450004275017081)
    ·
      refine ⟨1650315750337503206262811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200421000450004275017081 1650315750337503206262811)
      ·
        refine ⟨2475473625506254809394217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650315750337503206262811 2475473625506254809394217)
        ·
          refine ⟨1856605219129691107045663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475473625506254809394217 1856605219129691107045663)
          ·
            refine ⟨2784907828694536660568495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856605219129691107045663 2784907828694536660568495)
            ·
              refine ⟨4177361743041804990852743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784907828694536660568495 4177361743041804990852743)
              ·
                refine ⟨6266042614562707486279115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177361743041804990852743 6266042614562707486279115)
                ·
                  refine ⟨9399063921844061229418673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266042614562707486279115 9399063921844061229418673)
                  ·
                    refine ⟨7049297941383045922064005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9399063921844061229418673 7049297941383045922064005)
                    ·
                      refine ⟨1321743364009321110387001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7049297941383045922064005 1321743364009321110387001)
                      ·
                        rfl

theorem cell23_2574086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2574086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574086 prefixEnd_2574086 := by exact prefixLift 2574086
  have htrace : WordTrace (prefixWord ++ tailWord_2574086) baseStart_2574086 baseEnd_2574086 := by
    simpa [prefixWord, tailWord_2574086, baseEnd_2574086] using wordTrace_append hprefix tailTrace_2574086
  have hstable : (prefixWord ++ tailWord_2574086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574086).length < 2 ^ (prefixWord ++ tailWord_2574086).sum := by decide
  have hdescent : baseEnd_2574086 < baseStart_2574086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574107 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_2574107 : Nat := 118140960795 + 2574107 * 2 ^ 59
def prefixEnd_2574107 : Nat := 4983230072969 + 3 ^ 40 * 2574107 * 2
def baseEnd_2574107 : Nat := 1321754147103065528224403

theorem tailTrace_2574107 : CollatzResearch.WordTrace tailWord_2574107 prefixEnd_2574107 1321754147103065528224403 := by
  unfold tailWord_2574107
  simp only [CollatzResearch.WordTrace]
  refine ⟨93885395285457436320576575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62590263523638290880384383 93885395285457436320576575)
  ·
    refine ⟨140828092928186154480864863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93885395285457436320576575 140828092928186154480864863)
    ·
      refine ⟨211242139392279231721297295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140828092928186154480864863 211242139392279231721297295)
      ·
        refine ⟨316863209088418847581945943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211242139392279231721297295 316863209088418847581945943)
        ·
          refine ⟨475294813632628271372918915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316863209088418847581945943 475294813632628271372918915)
          ·
            refine ⟨712942220448942407059378373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475294813632628271372918915 712942220448942407059378373)
            ·
              refine ⟨133676666334176701323633445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 712942220448942407059378373 133676666334176701323633445)
              ·
                refine ⟨25064374937658131498181271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133676666334176701323633445 25064374937658131498181271)
                ·
                  refine ⟨37596562406487197247271907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25064374937658131498181271 37596562406487197247271907)
                  ·
                    refine ⟨56394843609730795870907861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37596562406487197247271907 56394843609730795870907861)
                    ·
                      refine ⟨1321754147103065528224403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56394843609730795870907861 1321754147103065528224403)
                      ·
                        rfl

theorem cell23_2574107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_2574107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574107 prefixEnd_2574107 := by exact prefixLift 2574107
  have htrace : WordTrace (prefixWord ++ tailWord_2574107) baseStart_2574107 baseEnd_2574107 := by
    simpa [prefixWord, tailWord_2574107, baseEnd_2574107] using wordTrace_append hprefix tailTrace_2574107
  have hstable : (prefixWord ++ tailWord_2574107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574107).length < 2 ^ (prefixWord ++ tailWord_2574107).sum := by decide
  have hdescent : baseEnd_2574107 < baseStart_2574107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574114 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2574114 : Nat := 118140960795 + 2574114 * 2 ^ 59
def prefixEnd_2574114 : Nat := 4983230072969 + 3 ^ 40 * 2574114 * 2
def baseEnd_2574114 : Nat := 440585913822549000278957

theorem tailTrace_2574114 : CollatzResearch.WordTrace tailWord_2574114 prefixEnd_2574114 440585913822549000278957 := by
  unfold tailWord_2574114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23471412649108019129020349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62590433730954717677387597 23471412649108019129020349)
  ·
    refine ⟨8801779743415507173382631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23471412649108019129020349 8801779743415507173382631)
    ·
      refine ⟨13202669615123260760073947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8801779743415507173382631 13202669615123260760073947)
      ·
        refine ⟨19804004422684891140110921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13202669615123260760073947 19804004422684891140110921)
        ·
          refine ⟨14853003317013668355083191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19804004422684891140110921 14853003317013668355083191)
          ·
            refine ⟨22279504975520502532624787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14853003317013668355083191 22279504975520502532624787)
            ·
              refine ⟨33419257463280753798937181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22279504975520502532624787 33419257463280753798937181)
              ·
                refine ⟨12532221548730282674601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33419257463280753798937181 12532221548730282674601443)
                ·
                  refine ⟨18798332323095424011902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12532221548730282674601443 18798332323095424011902165)
                  ·
                    refine ⟨440585913822549000278957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18798332323095424011902165 440585913822549000278957)
                    ·
                      rfl

theorem cell23_2574114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2574114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574114 prefixEnd_2574114 := by exact prefixLift 2574114
  have htrace : WordTrace (prefixWord ++ tailWord_2574114) baseStart_2574114 baseEnd_2574114 := by
    simpa [prefixWord, tailWord_2574114, baseEnd_2574114] using wordTrace_append hprefix tailTrace_2574114
  have hstable : (prefixWord ++ tailWord_2574114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574114).length < 2 ^ (prefixWord ++ tailWord_2574114).sum := by decide
  have hdescent : baseEnd_2574114 < baseStart_2574114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574127 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 10]
def baseStart_2574127 : Nat := 118140960795 + 2574127 * 2 ^ 59
def prefixEnd_2574127 : Nat := 4983230072969 + 3 ^ 40 * 2574127 * 2
def baseEnd_2574127 : Nat := 440588138905385149991437

theorem tailTrace_2574127 : CollatzResearch.WordTrace tailWord_2574127 prefixEnd_2574127 440588138905385149991437 := by
  unfold tailWord_2574127
  simp only [CollatzResearch.WordTrace]
  refine ⟨93886124745384979736304635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62590749830256653157536423 93886124745384979736304635)
  ·
    refine ⟨140829187118077469604456953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93886124745384979736304635 140829187118077469604456953)
    ·
      refine ⟨105621890338558102203342715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140829187118077469604456953 105621890338558102203342715)
      ·
        refine ⟨158432835507837153305014073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105621890338558102203342715 158432835507837153305014073)
        ·
          refine ⟨118824626630877864978760555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158432835507837153305014073 118824626630877864978760555)
          ·
            refine ⟨178236939946316797468140833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118824626630877864978760555 178236939946316797468140833)
            ·
              refine ⟨133677704959737598101105625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178236939946316797468140833 133677704959737598101105625)
              ·
                refine ⟨100258278719803198575829219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133677704959737598101105625 100258278719803198575829219)
                ·
                  refine ⟨150387418079704797863743829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100258278719803198575829219 150387418079704797863743829)
                  ·
                    refine ⟨440588138905385149991437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 150387418079704797863743829 440588138905385149991437)
                    ·
                      rfl

theorem cell23_2574127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_2574127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574127 prefixEnd_2574127 := by exact prefixLift 2574127
  have htrace : WordTrace (prefixWord ++ tailWord_2574127) baseStart_2574127 baseEnd_2574127 := by
    simpa [prefixWord, tailWord_2574127, baseEnd_2574127] using wordTrace_append hprefix tailTrace_2574127
  have hstable : (prefixWord ++ tailWord_2574127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574127).length < 2 ^ (prefixWord ++ tailWord_2574127).sum := by decide
  have hdescent : baseEnd_2574127 < baseStart_2574127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574131 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 2, 5]
def baseStart_2574131 : Nat := 118140960795 + 2574131 * 2 ^ 59
def prefixEnd_2574131 : Nat := 4983230072969 + 3 ^ 40 * 2574131 * 2
def baseEnd_2574131 : Nat := 440588823546257811441431

theorem tailTrace_2574131 : CollatzResearch.WordTrace tailWord_2574131 prefixEnd_2574131 440588823546257811441431 := by
  unfold tailWord_2574131
  simp only [CollatzResearch.WordTrace]
  refine ⟨93886270637370488419450247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62590847091580325612966831 93886270637370488419450247)
  ·
    refine ⟨140829405956055732629175371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93886270637370488419450247 140829405956055732629175371)
    ·
      refine ⟨211244108934083598943763057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140829405956055732629175371 211244108934083598943763057)
      ·
        refine ⟨158433081700562699207822293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211244108934083598943763057 158433081700562699207822293)
        ·
          refine ⟨3713275352356938262683335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 158433081700562699207822293 3713275352356938262683335)
          ·
            refine ⟨5569913028535407394025003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713275352356938262683335 5569913028535407394025003)
            ·
              refine ⟨8354869542803111091037505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569913028535407394025003 8354869542803111091037505)
              ·
                refine ⟨6266152157102333318278129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354869542803111091037505 6266152157102333318278129)
                ·
                  refine ⟨4699614117826749988708597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266152157102333318278129 4699614117826749988708597)
                  ·
                    refine ⟨440588823546257811441431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4699614117826749988708597 440588823546257811441431)
                    ·
                      rfl

theorem cell23_2574131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].length) (baseStart_2574131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574131 prefixEnd_2574131 := by exact prefixLift 2574131
  have htrace : WordTrace (prefixWord ++ tailWord_2574131) baseStart_2574131 baseEnd_2574131 := by
    simpa [prefixWord, tailWord_2574131, baseEnd_2574131] using wordTrace_append hprefix tailTrace_2574131
  have hstable : (prefixWord ++ tailWord_2574131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574131).length < 2 ^ (prefixWord ++ tailWord_2574131).sum := by decide
  have hdescent : baseEnd_2574131 < baseStart_2574131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574141 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2574141 : Nat := 118140960795 + 2574141 * 2 ^ 59
def prefixEnd_2574141 : Nat := 4983230072969 + 3 ^ 40 * 2574141 * 2
def baseEnd_2574141 : Nat := 1321771605445318395199247

theorem tailTrace_2574141 : CollatzResearch.WordTrace tailWord_2574141 prefixEnd_2574141 1321771605445318395199247 := by
  unfold tailWord_2574141
  simp only [CollatzResearch.WordTrace]
  refine ⟨93886635367334260127314277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62591090244889506751542851 93886635367334260127314277)
  ·
    refine ⟨17603744131375173773871427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93886635367334260127314277 17603744131375173773871427)
    ·
      refine ⟨26405616197062760660807141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17603744131375173773871427 26405616197062760660807141)
      ·
        refine ⟨4951053036949267623901339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26405616197062760660807141 4951053036949267623901339)
        ·
          refine ⟨7426579555423901435852009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951053036949267623901339 7426579555423901435852009)
          ·
            refine ⟨5569934666567926076889007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7426579555423901435852009 5569934666567926076889007)
            ·
              refine ⟨8354901999851889115333511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569934666567926076889007 8354901999851889115333511)
              ·
                refine ⟨12532352999777833673000267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354901999851889115333511 12532352999777833673000267)
                ·
                  refine ⟨18798529499666750509500401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12532352999777833673000267 18798529499666750509500401)
                  ·
                    refine ⟨14098897124750062882125301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18798529499666750509500401 14098897124750062882125301)
                    ·
                      refine ⟨1321771605445318395199247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14098897124750062882125301 1321771605445318395199247)
                      ·
                        rfl

theorem cell23_2574141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2574141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574141 prefixEnd_2574141 := by exact prefixLift 2574141
  have htrace : WordTrace (prefixWord ++ tailWord_2574141) baseStart_2574141 baseEnd_2574141 := by
    simpa [prefixWord, tailWord_2574141, baseEnd_2574141] using wordTrace_append hprefix tailTrace_2574141
  have hstable : (prefixWord ++ tailWord_2574141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574141).length < 2 ^ (prefixWord ++ tailWord_2574141).sum := by decide
  have hdescent : baseEnd_2574141 < baseStart_2574141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574151 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_2574151 : Nat := 118140960795 + 2574151 * 2 ^ 59
def prefixEnd_2574151 : Nat := 4983230072969 + 3 ^ 40 * 2574151 * 2
def baseEnd_2574151 : Nat := 1321776740251863356074201

theorem tailTrace_2574151 : CollatzResearch.WordTrace tailWord_2574151 prefixEnd_2574151 1321776740251863356074201 := by
  unfold tailWord_2574151
  simp only [CollatzResearch.WordTrace]
  refine ⟨93887000097298031835178307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62591333398198687890118871 93887000097298031835178307)
  ·
    refine ⟨140830500145947047752767461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93887000097298031835178307 140830500145947047752767461)
    ·
      refine ⟨26405718777365071453643899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140830500145947047752767461 26405718777365071453643899)
      ·
        refine ⟨39608578166047607180465849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26405718777365071453643899 39608578166047607180465849)
        ·
          refine ⟨29706433624535705385349387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39608578166047607180465849 29706433624535705385349387)
          ·
            refine ⟨44559650436803558078024081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29706433624535705385349387 44559650436803558078024081)
            ·
              refine ⟨33419737827602668558518061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44559650436803558078024081 33419737827602668558518061)
              ·
                refine ⟨12532401685351000709444273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33419737827602668558518061 12532401685351000709444273)
                ·
                  refine ⟨9399301264013250532083205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12532401685351000709444273 9399301264013250532083205)
                  ·
                    refine ⟨1762368987002484474765601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9399301264013250532083205 1762368987002484474765601)
                    ·
                      refine ⟨1321776740251863356074201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762368987002484474765601 1321776740251863356074201)
                      ·
                        rfl

theorem cell23_2574151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_2574151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574151 prefixEnd_2574151 := by exact prefixLift 2574151
  have htrace : WordTrace (prefixWord ++ tailWord_2574151) baseStart_2574151 baseEnd_2574151 := by
    simpa [prefixWord, tailWord_2574151, baseEnd_2574151] using wordTrace_append hprefix tailTrace_2574151
  have hstable : (prefixWord ++ tailWord_2574151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574151).length < 2 ^ (prefixWord ++ tailWord_2574151).sum := by decide
  have hdescent : baseEnd_2574151 < baseStart_2574151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574194 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2574194 : Nat := 118140960795 + 2574194 * 2 ^ 59
def prefixEnd_2574194 : Nat := 4983230072969 + 3 ^ 40 * 2574194 * 2
def baseEnd_2574194 : Nat := 1321798819920006687836503

theorem tailTrace_2574194 : CollatzResearch.WordTrace tailWord_2574194 prefixEnd_2574194 1321798819920006687836503 := by
  unfold tailWord_2574194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472142109035562544748409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62592378957428166785995757 23472142109035562544748409)
  ·
    refine ⟨17604106581776671908561307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23472142109035562544748409 17604106581776671908561307)
    ·
      refine ⟨26406159872665007862841961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17604106581776671908561307 26406159872665007862841961)
      ·
        refine ⟨19804619904498755897131471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26406159872665007862841961 19804619904498755897131471)
        ·
          refine ⟨29706929856748133845697207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19804619904498755897131471 29706929856748133845697207)
          ·
            refine ⟨44560394785122200768545811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29706929856748133845697207 44560394785122200768545811)
            ·
              refine ⟨66840592177683301152818717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44560394785122200768545811 66840592177683301152818717)
              ·
                refine ⟨25065222066631237932307019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66840592177683301152818717 25065222066631237932307019)
                ·
                  refine ⟨37597833099946856898460529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25065222066631237932307019 37597833099946856898460529)
                  ·
                    refine ⟨28198374824960142673845397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37597833099946856898460529 28198374824960142673845397)
                    ·
                      refine ⟨1321798819920006687836503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28198374824960142673845397 1321798819920006687836503)
                      ·
                        rfl

theorem cell23_2574194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2574194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574194 prefixEnd_2574194 := by exact prefixLift 2574194
  have htrace : WordTrace (prefixWord ++ tailWord_2574194) baseStart_2574194 baseEnd_2574194 := by
    simpa [prefixWord, tailWord_2574194, baseEnd_2574194] using wordTrace_append hprefix tailTrace_2574194
  have hstable : (prefixWord ++ tailWord_2574194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574194).length < 2 ^ (prefixWord ++ tailWord_2574194).sum := by decide
  have hdescent : baseEnd_2574194 < baseStart_2574194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574222 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2574222 : Nat := 118140960795 + 2574222 * 2 ^ 59
def prefixEnd_2574222 : Nat := 4983230072969 + 3 ^ 40 * 2574222 * 2
def baseEnd_2574222 : Nat := 1321813197378332578286375

theorem tailTrace_2574222 : CollatzResearch.WordTrace tailWord_2574222 prefixEnd_2574222 1321813197378332578286375 := by
  unfold tailWord_2574222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736198710005101370126615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62593059786693873974008613 11736198710005101370126615)
  ·
    refine ⟨17604298065007652055189923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11736198710005101370126615 17604298065007652055189923)
    ·
      refine ⟨26406447097511478082784885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17604298065007652055189923 26406447097511478082784885)
      ·
        refine ⟨2475604415391701070261083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26406447097511478082784885 2475604415391701070261083)
        ·
          refine ⟨3713406623087551605391625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475604415391701070261083 3713406623087551605391625)
          ·
            refine ⟨2785054967315663704043719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713406623087551605391625 2785054967315663704043719)
            ·
              refine ⟨4177582450973495556065579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785054967315663704043719 4177582450973495556065579)
              ·
                refine ⟨6266373676460243334098369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177582450973495556065579 6266373676460243334098369)
                ·
                  refine ⟨4699780257345182500573777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266373676460243334098369 4699780257345182500573777)
                  ·
                    refine ⟨3524835193008886875430333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699780257345182500573777 3524835193008886875430333)
                    ·
                      refine ⟨1321813197378332578286375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3524835193008886875430333 1321813197378332578286375)
                      ·
                        rfl

theorem cell23_2574222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2574222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574222 prefixEnd_2574222 := by exact prefixLift 2574222
  have htrace : WordTrace (prefixWord ++ tailWord_2574222) baseStart_2574222 baseEnd_2574222 := by
    simpa [prefixWord, tailWord_2574222, baseEnd_2574222] using wordTrace_append hprefix tailTrace_2574222
  have hstable : (prefixWord ++ tailWord_2574222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574222).length < 2 ^ (prefixWord ++ tailWord_2574222).sum := by decide
  have hdescent : baseEnd_2574222 < baseStart_2574222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574261 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2574261 : Nat := 118140960795 + 2574261 * 2 ^ 59
def prefixEnd_2574261 : Nat := 4983230072969 + 3 ^ 40 * 2574261 * 2
def baseEnd_2574261 : Nat := 1321833223123857925698695

theorem tailTrace_2574261 : CollatzResearch.WordTrace tailWord_2574261 prefixEnd_2574261 1321833223123857925698695 := by
  unfold tailWord_2574261
  simp only [CollatzResearch.WordTrace]
  refine ⟨93891012126899520621682637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62594008084599680414455091 93891012126899520621682637)
  ·
    refine ⟨35209129547587320233130989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93891012126899520621682637 35209129547587320233130989)
    ·
      refine ⟨13203423580345245087424121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35209129547587320233130989 13203423580345245087424121)
      ·
        refine ⟨9902567685258933815568091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13203423580345245087424121 9902567685258933815568091)
        ·
          refine ⟨14853851527888400723352137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9902567685258933815568091 14853851527888400723352137)
          ·
            refine ⟨11140388645916300542514103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14853851527888400723352137 11140388645916300542514103)
            ·
              refine ⟨16710582968874450813771155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140388645916300542514103 16710582968874450813771155)
              ·
                refine ⟨25065874453311676220656733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16710582968874450813771155 25065874453311676220656733)
                ·
                  refine ⟨9399702919991878582746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25065874453311676220656733 9399702919991878582746275)
                  ·
                    refine ⟨14099554379987817874119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9399702919991878582746275 14099554379987817874119413)
                    ·
                      refine ⟨1321833223123857925698695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14099554379987817874119413 1321833223123857925698695)
                      ·
                        rfl

theorem cell23_2574261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2574261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574261 prefixEnd_2574261 := by exact prefixLift 2574261
  have htrace : WordTrace (prefixWord ++ tailWord_2574261) baseStart_2574261 baseEnd_2574261 := by
    simpa [prefixWord, tailWord_2574261, baseEnd_2574261] using wordTrace_append hprefix tailTrace_2574261
  have hstable : (prefixWord ++ tailWord_2574261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574261).length < 2 ^ (prefixWord ++ tailWord_2574261).sum := by decide
  have hdescent : baseEnd_2574261 < baseStart_2574261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574264 : List Nat := [2, 1, 2, 1, 2, 3, 2, 10]
def baseStart_2574264 : Nat := 118140960795 + 2574264 * 2 ^ 59
def prefixEnd_2574264 : Nat := 4983230072969 + 3 ^ 40 * 2574264 * 2
def baseEnd_2574264 : Nat := 48956843095030422739303

theorem tailTrace_2574264 : CollatzResearch.WordTrace tailWord_2574264 prefixEnd_2574264 48956843095030422739303 := by
  unfold tailWord_2574264
  simp only [CollatzResearch.WordTrace]
  refine ⟨46945560772944326067020923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62594081030592434756027897 46945560772944326067020923)
  ·
    refine ⟨70418341159416489100531385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46945560772944326067020923 70418341159416489100531385)
    ·
      refine ⟨52813755869562366825398539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70418341159416489100531385 52813755869562366825398539)
      ·
        refine ⟨79220633804343550238097809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52813755869562366825398539 79220633804343550238097809)
        ·
          refine ⟨59415475353257662678573357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79220633804343550238097809 59415475353257662678573357)
          ·
            refine ⟨22280803257471623504465009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59415475353257662678573357 22280803257471623504465009)
            ·
              refine ⟨16710602443103717628348757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22280803257471623504465009 16710602443103717628348757)
              ·
                refine ⟨48956843095030422739303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16710602443103717628348757 48956843095030422739303)
                ·
                  rfl

theorem cell23_2574264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 10].length) (baseStart_2574264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574264 prefixEnd_2574264 := by exact prefixLift 2574264
  have htrace : WordTrace (prefixWord ++ tailWord_2574264) baseStart_2574264 baseEnd_2574264 := by
    simpa [prefixWord, tailWord_2574264, baseEnd_2574264] using wordTrace_append hprefix tailTrace_2574264
  have hstable : (prefixWord ++ tailWord_2574264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574264).length < 2 ^ (prefixWord ++ tailWord_2574264).sum := by decide
  have hdescent : baseEnd_2574264 < baseStart_2574264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574298 : List Nat := [3, 1, 1, 2, 6, 1, 9]
def baseStart_2574298 : Nat := 118140960795 + 2574298 * 2 ^ 59
def prefixEnd_2574298 : Nat := 4983230072969 + 3 ^ 40 * 2574298 * 2
def baseEnd_2574298 : Nat := 16319163233433015814025

theorem tailTrace_2574298 : CollatzResearch.WordTrace tailWord_2574298 prefixEnd_2574298 16319163233433015814025 := by
  unfold tailWord_2574298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23473090406941368985194887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62594907751843650627186365 23473090406941368985194887)
  ·
    refine ⟨35209635610412053477792331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23473090406941368985194887 35209635610412053477792331)
    ·
      refine ⟨52814453415618080216688497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35209635610412053477792331 52814453415618080216688497)
      ·
        refine ⟨39610840061713560162516373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52814453415618080216688497 39610840061713560162516373)
        ·
          refine ⟨1856758127892823132617955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39610840061713560162516373 1856758127892823132617955)
          ·
            refine ⟨2785137191839234698926933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856758127892823132617955 2785137191839234698926933)
            ·
              refine ⟨16319163233433015814025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2785137191839234698926933 16319163233433015814025)
              ·
                rfl

theorem cell23_2574298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 9].length) (baseStart_2574298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574298 prefixEnd_2574298 := by exact prefixLift 2574298
  have htrace : WordTrace (prefixWord ++ tailWord_2574298) baseStart_2574298 baseEnd_2574298 := by
    simpa [prefixWord, tailWord_2574298, baseEnd_2574298] using wordTrace_append hprefix tailTrace_2574298
  have hstable : (prefixWord ++ tailWord_2574298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574298).length < 2 ^ (prefixWord ++ tailWord_2574298).sum := by decide
  have hdescent : baseEnd_2574298 < baseStart_2574298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574308 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_2574308 : Nat := 118140960795 + 2574308 * 2 ^ 59
def prefixEnd_2574308 : Nat := 4983230072969 + 3 ^ 40 * 2574308 * 2
def baseEnd_2574308 : Nat := 1321857356714619241810979

theorem tailTrace_2574308 : CollatzResearch.WordTrace tailWord_2574308 prefixEnd_2574308 1321857356714619241810979 := by
  unfold tailWord_2574308
  simp only [CollatzResearch.WordTrace]
  refine ⟨46946363178864623824321789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62595150905152831765762385 46946363178864623824321789)
  ·
    refine ⟨17604886192074233934120671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46946363178864623824321789 17604886192074233934120671)
    ·
      refine ⟨26407329288111350901181007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17604886192074233934120671 26407329288111350901181007)
      ·
        refine ⟨39610993932167026351771511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26407329288111350901181007 39610993932167026351771511)
        ·
          refine ⟨59416490898250539527657267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39610993932167026351771511 59416490898250539527657267)
          ·
            refine ⟨89124736347375809291485901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59416490898250539527657267 89124736347375809291485901)
            ·
              refine ⟨33421776130265928484307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89124736347375809291485901 33421776130265928484307213)
              ·
                refine ⟨12533166048849723181615205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33421776130265928484307213 12533166048849723181615205)
                ·
                  refine ⟨2349968634159323096552851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12533166048849723181615205 2349968634159323096552851)
                  ·
                    refine ⟨3524952951238984644829277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349968634159323096552851 3524952951238984644829277)
                    ·
                      refine ⟨1321857356714619241810979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3524952951238984644829277 1321857356714619241810979)
                      ·
                        rfl

theorem cell23_2574308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_2574308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574308 prefixEnd_2574308 := by exact prefixLift 2574308
  have htrace : WordTrace (prefixWord ++ tailWord_2574308) baseStart_2574308 baseEnd_2574308 := by
    simpa [prefixWord, tailWord_2574308, baseEnd_2574308] using wordTrace_append hprefix tailTrace_2574308
  have hstable : (prefixWord ++ tailWord_2574308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574308).length < 2 ^ (prefixWord ++ tailWord_2574308).sum := by decide
  have hdescent : baseEnd_2574308 < baseStart_2574308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574361 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2574361 : Nat := 118140960795 + 2574361 * 2 ^ 59
def prefixEnd_2574361 : Nat := 4983230072969 + 3 ^ 40 * 2574361 * 2
def baseEnd_2574361 : Nat := 1321884571189307534448235

theorem tailTrace_2574361 : CollatzResearch.WordTrace tailWord_2574361 prefixEnd_2574361 1321884571189307534448235 := by
  unfold tailWord_2574361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93894659426537237700322937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62596439617691491800215291 93894659426537237700322937)
  ·
    refine ⟨70420994569902928275242203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93894659426537237700322937 70420994569902928275242203)
    ·
      refine ⟨105631491854854392412863305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70420994569902928275242203 105631491854854392412863305)
      ·
        refine ⟨79223618891140794309647479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105631491854854392412863305 79223618891140794309647479)
        ·
          refine ⟨118835428336711191464471219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79223618891140794309647479 118835428336711191464471219)
          ·
            refine ⟨178253142505066787196706829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118835428336711191464471219 178253142505066787196706829)
            ·
              refine ⟨66844928439400045198765061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178253142505066787196706829 66844928439400045198765061)
              ·
                refine ⟨12533424082387508474768449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66844928439400045198765061 12533424082387508474768449)
                ·
                  refine ⟨9400068061790631356076337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12533424082387508474768449 9400068061790631356076337)
                  ·
                    refine ⟨7050051046342973517057253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9400068061790631356076337 7050051046342973517057253)
                    ·
                      refine ⟨1321884571189307534448235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7050051046342973517057253 1321884571189307534448235)
                      ·
                        rfl

theorem cell23_2574361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2574361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574361 prefixEnd_2574361 := by exact prefixLift 2574361
  have htrace : WordTrace (prefixWord ++ tailWord_2574361) baseStart_2574361 baseEnd_2574361 := by
    simpa [prefixWord, tailWord_2574361, baseEnd_2574361] using wordTrace_append hprefix tailTrace_2574361
  have hstable : (prefixWord ++ tailWord_2574361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574361).length < 2 ^ (prefixWord ++ tailWord_2574361).sum := by decide
  have hdescent : baseEnd_2574361 < baseStart_2574361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574371 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 7]
def baseStart_2574371 : Nat := 118140960795 + 2574371 * 2 ^ 59
def prefixEnd_2574371 : Nat := 4983230072969 + 3 ^ 40 * 2574371 * 2
def baseEnd_2574371 : Nat := 146876633999539166147021

theorem tailTrace_2574371 : CollatzResearch.WordTrace tailWord_2574371 prefixEnd_2574371 146876633999539166147021 := by
  unfold tailWord_2574371
  simp only [CollatzResearch.WordTrace]
  refine ⟨93895024156501009408186967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62596682771000672938791311 93895024156501009408186967)
  ·
    refine ⟨140842536234751514112280451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93895024156501009408186967 140842536234751514112280451)
    ·
      refine ⟨211263804352127271168420677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140842536234751514112280451 211263804352127271168420677)
      ·
        refine ⟨39611963316023863344078877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211263804352127271168420677 39611963316023863344078877)
        ·
          refine ⟨14854486243508948754029579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39611963316023863344078877 14854486243508948754029579)
          ·
            refine ⟨22281729365263423131044369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14854486243508948754029579 22281729365263423131044369)
            ·
              refine ⟨16711297023947567348283277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22281729365263423131044369 16711297023947567348283277)
              ·
                refine ⟨6266736383980337755606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16711297023947567348283277 6266736383980337755606229)
                ·
                  refine ⟨146876633999539166147021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6266736383980337755606229 146876633999539166147021)
                  ·
                    rfl

theorem cell23_2574371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 7].length) (baseStart_2574371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574371 prefixEnd_2574371 := by exact prefixLift 2574371
  have htrace : WordTrace (prefixWord ++ tailWord_2574371) baseStart_2574371 baseEnd_2574371 := by
    simpa [prefixWord, tailWord_2574371, baseEnd_2574371] using wordTrace_append hprefix tailTrace_2574371
  have hstable : (prefixWord ++ tailWord_2574371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574371).length < 2 ^ (prefixWord ++ tailWord_2574371).sum := by decide
  have hdescent : baseEnd_2574371 < baseStart_2574371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574375 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2574375 : Nat := 118140960795 + 2574375 * 2 ^ 59
def prefixEnd_2574375 : Nat := 4983230072969 + 3 ^ 40 * 2574375 * 2
def baseEnd_2574375 : Nat := 440630586639490159891057

theorem tailTrace_2574375 : CollatzResearch.WordTrace tailWord_2574375 prefixEnd_2574375 440630586639490159891057 := by
  unfold tailWord_2574375
  simp only [CollatzResearch.WordTrace]
  refine ⟨93895170048486518091332579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62596780032324345394221719 93895170048486518091332579)
  ·
    refine ⟨140842755072729777136998869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93895170048486518091332579 140842755072729777136998869)
    ·
      refine ⟨3301002072017104151648411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 140842755072729777136998869 3301002072017104151648411)
      ·
        refine ⟨4951503108025656227472617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301002072017104151648411 4951503108025656227472617)
        ·
          refine ⟨3713627331019242170604463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951503108025656227472617 3713627331019242170604463)
          ·
            refine ⟨5570440996528863255906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713627331019242170604463 5570440996528863255906695)
            ·
              refine ⟨8355661494793294883860043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570440996528863255906695 8355661494793294883860043)
              ·
                refine ⟨12533492242189942325790065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355661494793294883860043 12533492242189942325790065)
                ·
                  refine ⟨9400119181642456744342549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12533492242189942325790065 9400119181642456744342549)
                  ·
                    refine ⟨440630586639490159891057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9400119181642456744342549 440630586639490159891057)
                    ·
                      rfl

theorem cell23_2574375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2574375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574375 prefixEnd_2574375 := by exact prefixLift 2574375
  have htrace : WordTrace (prefixWord ++ tailWord_2574375) baseStart_2574375 baseEnd_2574375 := by
    simpa [prefixWord, tailWord_2574375, baseEnd_2574375] using wordTrace_append hprefix tailTrace_2574375
  have hstable : (prefixWord ++ tailWord_2574375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574375).length < 2 ^ (prefixWord ++ tailWord_2574375).sum := by decide
  have hdescent : baseEnd_2574375 < baseStart_2574375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574378 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2574378 : Nat := 118140960795 + 2574378 * 2 ^ 59
def prefixEnd_2574378 : Nat := 4983230072969 + 3 ^ 40 * 2574378 * 2
def baseEnd_2574378 : Nat := 1321893300360433967935657

theorem tailTrace_2574378 : CollatzResearch.WordTrace tailWord_2574378 prefixEnd_2574378 1321893300360433967935657 := by
  unfold tailWord_2574378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23473819866868912400922947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62596852978317099735794525 23473819866868912400922947)
  ·
    refine ⟨35210729800303368601384421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23473819866868912400922947 35210729800303368601384421)
    ·
      refine ⟨6602011837556881612759579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35210729800303368601384421 6602011837556881612759579)
      ·
        refine ⟨9903017756335322419139369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602011837556881612759579 9903017756335322419139369)
        ·
          refine ⟨7427263317251491814354527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903017756335322419139369 7427263317251491814354527)
          ·
            refine ⟨11140894975877237721531791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427263317251491814354527 11140894975877237721531791)
            ·
              refine ⟨16711342463815856582297687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140894975877237721531791 16711342463815856582297687)
              ·
                refine ⟨25067013695723784873446531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16711342463815856582297687 25067013695723784873446531)
                ·
                  refine ⟨37600520543585677310169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25067013695723784873446531 37600520543585677310169797)
                  ·
                    refine ⟨7050097601922314495656837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37600520543585677310169797 7050097601922314495656837)
                    ·
                      refine ⟨1321893300360433967935657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7050097601922314495656837 1321893300360433967935657)
                      ·
                        rfl

theorem cell23_2574378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2574378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574378 prefixEnd_2574378 := by exact prefixLift 2574378
  have htrace : WordTrace (prefixWord ++ tailWord_2574378) baseStart_2574378 baseEnd_2574378 := by
    simpa [prefixWord, tailWord_2574378, baseEnd_2574378] using wordTrace_append hprefix tailTrace_2574378
  have hstable : (prefixWord ++ tailWord_2574378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574378).length < 2 ^ (prefixWord ++ tailWord_2574378).sum := by decide
  have hdescent : baseEnd_2574378 < baseStart_2574378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574382 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2574382 : Nat := 118140960795 + 2574382 * 2 ^ 59
def prefixEnd_2574382 : Nat := 4983230072969 + 3 ^ 40 * 2574382 * 2
def baseEnd_2574382 : Nat := 1321895354283051952285639

theorem tailTrace_2574382 : CollatzResearch.WordTrace tailWord_2574382 prefixEnd_2574382 1321895354283051952285639 := by
  unfold tailWord_2574382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736928169932644785854675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62596950239640772191224933 11736928169932644785854675)
  ·
    refine ⟨17605392254898967178782013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11736928169932644785854675 17605392254898967178782013)
    ·
      refine ⟨6602022095587112692043255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17605392254898967178782013 6602022095587112692043255)
      ·
        refine ⟨9903033143380669038064883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602022095587112692043255 9903033143380669038064883)
        ·
          refine ⟨14854549715071003557097325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903033143380669038064883 14854549715071003557097325)
          ·
            refine ⟨5570456143151626333911497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14854549715071003557097325 5570456143151626333911497)
            ·
              refine ⟨4177842107363719750433623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570456143151626333911497 4177842107363719750433623)
              ·
                refine ⟨6266763161045579625650435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177842107363719750433623 6266763161045579625650435)
                ·
                  refine ⟨9400144741568369438475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266763161045579625650435 9400144741568369438475653)
                  ·
                    refine ⟨1762527139044069269714185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9400144741568369438475653 1762527139044069269714185)
                    ·
                      refine ⟨1321895354283051952285639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762527139044069269714185 1321895354283051952285639)
                      ·
                        rfl

theorem cell23_2574382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2574382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574382 prefixEnd_2574382 := by exact prefixLift 2574382
  have htrace : WordTrace (prefixWord ++ tailWord_2574382) baseStart_2574382 baseEnd_2574382 := by
    simpa [prefixWord, tailWord_2574382, baseEnd_2574382] using wordTrace_append hprefix tailTrace_2574382
  have hstable : (prefixWord ++ tailWord_2574382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574382).length < 2 ^ (prefixWord ++ tailWord_2574382).sum := by decide
  have hdescent : baseEnd_2574382 < baseStart_2574382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574408 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_2574408 : Nat := 118140960795 + 2574408 * 2 ^ 59
def prefixEnd_2574408 : Nat := 4983230072969 + 3 ^ 40 * 2574408 * 2
def baseEnd_2574408 : Nat := 1321908704780068850560519

theorem tailTrace_2574408 : CollatzResearch.WordTrace tailWord_2574408 prefixEnd_2574408 1321908704780068850560519 := by
  unfold tailWord_2574408
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948186828683482363641939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62597582438244643151522585 46948186828683482363641939)
  ·
    refine ⟨70422280243025223545462909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46948186828683482363641939 70422280243025223545462909)
    ·
      refine ⟨26408355091134458829548591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70422280243025223545462909 26408355091134458829548591)
      ·
        refine ⟨39612532636701688244322887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26408355091134458829548591 39612532636701688244322887)
        ·
          refine ⟨59418798955052532366484331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39612532636701688244322887 59418798955052532366484331)
          ·
            refine ⟨89128198432578798549726497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59418798955052532366484331 89128198432578798549726497)
            ·
              refine ⟨66846148824434098912294873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89128198432578798549726497 66846148824434098912294873)
              ·
                refine ⟨50134611618325574184221155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66846148824434098912294873 50134611618325574184221155)
                ·
                  refine ⟨75201917427488361276331733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50134611618325574184221155 75201917427488361276331733)
                  ·
                    refine ⟨1762544939706758467414025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75201917427488361276331733 1762544939706758467414025)
                    ·
                      refine ⟨1321908704780068850560519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762544939706758467414025 1321908704780068850560519)
                      ·
                        rfl

theorem cell23_2574408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_2574408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574408 prefixEnd_2574408 := by exact prefixLift 2574408
  have htrace : WordTrace (prefixWord ++ tailWord_2574408) baseStart_2574408 baseEnd_2574408 := by
    simpa [prefixWord, tailWord_2574408, baseEnd_2574408] using wordTrace_append hprefix tailTrace_2574408
  have hstable : (prefixWord ++ tailWord_2574408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574408).length < 2 ^ (prefixWord ++ tailWord_2574408).sum := by decide
  have hdescent : baseEnd_2574408 < baseStart_2574408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574422 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2574422 : Nat := 118140960795 + 2574422 * 2 ^ 59
def prefixEnd_2574422 : Nat := 4983230072969 + 3 ^ 40 * 2574422 * 2
def baseEnd_2574422 : Nat := 146879543723247977309495

theorem tailTrace_2574422 : CollatzResearch.WordTrace tailWord_2574422 prefixEnd_2574422 146879543723247977309495 := by
  unfold tailWord_2574422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868555267457265319893345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62597922852877496745529013 5868555267457265319893345)
  ·
    refine ⟨4401416450592948989920009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5868555267457265319893345 4401416450592948989920009)
    ·
      refine ⟨3301062337944711742440007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4401416450592948989920009 3301062337944711742440007)
      ·
        refine ⟨4951593506917067613660011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301062337944711742440007 4951593506917067613660011)
        ·
          refine ⟨7427390260375601420490017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951593506917067613660011 7427390260375601420490017)
          ·
            refine ⟨5570542695281701065367513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427390260375601420490017 5570542695281701065367513)
            ·
              refine ⟨4177907021461275799025635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570542695281701065367513 4177907021461275799025635)
              ·
                refine ⟨6266860532191913698538453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177907021461275799025635 6266860532191913698538453)
                ·
                  refine ⟨146879543723247977309495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6266860532191913698538453 146879543723247977309495)
                  ·
                    rfl

theorem cell23_2574422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2574422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574422 prefixEnd_2574422 := by exact prefixLift 2574422
  have htrace : WordTrace (prefixWord ++ tailWord_2574422) baseStart_2574422 baseEnd_2574422 := by
    simpa [prefixWord, tailWord_2574422, baseEnd_2574422] using wordTrace_append hprefix tailTrace_2574422
  have hstable : (prefixWord ++ tailWord_2574422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574422).length < 2 ^ (prefixWord ++ tailWord_2574422).sum := by decide
  have hdescent : baseEnd_2574422 < baseStart_2574422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574458 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_2574458 : Nat := 118140960795 + 2574458 * 2 ^ 59
def prefixEnd_2574458 : Nat := 4983230072969 + 3 ^ 40 * 2574458 * 2
def baseEnd_2574458 : Nat := 1321934378812793654935289

theorem tailTrace_2574458 : CollatzResearch.WordTrace tailWord_2574458 prefixEnd_2574458 1321934378812793654935289 := by
  unfold tailWord_2574458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23474549326796455816651007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62598798204790548844402685 23474549326796455816651007)
  ·
    refine ⟨35211823990194683724976511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23474549326796455816651007 35211823990194683724976511)
    ·
      refine ⟨52817735985292025587464767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35211823990194683724976511 52817735985292025587464767)
      ·
        refine ⟨79226603977938038381197151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52817735985292025587464767 79226603977938038381197151)
        ·
          refine ⟨118839905966907057571795727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79226603977938038381197151 118839905966907057571795727)
          ·
            refine ⟨178259858950360586357693591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118839905966907057571795727 178259858950360586357693591)
            ·
              refine ⟨267389788425540879536540387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178259858950360586357693591 267389788425540879536540387)
              ·
                refine ⟨401084682638311319304810581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267389788425540879536540387 401084682638311319304810581)
                ·
                  refine ⟨4700211124667710773103249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 401084682638311319304810581 4700211124667710773103249)
                  ·
                    refine ⟨3525158343500783079827437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700211124667710773103249 3525158343500783079827437)
                    ·
                      refine ⟨1321934378812793654935289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525158343500783079827437 1321934378812793654935289)
                      ·
                        rfl

theorem cell23_2574458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_2574458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574458 prefixEnd_2574458 := by exact prefixLift 2574458
  have htrace : WordTrace (prefixWord ++ tailWord_2574458) baseStart_2574458 baseEnd_2574458 := by
    simpa [prefixWord, tailWord_2574458, baseEnd_2574458] using wordTrace_append hprefix tailTrace_2574458
  have hstable : (prefixWord ++ tailWord_2574458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574458).length < 2 ^ (prefixWord ++ tailWord_2574458).sum := by decide
  have hdescent : baseEnd_2574458 < baseStart_2574458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574495 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 6]
def baseStart_2574495 : Nat := 118140960795 + 2574495 * 2 ^ 59
def prefixEnd_2574495 : Nat := 4983230072969 + 3 ^ 40 * 2574495 * 2
def baseEnd_2574495 : Nat := 146883708621890001130291

theorem tailTrace_2574495 : CollatzResearch.WordTrace tailWord_2574495 prefixEnd_2574495 146883708621890001130291 := by
  unfold tailWord_2574495
  simp only [CollatzResearch.WordTrace]
  refine ⟨93899546808051778585700939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62599697872034519057133959 93899546808051778585700939)
  ·
    refine ⟨140849320212077667878551409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93899546808051778585700939 140849320212077667878551409)
    ·
      refine ⟨105636990159058250908913557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140849320212077667878551409 105636990159058250908913557)
      ·
        refine ⟨4951733913705855511355323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105636990159058250908913557 4951733913705855511355323)
        ·
          refine ⟨7427600870558783267032985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951733913705855511355323 7427600870558783267032985)
          ·
            refine ⟨5570700652919087450274739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427600870558783267032985 5570700652919087450274739)
            ·
              refine ⟨8356050979378631175412109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570700652919087450274739 8356050979378631175412109)
              ·
                refine ⟨3133519117266986690779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8356050979378631175412109 3133519117266986690779541)
                ·
                  refine ⟨146883708621890001130291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3133519117266986690779541 146883708621890001130291)
                  ·
                    rfl

theorem cell23_2574495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 6].length) (baseStart_2574495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574495 prefixEnd_2574495 := by exact prefixLift 2574495
  have htrace : WordTrace (prefixWord ++ tailWord_2574495) baseStart_2574495 baseEnd_2574495 := by
    simpa [prefixWord, tailWord_2574495, baseEnd_2574495] using wordTrace_append hprefix tailTrace_2574495
  have hstable : (prefixWord ++ tailWord_2574495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574495).length < 2 ^ (prefixWord ++ tailWord_2574495).sum := by decide
  have hdescent : baseEnd_2574495 < baseStart_2574495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574538 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_2574538 : Nat := 118140960795 + 2574538 * 2 ^ 59
def prefixEnd_2574538 : Nat := 4983230072969 + 3 ^ 40 * 2574538 * 2
def baseEnd_2574538 : Nat := 440658485755051113978307

theorem tailTrace_2574538 : CollatzResearch.WordTrace tailWord_2574538 prefixEnd_2574538 440658485755051113978307 := by
  unfold tailWord_2574538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475278786723999232379067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62600743431263997953010845 23475278786723999232379067)
  ·
    refine ⟨35212918180085998848568601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23475278786723999232379067 35212918180085998848568601)
    ·
      refine ⟨26409688635064499136426451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35212918180085998848568601 26409688635064499136426451)
      ·
        refine ⟨39614532952596748704639677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26409688635064499136426451 39614532952596748704639677)
        ·
          refine ⟨14855449857223780764239879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39614532952596748704639677 14855449857223780764239879)
          ·
            refine ⟨22283174785835671146359819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14855449857223780764239879 22283174785835671146359819)
            ·
              refine ⟨33424762178753506719539729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22283174785835671146359819 33424762178753506719539729)
              ·
                refine ⟨25068571634065130039654797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33424762178753506719539729 25068571634065130039654797)
                ·
                  refine ⟨9400714362774423764870549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25068571634065130039654797 9400714362774423764870549)
                  ·
                    refine ⟨440658485755051113978307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9400714362774423764870549 440658485755051113978307)
                    ·
                      rfl

theorem cell23_2574538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_2574538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574538 prefixEnd_2574538 := by exact prefixLift 2574538
  have htrace : WordTrace (prefixWord ++ tailWord_2574538) baseStart_2574538 baseEnd_2574538 := by
    simpa [prefixWord, tailWord_2574538, baseEnd_2574538] using wordTrace_append hprefix tailTrace_2574538
  have hstable : (prefixWord ++ tailWord_2574538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574538).length < 2 ^ (prefixWord ++ tailWord_2574538).sum := by decide
  have hdescent : baseEnd_2574538 < baseStart_2574538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574556 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2574556 : Nat := 118140960795 + 2574556 * 2 ^ 59
def prefixEnd_2574556 : Nat := 4983230072969 + 3 ^ 40 * 2574556 * 2
def baseEnd_2574556 : Nat := 1321984699916934271509839

theorem tailTrace_2574556 : CollatzResearch.WordTrace tailWord_2574556 prefixEnd_2574556 1321984699916934271509839 := by
  unfold tailWord_2574556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46950885830415393001835761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62601181107220524002447681 46950885830415393001835761)
  ·
    refine ⟨35213164372811544751376821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46950885830415393001835761 35213164372811544751376821)
    ·
      refine ⟨3301234159951082320441577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35213164372811544751376821 3301234159951082320441577)
      ·
        refine ⟨2475925619963311740331183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301234159951082320441577 2475925619963311740331183)
        ·
          refine ⟨3713888429944967610496775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475925619963311740331183 3713888429944967610496775)
          ·
            refine ⟨5570832644917451415745163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713888429944967610496775 5570832644917451415745163)
            ·
              refine ⟨8356248967376177123617745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570832644917451415745163 8356248967376177123617745)
              ·
                refine ⟨6267186725532132842713309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8356248967376177123617745 6267186725532132842713309)
                ·
                  refine ⟨2350195022074549816017491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6267186725532132842713309 2350195022074549816017491)
                  ·
                    refine ⟨3525292533111824724026237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350195022074549816017491 3525292533111824724026237)
                    ·
                      refine ⟨1321984699916934271509839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525292533111824724026237 1321984699916934271509839)
                      ·
                        rfl

theorem cell23_2574556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2574556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574556 prefixEnd_2574556 := by exact prefixLift 2574556
  have htrace : WordTrace (prefixWord ++ tailWord_2574556) baseStart_2574556 baseEnd_2574556 := by
    simpa [prefixWord, tailWord_2574556, baseEnd_2574556] using wordTrace_append hprefix tailTrace_2574556
  have hstable : (prefixWord ++ tailWord_2574556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574556).length < 2 ^ (prefixWord ++ tailWord_2574556).sum := by decide
  have hdescent : baseEnd_2574556 < baseStart_2574556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574575 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_2574575 : Nat := 118140960795 + 2574575 * 2 ^ 59
def prefixEnd_2574575 : Nat := 4983230072969 + 3 ^ 40 * 2574575 * 2
def baseEnd_2574575 : Nat := 1321994456049369697172251

theorem tailTrace_2574575 : CollatzResearch.WordTrace tailWord_2574575 prefixEnd_2574575 1321994456049369697172251 := by
  unfold tailWord_2574575
  simp only [CollatzResearch.WordTrace]
  refine ⟨93902464647761952248613179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62601643098507968165742119 93902464647761952248613179)
  ·
    refine ⟨140853696971642928372919769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93902464647761952248613179 140853696971642928372919769)
    ·
      refine ⟨105640272728732196279689827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140853696971642928372919769 105640272728732196279689827)
      ·
        refine ⟨158460409093098294419534741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105640272728732196279689827 158460409093098294419534741)
        ·
          refine ⟨7427831676238982550915691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158460409093098294419534741 7427831676238982550915691)
          ·
            refine ⟨11141747514358473826373537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427831676238982550915691 11141747514358473826373537)
            ·
              refine ⟨8356310635768855369780153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141747514358473826373537 8356310635768855369780153)
              ·
                refine ⟨6267232976826641527335115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8356310635768855369780153 6267232976826641527335115)
                ·
                  refine ⟨9400849465239962291002673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267232976826641527335115 9400849465239962291002673)
                  ·
                    refine ⟨7050637098929971718252005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9400849465239962291002673 7050637098929971718252005)
                    ·
                      refine ⟨1321994456049369697172251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7050637098929971718252005 1321994456049369697172251)
                      ·
                        rfl

theorem cell23_2574575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_2574575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574575 prefixEnd_2574575 := by exact prefixLift 2574575
  have htrace : WordTrace (prefixWord ++ tailWord_2574575) baseStart_2574575 baseEnd_2574575 := by
    simpa [prefixWord, tailWord_2574575, baseEnd_2574575] using wordTrace_append hprefix tailTrace_2574575
  have hstable : (prefixWord ++ tailWord_2574575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574575).length < 2 ^ (prefixWord ++ tailWord_2574575).sum := by decide
  have hdescent : baseEnd_2574575 < baseStart_2574575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574596 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2574596 : Nat := 118140960795 + 2574596 * 2 ^ 59
def prefixEnd_2574596 : Nat := 4983230072969 + 3 ^ 40 * 2574596 * 2
def baseEnd_2574596 : Nat := 1322005239143114115009655

theorem tailTrace_2574596 : CollatzResearch.WordTrace tailWord_2574596 prefixEnd_2574596 1322005239143114115009655 := by
  unfold tailWord_2574596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951615290342936417563821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62602153720457248556751761 46951615290342936417563821)
  ·
    refine ⟨17606855733878601156586433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46951615290342936417563821 17606855733878601156586433)
    ·
      refine ⟨13205141800408950867439825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17606855733878601156586433 13205141800408950867439825)
      ·
        refine ⟨9903856350306713150579869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13205141800408950867439825 9903856350306713150579869)
        ·
          refine ⟨3713946131365017431467451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9903856350306713150579869 3713946131365017431467451)
          ·
            refine ⟨5570919197047526147201177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713946131365017431467451 5570919197047526147201177)
            ·
              refine ⟨4178189397785644610400883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570919197047526147201177 4178189397785644610400883)
              ·
                refine ⟨6267284096678466915601325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178189397785644610400883 6267284096678466915601325)
                ·
                  refine ⟨2350231536254425093350497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6267284096678466915601325 2350231536254425093350497)
                  ·
                    refine ⟨1762673652190818820012873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350231536254425093350497 1762673652190818820012873)
                    ·
                      refine ⟨1322005239143114115009655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762673652190818820012873 1322005239143114115009655)
                      ·
                        rfl

theorem cell23_2574596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2574596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574596 prefixEnd_2574596 := by exact prefixLift 2574596
  have htrace : WordTrace (prefixWord ++ tailWord_2574596) baseStart_2574596 baseEnd_2574596 := by
    simpa [prefixWord, tailWord_2574596, baseEnd_2574596] using wordTrace_append hprefix tailTrace_2574596
  have hstable : (prefixWord ++ tailWord_2574596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574596).length < 2 ^ (prefixWord ++ tailWord_2574596).sum := by decide
  have hdescent : baseEnd_2574596 < baseStart_2574596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574655 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_2574655 : Nat := 118140960795 + 2574655 * 2 ^ 59
def prefixEnd_2574655 : Nat := 4983230072969 + 3 ^ 40 * 2574655 * 2
def baseEnd_2574655 : Nat := 1322035534501729384171883

theorem tailTrace_2574655 : CollatzResearch.WordTrace tailWord_2574655 prefixEnd_2574655 1322035534501729384171883 := by
  unfold tailWord_2574655
  simp only [CollatzResearch.WordTrace]
  refine ⟨93905382487472125911525419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62603588324981417274350279 93905382487472125911525419)
  ·
    refine ⟨140858073731208188867288129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93905382487472125911525419 140858073731208188867288129)
    ·
      refine ⟨105643555298406141650466097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140858073731208188867288129 105643555298406141650466097)
      ·
        refine ⟨79232666473804606237849573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105643555298406141650466097 79232666473804606237849573)
        ·
          refine ⟨14856124963838363669596795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79232666473804606237849573 14856124963838363669596795)
          ·
            refine ⟨22284187445757545504395193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14856124963838363669596795 22284187445757545504395193)
            ·
              refine ⟨16713140584318159128296395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22284187445757545504395193 16713140584318159128296395)
              ·
                refine ⟨25069710876477238692444593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16713140584318159128296395 25069710876477238692444593)
                ·
                  refine ⟨18802283157357929019333445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25069710876477238692444593 18802283157357929019333445)
                  ·
                    refine ⟨3525428092004611691125021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18802283157357929019333445 3525428092004611691125021)
                    ·
                      refine ⟨1322035534501729384171883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525428092004611691125021 1322035534501729384171883)
                      ·
                        rfl

theorem cell23_2574655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_2574655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574655 prefixEnd_2574655 := by exact prefixLift 2574655
  have htrace : WordTrace (prefixWord ++ tailWord_2574655) baseStart_2574655 baseEnd_2574655 := by
    simpa [prefixWord, tailWord_2574655, baseEnd_2574655] using wordTrace_append hprefix tailTrace_2574655
  have hstable : (prefixWord ++ tailWord_2574655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574655).length < 2 ^ (prefixWord ++ tailWord_2574655).sum := by decide
  have hdescent : baseEnd_2574655 < baseStart_2574655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574692 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2574692 : Nat := 118140960795 + 2574692 * 2 ^ 59
def prefixEnd_2574692 : Nat := 4983230072969 + 3 ^ 40 * 2574692 * 2
def baseEnd_2574692 : Nat := 146894948142882859934357

theorem tailTrace_2574692 : CollatzResearch.WordTrace tailWord_2574692 prefixEnd_2574692 146894948142882859934357 := by
  unfold tailWord_2574692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953365994169040615311165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62604487992225387487081553 46953365994169040615311165)
  ·
    refine ⟨17607512247813390230741687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46953365994169040615311165 17607512247813390230741687)
    ·
      refine ⟨26411268371720085346112531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17607512247813390230741687 26411268371720085346112531)
      ·
        refine ⟨39616902557580128019168797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26411268371720085346112531 39616902557580128019168797)
        ·
          refine ⟨14856338459092548007188299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39616902557580128019168797 14856338459092548007188299)
          ·
            refine ⟨22284507688638822010782449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14856338459092548007188299 22284507688638822010782449)
            ·
              refine ⟨16713380766479116508086837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22284507688638822010782449 16713380766479116508086837)
              ·
                refine ⟨1566879446857417172633141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16713380766479116508086837 1566879446857417172633141)
                ·
                  refine ⟨146894948142882859934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566879446857417172633141 146894948142882859934357)
                  ·
                    rfl

theorem cell23_2574692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2574692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574692 prefixEnd_2574692 := by exact prefixLift 2574692
  have htrace : WordTrace (prefixWord ++ tailWord_2574692) baseStart_2574692 baseEnd_2574692 := by
    simpa [prefixWord, tailWord_2574692, baseEnd_2574692] using wordTrace_append hprefix tailTrace_2574692
  have hstable : (prefixWord ++ tailWord_2574692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574692).length < 2 ^ (prefixWord ++ tailWord_2574692).sum := by decide
  have hdescent : baseEnd_2574692 < baseStart_2574692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574709 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 5]
def baseStart_2574709 : Nat := 118140960795 + 2574709 * 2 ^ 59
def prefixEnd_2574709 : Nat := 4983230072969 + 3 ^ 40 * 2574709 * 2
def baseEnd_2574709 : Nat := 146895918050785796988515

theorem tailTrace_2574709 : CollatzResearch.WordTrace tailWord_2574709 prefixEnd_2574709 146895918050785796988515 := by
  unfold tailWord_2574709
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907352029276493133991181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62604901352850995422660787 93907352029276493133991181)
  ·
    refine ⟨35215257010978684925246693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93907352029276493133991181 35215257010978684925246693)
    ·
      refine ⟨6602860689558503423483755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35215257010978684925246693 6602860689558503423483755)
      ·
        refine ⟨9904291034337755135225633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602860689558503423483755 9904291034337755135225633)
        ·
          refine ⟨7428218275753316351419225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9904291034337755135225633 7428218275753316351419225)
          ·
            refine ⟨5571163706814987263564419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428218275753316351419225 5571163706814987263564419)
            ·
              refine ⟨8356745560222480895346629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571163706814987263564419 8356745560222480895346629)
              ·
                refine ⟨1566889792541715167877493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8356745560222480895346629 1566889792541715167877493)
                ·
                  refine ⟨146895918050785796988515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566889792541715167877493 146895918050785796988515)
                  ·
                    rfl

theorem cell23_2574709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_2574709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574709 prefixEnd_2574709 := by exact prefixLift 2574709
  have htrace : WordTrace (prefixWord ++ tailWord_2574709) baseStart_2574709 baseEnd_2574709 := by
    simpa [prefixWord, tailWord_2574709, baseEnd_2574709] using wordTrace_append hprefix tailTrace_2574709
  have hstable : (prefixWord ++ tailWord_2574709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574709).length < 2 ^ (prefixWord ++ tailWord_2574709).sum := by decide
  have hdescent : baseEnd_2574709 < baseStart_2574709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574715 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_2574715 : Nat := 118140960795 + 2574715 * 2 ^ 59
def prefixEnd_2574715 : Nat := 4983230072969 + 3 ^ 40 * 2574715 * 2
def baseEnd_2574715 : Nat := 1322066343340999149421607

theorem tailTrace_2574715 : CollatzResearch.WordTrace tailWord_2574715 prefixEnd_2574715 1322066343340999149421607 := by
  unfold tailWord_2574715
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907570867254756158709599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62605047244836504105806399 93907570867254756158709599)
  ·
    refine ⟨140861356300882134238064399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93907570867254756158709599 140861356300882134238064399)
    ·
      refine ⟨211292034451323201357096599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140861356300882134238064399 211292034451323201357096599)
      ·
        refine ⟨316938051676984802035644899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211292034451323201357096599 316938051676984802035644899)
        ·
          refine ⟨475407077515477203053467349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316938051676984802035644899 475407077515477203053467349)
          ·
            refine ⟨11142353379268996946565641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 475407077515477203053467349 11142353379268996946565641)
            ·
              refine ⟨8356765034451747709924231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11142353379268996946565641 8356765034451747709924231)
              ·
                refine ⟨12535147551677621564886347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356765034451747709924231 12535147551677621564886347)
                ·
                  refine ⟨18802721327516432347329521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535147551677621564886347 18802721327516432347329521)
                  ·
                    refine ⟨14102040995637324260497141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18802721327516432347329521 14102040995637324260497141)
                    ·
                      refine ⟨1322066343340999149421607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14102040995637324260497141 1322066343340999149421607)
                      ·
                        rfl

theorem cell23_2574715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_2574715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574715 prefixEnd_2574715 := by exact prefixLift 2574715
  have htrace : WordTrace (prefixWord ++ tailWord_2574715) baseStart_2574715 baseEnd_2574715 := by
    simpa [prefixWord, tailWord_2574715, baseEnd_2574715] using wordTrace_append hprefix tailTrace_2574715
  have hstable : (prefixWord ++ tailWord_2574715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574715).length < 2 ^ (prefixWord ++ tailWord_2574715).sum := by decide
  have hdescent : baseEnd_2574715 < baseStart_2574715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574725 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_2574725 : Nat := 118140960795 + 2574725 * 2 ^ 59
def prefixEnd_2574725 : Nat := 4983230072969 + 3 ^ 40 * 2574725 * 2
def baseEnd_2574725 : Nat := 1322071478147544110296561

theorem tailTrace_2574725 : CollatzResearch.WordTrace tailWord_2574725 prefixEnd_2574725 1322071478147544110296561 := by
  unfold tailWord_2574725
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907935597218527866573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62605290398145685244382419 93907935597218527866573629)
  ·
    refine ⟨35215475848956947949965111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93907935597218527866573629 35215475848956947949965111)
    ·
      refine ⟨52823213773435421924947667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35215475848956947949965111 52823213773435421924947667)
      ·
        refine ⟨79234820660153132887421501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52823213773435421924947667 79234820660153132887421501)
        ·
          refine ⟨29713057747557424832783063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79234820660153132887421501 29713057747557424832783063)
          ·
            refine ⟨44569586621336137249174595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29713057747557424832783063 44569586621336137249174595)
            ·
              refine ⟨66854379932004205873761893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44569586621336137249174595 66854379932004205873761893)
              ·
                refine ⟨12535196237250788601330355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66854379932004205873761893 12535196237250788601330355)
                ·
                  refine ⟨18802794355876182901995533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535196237250788601330355 18802794355876182901995533)
                  ·
                    refine ⟨7051047883453568588248325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18802794355876182901995533 7051047883453568588248325)
                    ·
                      refine ⟨1322071478147544110296561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7051047883453568588248325 1322071478147544110296561)
                      ·
                        rfl

theorem cell23_2574725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_2574725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574725 prefixEnd_2574725 := by exact prefixLift 2574725
  have htrace : WordTrace (prefixWord ++ tailWord_2574725) baseStart_2574725 baseEnd_2574725 := by
    simpa [prefixWord, tailWord_2574725, baseEnd_2574725] using wordTrace_append hprefix tailTrace_2574725
  have hstable : (prefixWord ++ tailWord_2574725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574725).length < 2 ^ (prefixWord ++ tailWord_2574725).sum := by decide
  have hdescent : baseEnd_2574725 < baseStart_2574725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574755 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2574755 : Nat := 118140960795 + 2574755 * 2 ^ 59
def prefixEnd_2574755 : Nat := 4983230072969 + 3 ^ 40 * 2574755 * 2
def baseEnd_2574755 : Nat := 1322086882567178992921423

theorem tailTrace_2574755 : CollatzResearch.WordTrace tailWord_2574755 prefixEnd_2574755 1322086882567178992921423 := by
  unfold tailWord_2574755
  simp only [CollatzResearch.WordTrace]
  refine ⟨93909029787109842990165719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62606019858073228660110479 93909029787109842990165719)
  ·
    refine ⟨140863544680664764485248579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93909029787109842990165719 140863544680664764485248579)
    ·
      refine ⟨211295317020997146727872869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140863544680664764485248579 211295317020997146727872869)
      ·
        refine ⟨39617871941436965011476163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211295317020997146727872869 39617871941436965011476163)
        ·
          refine ⟨59426807912155447517214245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39617871941436965011476163 59426807912155447517214245)
          ·
            refine ⟨11142526483529146409477671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59426807912155447517214245 11142526483529146409477671)
            ·
              refine ⟨16713789725293719614216507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142526483529146409477671 16713789725293719614216507)
              ·
                refine ⟨25070684587940579421324761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16713789725293719614216507 25070684587940579421324761)
                ·
                  refine ⟨18803013440955434565993571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25070684587940579421324761 18803013440955434565993571)
                  ·
                    refine ⟨28204520161433151848990357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18803013440955434565993571 28204520161433151848990357)
                    ·
                      refine ⟨1322086882567178992921423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28204520161433151848990357 1322086882567178992921423)
                      ·
                        rfl

theorem cell23_2574755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2574755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574755 prefixEnd_2574755 := by exact prefixLift 2574755
  have htrace : WordTrace (prefixWord ++ tailWord_2574755) baseStart_2574755 baseEnd_2574755 := by
    simpa [prefixWord, tailWord_2574755, baseEnd_2574755] using wordTrace_append hprefix tailTrace_2574755
  have hstable : (prefixWord ++ tailWord_2574755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574755).length < 2 ^ (prefixWord ++ tailWord_2574755).sum := by decide
  have hdescent : baseEnd_2574755 < baseStart_2574755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574759 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2574759 : Nat := 118140960795 + 2574759 * 2 ^ 59
def prefixEnd_2574759 : Nat := 4983230072969 + 3 ^ 40 * 2574759 * 2
def baseEnd_2574759 : Nat := 1322088936489796977271405

theorem tailTrace_2574759 : CollatzResearch.WordTrace tailWord_2574759 prefixEnd_2574759 1322088936489796977271405 := by
  unfold tailWord_2574759
  simp only [CollatzResearch.WordTrace]
  refine ⟨93909175679095351673311331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62606117119396901115540887 93909175679095351673311331)
  ·
    refine ⟨140863763518643027509966997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93909175679095351673311331 140863763518643027509966997)
    ·
      refine ⟨6602988914936391914529703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140863763518643027509966997 6602988914936391914529703)
      ·
        refine ⟨9904483372404587871794555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602988914936391914529703 9904483372404587871794555)
        ·
          refine ⟨14856725058606881807691833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904483372404587871794555 14856725058606881807691833)
          ·
            refine ⟨11142543793955161355768875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14856725058606881807691833 11142543793955161355768875)
            ·
              refine ⟨16713815690932742033653313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142543793955161355768875 16713815690932742033653313)
              ·
                refine ⟨12535361768199556525239985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16713815690932742033653313 12535361768199556525239985)
                ·
                  refine ⟨9401521326149667393929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12535361768199556525239985 9401521326149667393929989)
                  ·
                    refine ⟨1762785248653062636361873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9401521326149667393929989 1762785248653062636361873)
                    ·
                      refine ⟨1322088936489796977271405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762785248653062636361873 1322088936489796977271405)
                      ·
                        rfl

theorem cell23_2574759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2574759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574759 prefixEnd_2574759 := by exact prefixLift 2574759
  have htrace : WordTrace (prefixWord ++ tailWord_2574759) baseStart_2574759 baseEnd_2574759 := by
    simpa [prefixWord, tailWord_2574759, baseEnd_2574759] using wordTrace_append hprefix tailTrace_2574759
  have hstable : (prefixWord ++ tailWord_2574759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574759).length < 2 ^ (prefixWord ++ tailWord_2574759).sum := by decide
  have hdescent : baseEnd_2574759 < baseStart_2574759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574769 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2574769 : Nat := 118140960795 + 2574769 * 2 ^ 59
def prefixEnd_2574769 : Nat := 4983230072969 + 3 ^ 40 * 2574769 * 2
def baseEnd_2574769 : Nat := 440698023765447312715453

theorem tailTrace_2574769 : CollatzResearch.WordTrace tailWord_2574769 prefixEnd_2574769 440698023765447312715453 := by
  unfold tailWord_2574769
  simp only [CollatzResearch.WordTrace]
  refine ⟨93909540409059123381175361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62606360272706082254116907 93909540409059123381175361)
  ·
    refine ⟨70432155306794342535881521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93909540409059123381175361 70432155306794342535881521)
    ·
      refine ⟨52824116480095756901911141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70432155306794342535881521 52824116480095756901911141)
      ·
        refine ⟨9904521840017954419108339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52824116480095756901911141 9904521840017954419108339)
        ·
          refine ⟨14856782760026931628662509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904521840017954419108339 14856782760026931628662509)
          ·
            refine ⟨5571293535010099360748441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14856782760026931628662509 5571293535010099360748441)
            ·
              refine ⟨4178470151257574520561331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571293535010099360748441 4178470151257574520561331)
              ·
                refine ⟨6267705226886361780841997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178470151257574520561331 6267705226886361780841997)
                ·
                  refine ⟨2350389460082385667815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6267705226886361780841997 2350389460082385667815749)
                  ·
                    refine ⟨440698023765447312715453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350389460082385667815749 440698023765447312715453)
                    ·
                      rfl

theorem cell23_2574769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2574769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574769 prefixEnd_2574769 := by exact prefixLift 2574769
  have htrace : WordTrace (prefixWord ++ tailWord_2574769) baseStart_2574769 baseEnd_2574769 := by
    simpa [prefixWord, tailWord_2574769, baseEnd_2574769] using wordTrace_append hprefix tailTrace_2574769
  have hstable : (prefixWord ++ tailWord_2574769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574769).length < 2 ^ (prefixWord ++ tailWord_2574769).sum := by decide
  have hdescent : baseEnd_2574769 < baseStart_2574769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574782 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2574782 : Nat := 118140960795 + 2574782 * 2 ^ 59
def prefixEnd_2574782 : Nat := 4983230072969 + 3 ^ 40 * 2574782 * 2
def baseEnd_2574782 : Nat := 146900082949427820809311

theorem tailTrace_2574782 : CollatzResearch.WordTrace tailWord_2574782 prefixEnd_2574782 146900082949427820809311 := by
  unfold tailWord_2574782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738751819751503325174825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62606676372008017734265733 11738751819751503325174825)
  ·
    refine ⟨8804063864813627493881119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11738751819751503325174825 8804063864813627493881119)
    ·
      refine ⟨13206095797220441240821679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804063864813627493881119 13206095797220441240821679)
      ·
        refine ⟨19809143695830661861232519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206095797220441240821679 19809143695830661861232519)
        ·
          refine ⟨29713715543745992791848779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809143695830661861232519 29713715543745992791848779)
          ·
            refine ⟨44570573315618989187773169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29713715543745992791848779 44570573315618989187773169)
            ·
              refine ⟨33427929986714241890829877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44570573315618989187773169 33427929986714241890829877)
              ·
                refine ⟨3133868436254460177265301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33427929986714241890829877 3133868436254460177265301)
                ·
                  refine ⟨146900082949427820809311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3133868436254460177265301 146900082949427820809311)
                  ·
                    rfl

theorem cell23_2574782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2574782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574782 prefixEnd_2574782 := by exact prefixLift 2574782
  have htrace : WordTrace (prefixWord ++ tailWord_2574782) baseStart_2574782 baseEnd_2574782 := by
    simpa [prefixWord, tailWord_2574782, baseEnd_2574782] using wordTrace_append hprefix tailTrace_2574782
  have hstable : (prefixWord ++ tailWord_2574782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574782).length < 2 ^ (prefixWord ++ tailWord_2574782).sum := by decide
  have hdescent : baseEnd_2574782 < baseStart_2574782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574825 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_2574825 : Nat := 118140960795 + 2574825 * 2 ^ 59
def prefixEnd_2574825 : Nat := 4983230072969 + 3 ^ 40 * 2574825 * 2
def baseEnd_2574825 : Nat := 440707608737664573015367

theorem tailTrace_2574825 : CollatzResearch.WordTrace tailWord_2574825 prefixEnd_2574825 440707608737664573015367 := by
  unfold tailWord_2574825
  simp only [CollatzResearch.WordTrace]
  refine ⟨93911582896856244945213929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62607721931237496630142619 93911582896856244945213929)
  ·
    refine ⟨70433687172642183708910447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93911582896856244945213929 70433687172642183708910447)
    ·
      refine ⟨105650530758963275563365671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70433687172642183708910447 105650530758963275563365671)
      ·
        refine ⟨158475796138444913345048507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105650530758963275563365671 158475796138444913345048507)
        ·
          refine ⟨237713694207667370017572761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158475796138444913345048507 237713694207667370017572761)
          ·
            refine ⟨178285270655750527513179571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237713694207667370017572761 178285270655750527513179571)
            ·
              refine ⟨267427905983625791269769357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178285270655750527513179571 267427905983625791269769357)
              ·
                refine ⟨100285464743859671726163509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267427905983625791269769357 100285464743859671726163509)
                ·
                  refine ⟨9401762319736844224327829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100285464743859671726163509 9401762319736844224327829)
                  ·
                    refine ⟨440707608737664573015367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9401762319736844224327829 440707608737664573015367)
                    ·
                      rfl

theorem cell23_2574825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_2574825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574825 prefixEnd_2574825 := by exact prefixLift 2574825
  have htrace : WordTrace (prefixWord ++ tailWord_2574825) baseStart_2574825 baseEnd_2574825 := by
    simpa [prefixWord, tailWord_2574825, baseEnd_2574825] using wordTrace_append hprefix tailTrace_2574825
  have hstable : (prefixWord ++ tailWord_2574825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574825).length < 2 ^ (prefixWord ++ tailWord_2574825).sum := by decide
  have hdescent : baseEnd_2574825 < baseStart_2574825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574826 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2574826 : Nat := 118140960795 + 2574826 * 2 ^ 59
def prefixEnd_2574826 : Nat := 4983230072969 + 3 ^ 40 * 2574826 * 2
def baseEnd_2574826 : Nat := 1322123339693648215133597

theorem tailTrace_2574826 : CollatzResearch.WordTrace tailWord_2574826 prefixEnd_2574826 1322123339693648215133597 := by
  unfold tailWord_2574826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23477904842463155529000083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62607746246568414744000221 23477904842463155529000083)
  ·
    refine ⟨35216857263694733293500125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23477904842463155529000083 35216857263694733293500125)
    ·
      refine ⟨13206321473885524985062547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35216857263694733293500125 13206321473885524985062547)
      ·
        refine ⟨19809482210828287477593821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206321473885524985062547 19809482210828287477593821)
        ·
          refine ⟨7428555829060607804097683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19809482210828287477593821 7428555829060607804097683)
          ·
            refine ⟨11142833743590911706146525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428555829060607804097683 11142833743590911706146525)
            ·
              refine ⟨4178562653846591889804947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11142833743590911706146525 4178562653846591889804947)
              ·
                refine ⟨6267843980769887834707421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178562653846591889804947 6267843980769887834707421)
                ·
                  refine ⟨2350441492788707938015283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6267843980769887834707421 2350441492788707938015283)
                  ·
                    refine ⟨3525662239183061907022925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350441492788707938015283 3525662239183061907022925)
                    ·
                      refine ⟨1322123339693648215133597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525662239183061907022925 1322123339693648215133597)
                      ·
                        rfl

theorem cell23_2574826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2574826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574826 prefixEnd_2574826 := by exact prefixLift 2574826
  have htrace : WordTrace (prefixWord ++ tailWord_2574826) baseStart_2574826 baseEnd_2574826 := by
    simpa [prefixWord, tailWord_2574826, baseEnd_2574826] using wordTrace_append hprefix tailTrace_2574826
  have hstable : (prefixWord ++ tailWord_2574826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574826).length < 2 ^ (prefixWord ++ tailWord_2574826).sum := by decide
  have hdescent : baseEnd_2574826 < baseStart_2574826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574832 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_2574832 : Nat := 118140960795 + 2574832 * 2 ^ 59
def prefixEnd_2574832 : Nat := 4983230072969 + 3 ^ 40 * 2574832 * 2
def baseEnd_2574832 : Nat := 1322126420577575191658569

theorem tailTrace_2574832 : CollatzResearch.WordTrace tailWord_2574832 prefixEnd_2574832 1322126420577575191658569 := by
  unfold tailWord_2574832
  simp only [CollatzResearch.WordTrace]
  refine ⟨46955919103915442570359375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62607892138553923427145833 46955919103915442570359375)
  ·
    refine ⟨70433878655873163855539063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46955919103915442570359375 70433878655873163855539063)
    ·
      refine ⟨105650817983809745783308595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70433878655873163855539063 105650817983809745783308595)
      ·
        refine ⟨158476226975714618674962893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105650817983809745783308595 158476226975714618674962893)
        ·
          refine ⟨59428585115892982003111085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158476226975714618674962893 59428585115892982003111085)
          ·
            refine ⟨22285719418459868251166657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59428585115892982003111085 22285719418459868251166657)
            ·
              refine ⟨16714289563844901188374993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22285719418459868251166657 16714289563844901188374993)
              ·
                refine ⟨12535717172883675891281245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16714289563844901188374993 12535717172883675891281245)
                ·
                  refine ⟨4700893939831378459230467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12535717172883675891281245 4700893939831378459230467)
                  ·
                    refine ⟨7051340909747067688845701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700893939831378459230467 7051340909747067688845701)
                    ·
                      refine ⟨1322126420577575191658569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7051340909747067688845701 1322126420577575191658569)
                      ·
                        rfl

theorem cell23_2574832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_2574832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574832 prefixEnd_2574832 := by exact prefixLift 2574832
  have htrace : WordTrace (prefixWord ++ tailWord_2574832) baseStart_2574832 baseEnd_2574832 := by
    simpa [prefixWord, tailWord_2574832, baseEnd_2574832] using wordTrace_append hprefix tailTrace_2574832
  have hstable : (prefixWord ++ tailWord_2574832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574832).length < 2 ^ (prefixWord ++ tailWord_2574832).sum := by decide
  have hdescent : baseEnd_2574832 < baseStart_2574832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574842 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_2574842 : Nat := 118140960795 + 2574842 * 2 ^ 59
def prefixEnd_2574842 : Nat := 4983230072969 + 3 ^ 40 * 2574842 * 2
def baseEnd_2574842 : Nat := 440710518461373384177841

theorem tailTrace_2574842 : CollatzResearch.WordTrace tailWord_2574842 prefixEnd_2574842 440710518461373384177841 := by
  unfold tailWord_2574842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478050734448664212145695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62608135291863104565721853 23478050734448664212145695)
  ·
    refine ⟨35217076101672996318218543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478050734448664212145695 35217076101672996318218543)
    ·
      refine ⟨52825614152509494477327815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35217076101672996318218543 52825614152509494477327815)
      ·
        refine ⟨79238421228764241715991723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52825614152509494477327815 79238421228764241715991723)
        ·
          refine ⟨118857631843146362573987585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79238421228764241715991723 118857631843146362573987585)
          ·
            refine ⟨89143223882359771930490689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118857631843146362573987585 89143223882359771930490689)
            ·
              refine ⟨66857417911769828947868017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89143223882359771930490689 66857417911769828947868017)
              ·
                refine ⟨50143063433827371710901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66857417911769828947868017 50143063433827371710901013)
                ·
                  refine ⟨2350456098460658048948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50143063433827371710901013 2350456098460658048948485)
                  ·
                    refine ⟨440710518461373384177841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350456098460658048948485 440710518461373384177841)
                    ·
                      rfl

theorem cell23_2574842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_2574842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574842 prefixEnd_2574842 := by exact prefixLift 2574842
  have htrace : WordTrace (prefixWord ++ tailWord_2574842) baseStart_2574842 baseEnd_2574842 := by
    simpa [prefixWord, tailWord_2574842, baseEnd_2574842] using wordTrace_append hprefix tailTrace_2574842
  have hstable : (prefixWord ++ tailWord_2574842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574842).length < 2 ^ (prefixWord ++ tailWord_2574842).sum := by decide
  have hdescent : baseEnd_2574842 < baseStart_2574842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574849 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2574849 : Nat := 118140960795 + 2574849 * 2 ^ 59
def prefixEnd_2574849 : Nat := 4983230072969 + 3 ^ 40 * 2574849 * 2
def baseEnd_2574849 : Nat := 1322135149748701625145991

theorem tailTrace_2574849 : CollatzResearch.WordTrace tailWord_2574849 prefixEnd_2574849 1322135149748701625145991 := by
  unfold tailWord_2574849
  simp only [CollatzResearch.WordTrace]
  refine ⟨93912458248769297044087601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62608305499179531362725067 93912458248769297044087601)
  ·
    refine ⟨70434343686576972783065701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93912458248769297044087601 70434343686576972783065701)
    ·
      refine ⟨13206439441233182396824819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70434343686576972783065701 13206439441233182396824819)
      ·
        refine ⟨19809659161849773595237229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206439441233182396824819 19809659161849773595237229)
        ·
          refine ⟨7428622185693665098213961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19809659161849773595237229 7428622185693665098213961)
          ·
            refine ⟨5571466639270248823660471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428622185693665098213961 5571466639270248823660471)
            ·
              refine ⟨8357199958905373235490707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571466639270248823660471 8357199958905373235490707)
              ·
                refine ⟨12535799938358059853236061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8357199958905373235490707 12535799938358059853236061)
                ·
                  refine ⟨4700924976884272444963523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12535799938358059853236061 4700924976884272444963523)
                  ·
                    refine ⟨7051387465326408667445285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700924976884272444963523 7051387465326408667445285)
                    ·
                      refine ⟨1322135149748701625145991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7051387465326408667445285 1322135149748701625145991)
                      ·
                        rfl

theorem cell23_2574849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2574849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574849 prefixEnd_2574849 := by exact prefixLift 2574849
  have htrace : WordTrace (prefixWord ++ tailWord_2574849) baseStart_2574849 baseEnd_2574849 := by
    simpa [prefixWord, tailWord_2574849, baseEnd_2574849] using wordTrace_append hprefix tailTrace_2574849
  have hstable : (prefixWord ++ tailWord_2574849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574849).length < 2 ^ (prefixWord ++ tailWord_2574849).sum := by decide
  have hdescent : baseEnd_2574849 < baseStart_2574849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574875 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_2574875 : Nat := 118140960795 + 2574875 * 2 ^ 59
def prefixEnd_2574875 : Nat := 4983230072969 + 3 ^ 40 * 2574875 * 2
def baseEnd_2574875 : Nat := 1322148500245718523420871

theorem tailTrace_2574875 : CollatzResearch.WordTrace tailWord_2574875 prefixEnd_2574875 1322148500245718523420871 := by
  unfold tailWord_2574875
  simp only [CollatzResearch.WordTrace]
  refine ⟨93913406546675103484534079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62608937697783402323022719 93913406546675103484534079)
  ·
    refine ⟨140870109820012655226801119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93913406546675103484534079 140870109820012655226801119)
    ·
      refine ⟨211305164730018982840201679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140870109820012655226801119 211305164730018982840201679)
      ·
        refine ⟨316957747095028474260302519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211305164730018982840201679 316957747095028474260302519)
        ·
          refine ⟨475436620642542711390453779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316957747095028474260302519 475436620642542711390453779)
          ·
            refine ⟨713154930963814067085680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475436620642542711390453779 713154930963814067085680669)
            ·
              refine ⟨267433099111430275157130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713154930963814067085680669 267433099111430275157130251)
              ·
                refine ⟨401149648667145412735695377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267433099111430275157130251 401149648667145412735695377)
                ·
                  refine ⟨300862236500359059551771533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401149648667145412735695377 300862236500359059551771533)
                  ·
                    refine ⟨112823338687634647331914325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300862236500359059551771533 112823338687634647331914325)
                    ·
                      refine ⟨1322148500245718523420871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112823338687634647331914325 1322148500245718523420871)
                      ·
                        rfl

theorem cell23_2574875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_2574875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574875 prefixEnd_2574875 := by exact prefixLift 2574875
  have htrace : WordTrace (prefixWord ++ tailWord_2574875) baseStart_2574875 baseEnd_2574875 := by
    simpa [prefixWord, tailWord_2574875, baseEnd_2574875] using wordTrace_append hprefix tailTrace_2574875
  have hstable : (prefixWord ++ tailWord_2574875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574875).length < 2 ^ (prefixWord ++ tailWord_2574875).sum := by decide
  have hdescent : baseEnd_2574875 < baseStart_2574875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574876 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2574876 : Nat := 118140960795 + 2574876 * 2 ^ 59
def prefixEnd_2574876 : Nat := 4983230072969 + 3 ^ 40 * 2574876 * 2
def baseEnd_2574876 : Nat := 440716337908791006502789

theorem tailTrace_2574876 : CollatzResearch.WordTrace tailWord_2574876 prefixEnd_2574876 440716337908791006502789 := by
  unfold tailWord_2574876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956721509835740327660241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62608962013114320436880321 46956721509835740327660241)
  ·
    refine ⟨35217541132376805245745181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46956721509835740327660241 35217541132376805245745181)
    ·
      refine ⟨13206577924641301967154443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35217541132376805245745181 13206577924641301967154443)
      ·
        refine ⟨19809866886961952950731665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206577924641301967154443 19809866886961952950731665)
        ·
          refine ⟨14857400165221464713048749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19809866886961952950731665 14857400165221464713048749)
          ·
            refine ⟨5571525061958049267393281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14857400165221464713048749 5571525061958049267393281)
            ·
              refine ⟨4178643796468536950544961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571525061958049267393281 4178643796468536950544961)
              ·
                refine ⟨3133982847351402712908721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178643796468536950544961 3133982847351402712908721)
                ·
                  refine ⟨2350487135513552034681541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133982847351402712908721 2350487135513552034681541)
                  ·
                    refine ⟨440716337908791006502789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350487135513552034681541 440716337908791006502789)
                    ·
                      rfl

theorem cell23_2574876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2574876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574876 prefixEnd_2574876 := by exact prefixLift 2574876
  have htrace : WordTrace (prefixWord ++ tailWord_2574876) baseStart_2574876 baseEnd_2574876 := by
    simpa [prefixWord, tailWord_2574876, baseEnd_2574876] using wordTrace_append hprefix tailTrace_2574876
  have hstable : (prefixWord ++ tailWord_2574876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574876).length < 2 ^ (prefixWord ++ tailWord_2574876).sum := by decide
  have hdescent : baseEnd_2574876 < baseStart_2574876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574899 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3]
def baseStart_2574899 : Nat := 118140960795 + 2574899 * 2 ^ 59
def prefixEnd_2574899 : Nat := 4983230072969 + 3 ^ 40 * 2574899 * 2
def baseEnd_2574899 : Nat := 1322160823781426429520761

theorem tailTrace_2574899 : CollatzResearch.WordTrace tailWord_2574899 prefixEnd_2574899 1322160823781426429520761 := by
  unfold tailWord_2574899
  simp only [CollatzResearch.WordTrace]
  refine ⟨93914281898588155583407751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62609521265725437055605167 93914281898588155583407751)
  ·
    refine ⟨140871422847882233375111627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93914281898588155583407751 140871422847882233375111627)
    ·
      refine ⟨211307134271823350062667441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140871422847882233375111627 211307134271823350062667441)
      ·
        refine ⟨158480350703867512547000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211307134271823350062667441 158480350703867512547000581)
        ·
          refine ⟨29715065756975158602562609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158480350703867512547000581 29715065756975158602562609)
          ·
            refine ⟨22286299317731368951921957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29715065756975158602562609 22286299317731368951921957)
            ·
              refine ⟨4178681122074631678485367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22286299317731368951921957 4178681122074631678485367)
              ·
                refine ⟨6268021683111947517728051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178681122074631678485367 6268021683111947517728051)
                ·
                  refine ⟨9402032524667921276592077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268021683111947517728051 9402032524667921276592077)
                  ·
                    refine ⟨3525762196750470478722029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9402032524667921276592077 3525762196750470478722029)
                    ·
                      refine ⟨1322160823781426429520761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525762196750470478722029 1322160823781426429520761)
                      ·
                        rfl

theorem cell23_2574899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_2574899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574899 prefixEnd_2574899 := by exact prefixLift 2574899
  have htrace : WordTrace (prefixWord ++ tailWord_2574899) baseStart_2574899 baseEnd_2574899 := by
    simpa [prefixWord, tailWord_2574899, baseEnd_2574899] using wordTrace_append hprefix tailTrace_2574899
  have hstable : (prefixWord ++ tailWord_2574899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574899).length < 2 ^ (prefixWord ++ tailWord_2574899).sum := by decide
  have hdescent : baseEnd_2574899 < baseStart_2574899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574956 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_2574956 : Nat := 118140960795 + 2574956 * 2 ^ 59
def prefixEnd_2574956 : Nat := 4983230072969 + 3 ^ 40 * 2574956 * 2
def baseEnd_2574956 : Nat := 1322190092178732706507999

theorem tailTrace_2574956 : CollatzResearch.WordTrace tailWord_2574956 prefixEnd_2574956 1322190092178732706507999 := by
  unfold tailWord_2574956
  simp only [CollatzResearch.WordTrace]
  refine ⟨46958180429690827159116361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62610907239587769545488481 46958180429690827159116361)
  ·
    refine ⟨35218635322268120369337271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46958180429690827159116361 35218635322268120369337271)
    ·
      refine ⟨52827952983402180554005907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35218635322268120369337271 52827952983402180554005907)
      ·
        refine ⟨79241929475103270831008861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52827952983402180554005907 79241929475103270831008861)
        ·
          refine ⟨29715723553163726561628323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79241929475103270831008861 29715723553163726561628323)
          ·
            refine ⟨44573585329745589842442485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29715723553163726561628323 44573585329745589842442485)
            ·
              refine ⟨4178773624663649047728983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44573585329745589842442485 4178773624663649047728983)
              ·
                refine ⟨6268160436995473571593475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178773624663649047728983 6268160436995473571593475)
                ·
                  refine ⟨9402240655493210357390213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268160436995473571593475 9402240655493210357390213)
                  ·
                    refine ⟨1762920122904976942010665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9402240655493210357390213 1762920122904976942010665)
                    ·
                      refine ⟨1322190092178732706507999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1762920122904976942010665 1322190092178732706507999)
                      ·
                        rfl

theorem cell23_2574956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_2574956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574956 prefixEnd_2574956 := by exact prefixLift 2574956
  have htrace : WordTrace (prefixWord ++ tailWord_2574956) baseStart_2574956 baseEnd_2574956 := by
    simpa [prefixWord, tailWord_2574956, baseEnd_2574956] using wordTrace_append hprefix tailTrace_2574956
  have hstable : (prefixWord ++ tailWord_2574956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574956).length < 2 ^ (prefixWord ++ tailWord_2574956).sum := by decide
  have hdescent : baseEnd_2574956 < baseStart_2574956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574996 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2574996 : Nat := 118140960795 + 2574996 * 2 ^ 59
def prefixEnd_2574996 : Nat := 4983230072969 + 3 ^ 40 * 2574996 * 2
def baseEnd_2574996 : Nat := 146912292378323616667535

theorem tailTrace_2574996 : CollatzResearch.WordTrace tailWord_2574996 prefixEnd_2574996 146912292378323616667535 := by
  unfold tailWord_2574996
  simp only [CollatzResearch.WordTrace]
  refine ⟨46958909889618370574844421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62611879852824494099792561 46958909889618370574844421)
  ·
    refine ⟨8804795604303444482783329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46958909889618370574844421 8804795604303444482783329)
    ·
      refine ⟨6603596703227583362087497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8804795604303444482783329 6603596703227583362087497)
      ·
        refine ⟨4952697527420687521565623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6603596703227583362087497 4952697527420687521565623)
        ·
          refine ⟨7429046291131031282348435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952697527420687521565623 7429046291131031282348435)
          ·
            refine ⟨11143569436696546923522653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429046291131031282348435 11143569436696546923522653)
            ·
              refine ⟨4178838538761205096320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11143569436696546923522653 4178838538761205096320995)
              ·
                refine ⟨6268257808141807644481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178838538761205096320995 6268257808141807644481493)
                ·
                  refine ⟨146912292378323616667535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6268257808141807644481493 146912292378323616667535)
                  ·
                    rfl

theorem cell23_2574996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2574996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2574996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2574996 prefixEnd_2574996 := by exact prefixLift 2574996
  have htrace : WordTrace (prefixWord ++ tailWord_2574996) baseStart_2574996 baseEnd_2574996 := by
    simpa [prefixWord, tailWord_2574996, baseEnd_2574996] using wordTrace_append hprefix tailTrace_2574996
  have hstable : (prefixWord ++ tailWord_2574996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574996).length < 2 ^ (prefixWord ++ tailWord_2574996).sum := by decide
  have hdescent : baseEnd_2574996 < baseStart_2574996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575006 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2575006 : Nat := 118140960795 + 2575006 * 2 ^ 59
def prefixEnd_2575006 : Nat := 4983230072969 + 3 ^ 40 * 2575006 * 2
def baseEnd_2575006 : Nat := 1322215766211457510882769

theorem tailTrace_2575006 : CollatzResearch.WordTrace tailWord_2575006 prefixEnd_2575006 1322215766211457510882769 := by
  unfold tailWord_2575006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739773063650064107194109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62612123006133675238368581 11739773063650064107194109)
  ·
    refine ⟨4402414898868774040197791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11739773063650064107194109 4402414898868774040197791)
    ·
      refine ⟨6603622348303161060296687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4402414898868774040197791 6603622348303161060296687)
      ·
        refine ⟨9905433522454741590445031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603622348303161060296687 9905433522454741590445031)
        ·
          refine ⟨14858150283682112385667547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905433522454741590445031 14858150283682112385667547)
          ·
            refine ⟨22287225425523168578501321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14858150283682112385667547 22287225425523168578501321)
            ·
              refine ⟨16715419069142376433875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22287225425523168578501321 16715419069142376433875991)
              ·
                refine ⟨25073128603713564650813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16715419069142376433875991 25073128603713564650813987)
                ·
                  refine ⟨37609692905570346976220981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25073128603713564650813987 37609692905570346976220981)
                  ·
                    refine ⟨3525908709897220029020717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37609692905570346976220981 3525908709897220029020717)
                    ·
                      refine ⟨1322215766211457510882769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3525908709897220029020717 1322215766211457510882769)
                      ·
                        rfl

theorem cell23_2575006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2575006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575006 prefixEnd_2575006 := by exact prefixLift 2575006
  have htrace : WordTrace (prefixWord ++ tailWord_2575006) baseStart_2575006 baseEnd_2575006 := by
    simpa [prefixWord, tailWord_2575006, baseEnd_2575006] using wordTrace_append hprefix tailTrace_2575006
  have hstable : (prefixWord ++ tailWord_2575006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575006).length < 2 ^ (prefixWord ++ tailWord_2575006).sum := by decide
  have hdescent : baseEnd_2575006 < baseStart_2575006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575032 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2575032 : Nat := 118140960795 + 2575032 * 2 ^ 59
def prefixEnd_2575032 : Nat := 4983230072969 + 3 ^ 40 * 2575032 * 2
def baseEnd_2575032 : Nat := 1322229116708474409157649

theorem tailTrace_2575032 : CollatzResearch.WordTrace tailWord_2575032 prefixEnd_2575032 1322229116708474409157649 := by
  unfold tailWord_2575032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959566403553159648999675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62612755204737546198666233 46959566403553159648999675)
  ·
    refine ⟨70439349605329739473499513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46959566403553159648999675 70439349605329739473499513)
    ·
      refine ⟨52829512203997304605124635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70439349605329739473499513 52829512203997304605124635)
      ·
        refine ⟨79244268305995956907686953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52829512203997304605124635 79244268305995956907686953)
        ·
          refine ⟨59433201229496967680765215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79244268305995956907686953 59433201229496967680765215)
          ·
            refine ⟨89149801844245451521147823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59433201229496967680765215 89149801844245451521147823)
            ·
              refine ⟨133724702766368177281721735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89149801844245451521147823 133724702766368177281721735)
              ·
                refine ⟨200587054149552265922582603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133724702766368177281721735 200587054149552265922582603)
                ·
                  refine ⟨300880581224328398883873905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200587054149552265922582603 300880581224328398883873905)
                  ·
                    refine ⟨225660435918246299162905429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300880581224328398883873905 225660435918246299162905429)
                    ·
                      refine ⟨1322229116708474409157649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 225660435918246299162905429 1322229116708474409157649)
                      ·
                        rfl

theorem cell23_2575032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2575032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575032 prefixEnd_2575032 := by exact prefixLift 2575032
  have htrace : WordTrace (prefixWord ++ tailWord_2575032) baseStart_2575032 baseEnd_2575032 := by
    simpa [prefixWord, tailWord_2575032, baseEnd_2575032] using wordTrace_append hprefix tailTrace_2575032
  have hstable : (prefixWord ++ tailWord_2575032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575032).length < 2 ^ (prefixWord ++ tailWord_2575032).sum := by decide
  have hdescent : baseEnd_2575032 < baseStart_2575032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575080 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2575080 : Nat := 118140960795 + 2575080 * 2 ^ 59
def prefixEnd_2575080 : Nat := 4983230072969 + 3 ^ 40 * 2575080 * 2
def baseEnd_2575080 : Nat := 1322253763779890221357429

theorem tailTrace_2575080 : CollatzResearch.WordTrace tailWord_2575080 prefixEnd_2575080 1322253763779890221357429 := by
  unfold tailWord_2575080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46960441755466211747873347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62613922340621615663831129 46960441755466211747873347)
  ·
    refine ⟨70440662633199317621810021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46960441755466211747873347 70440662633199317621810021)
    ·
      refine ⟨13207624243724872054089379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70440662633199317621810021 13207624243724872054089379)
      ·
        refine ⟨19811436365587308081134069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13207624243724872054089379 19811436365587308081134069)
        ·
          refine ⟨1857322159273810132606319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19811436365587308081134069 1857322159273810132606319)
          ·
            refine ⟨2785983238910715198909479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857322159273810132606319 2785983238910715198909479)
            ·
              refine ⟨4178974858366072798364219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785983238910715198909479 4178974858366072798364219)
              ·
                refine ⟨6268462287549109197546329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178974858366072798364219 6268462287549109197546329)
                ·
                  refine ⟨4701346715661831898159747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6268462287549109197546329 4701346715661831898159747)
                  ·
                    refine ⟨7052020073492747847239621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4701346715661831898159747 7052020073492747847239621)
                    ·
                      refine ⟨1322253763779890221357429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7052020073492747847239621 1322253763779890221357429)
                      ·
                        rfl

theorem cell23_2575080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2575080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575080 prefixEnd_2575080 := by exact prefixLift 2575080
  have htrace : WordTrace (prefixWord ++ tailWord_2575080) baseStart_2575080 baseEnd_2575080 := by
    simpa [prefixWord, tailWord_2575080, baseEnd_2575080] using wordTrace_append hprefix tailTrace_2575080
  have hstable : (prefixWord ++ tailWord_2575080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575080).length < 2 ^ (prefixWord ++ tailWord_2575080).sum := by decide
  have hdescent : baseEnd_2575080 < baseStart_2575080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575090 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_2575090 : Nat := 118140960795 + 2575090 * 2 ^ 59
def prefixEnd_2575090 : Nat := 4983230072969 + 3 ^ 40 * 2575090 * 2
def baseEnd_2575090 : Nat := 440752966195478394077461

theorem tailTrace_2575090 : CollatzResearch.WordTrace tailWord_2575090 prefixEnd_2575090 440752966195478394077461 := by
  unfold tailWord_2575090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23480312060224048800902681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62614165493930796802407149 23480312060224048800902681)
  ·
    refine ⟨17610234045168036600677011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23480312060224048800902681 17610234045168036600677011)
    ·
      refine ⟨26415351067752054901015517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17610234045168036600677011 26415351067752054901015517)
      ·
        refine ⟨9905756650407020587880819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26415351067752054901015517 9905756650407020587880819)
        ·
          refine ⟨14858634975610530881821229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905756650407020587880819 14858634975610530881821229)
          ·
            refine ⟨5571988115853949080682961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14858634975610530881821229 5571988115853949080682961)
            ·
              refine ⟨4178991086890461810512221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571988115853949080682961 4178991086890461810512221)
              ·
                refine ⟨1567121657583923178942083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4178991086890461810512221 1567121657583923178942083)
                ·
                  refine ⟨2350682486375884768413125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567121657583923178942083 2350682486375884768413125)
                  ·
                    refine ⟨440752966195478394077461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350682486375884768413125 440752966195478394077461)
                    ·
                      rfl

theorem cell23_2575090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_2575090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575090 prefixEnd_2575090 := by exact prefixLift 2575090
  have htrace : WordTrace (prefixWord ++ tailWord_2575090) baseStart_2575090 baseEnd_2575090 := by
    simpa [prefixWord, tailWord_2575090, baseEnd_2575090] using wordTrace_append hprefix tailTrace_2575090
  have hstable : (prefixWord ++ tailWord_2575090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575090).length < 2 ^ (prefixWord ++ tailWord_2575090).sum := by decide
  have hdescent : baseEnd_2575090 < baseStart_2575090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575096 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_2575096 : Nat := 118140960795 + 2575096 * 2 ^ 59
def prefixEnd_2575096 : Nat := 4983230072969 + 3 ^ 40 * 2575096 * 2
def baseEnd_2575096 : Nat := 1322261979470362158757355

theorem tailTrace_2575096 : CollatzResearch.WordTrace tailWord_2575096 prefixEnd_2575096 1322261979470362158757355 := by
  unfold tailWord_2575096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46960733539437229114164571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62614311385916305485552761 46960733539437229114164571)
  ·
    refine ⟨70441100309155843671246857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46960733539437229114164571 70441100309155843671246857)
    ·
      refine ⟨52830825231866882753435143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70441100309155843671246857 52830825231866882753435143)
      ·
        refine ⟨79246237847800324130152715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52830825231866882753435143 79246237847800324130152715)
        ·
          refine ⟨118869356771700486195229073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79246237847800324130152715 118869356771700486195229073)
          ·
            refine ⟨89152017578775364646421805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118869356771700486195229073 89152017578775364646421805)
            ·
              refine ⟨33432006592040761742408177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89152017578775364646421805 33432006592040761742408177)
              ·
                refine ⟨25074004944030571306806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33432006592040761742408177 25074004944030571306806133)
                ·
                  refine ⟨2350687963502866060013075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25074004944030571306806133 2350687963502866060013075)
                  ·
                    refine ⟨3526031945254299090019613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350687963502866060013075 3526031945254299090019613)
                    ·
                      refine ⟨1322261979470362158757355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526031945254299090019613 1322261979470362158757355)
                      ·
                        rfl

theorem cell23_2575096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_2575096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575096 prefixEnd_2575096 := by exact prefixLift 2575096
  have htrace : WordTrace (prefixWord ++ tailWord_2575096) baseStart_2575096 baseEnd_2575096 := by
    simpa [prefixWord, tailWord_2575096, baseEnd_2575096] using wordTrace_append hprefix tailTrace_2575096
  have hstable : (prefixWord ++ tailWord_2575096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575096).length < 2 ^ (prefixWord ++ tailWord_2575096).sum := by decide
  have hdescent : baseEnd_2575096 < baseStart_2575096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575106 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2575106 : Nat := 118140960795 + 2575106 * 2 ^ 59
def prefixEnd_2575106 : Nat := 4983230072969 + 3 ^ 40 * 2575106 * 2
def baseEnd_2575106 : Nat := 1322267114276907119632309

theorem tailTrace_2575106 : CollatzResearch.WordTrace tailWord_2575106 prefixEnd_2575106 1322267114276907119632309 := by
  unfold tailWord_2575106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23480457952209557484048293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62614554539225486624128781 23480457952209557484048293)
  ·
    refine ⟨4402585866039292028259055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23480457952209557484048293 4402585866039292028259055)
    ·
      refine ⟨6603878799058938042388583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4402585866039292028259055 6603878799058938042388583)
      ·
        refine ⟨9905818198588407063582875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603878799058938042388583 9905818198588407063582875)
        ·
          refine ⟨14858727297882610595374313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905818198588407063582875 14858727297882610595374313)
          ·
            refine ⟨11144045473411957946530735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14858727297882610595374313 11144045473411957946530735)
            ·
              refine ⟨16716068210117936919796103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11144045473411957946530735 16716068210117936919796103)
              ·
                refine ⟨25074102315176905379694155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16716068210117936919796103 25074102315176905379694155)
                ·
                  refine ⟨37611153472765358069541233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25074102315176905379694155 37611153472765358069541233)
                  ·
                    refine ⟨28208365104574018552155925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37611153472765358069541233 28208365104574018552155925)
                    ·
                      refine ⟨1322267114276907119632309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28208365104574018552155925 1322267114276907119632309)
                      ·
                        rfl

theorem cell23_2575106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2575106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575106 prefixEnd_2575106 := by exact prefixLift 2575106
  have htrace : WordTrace (prefixWord ++ tailWord_2575106) baseStart_2575106 baseEnd_2575106 := by
    simpa [prefixWord, tailWord_2575106, baseEnd_2575106] using wordTrace_append hprefix tailTrace_2575106
  have hstable : (prefixWord ++ tailWord_2575106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575106).length < 2 ^ (prefixWord ++ tailWord_2575106).sum := by decide
  have hdescent : baseEnd_2575106 < baseStart_2575106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575129 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_2575129 : Nat := 118140960795 + 2575129 * 2 ^ 59
def prefixEnd_2575129 : Nat := 4983230072969 + 3 ^ 40 * 2575129 * 2
def baseEnd_2575129 : Nat := 440759641443986843214901

theorem tailTrace_2575129 : CollatzResearch.WordTrace tailWord_2575129 prefixEnd_2575129 440759641443986843214901 := by
  unfold tailWord_2575129
  simp only [CollatzResearch.WordTrace]
  refine ⟨93922670687754904864280441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62615113791836603242853627 93922670687754904864280441)
  ·
    refine ⟨70442003015816178648210331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93922670687754904864280441 70442003015816178648210331)
    ·
      refine ⟨105663004523724267972315497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70442003015816178648210331 105663004523724267972315497)
      ·
        refine ⟨79247253392793200979236623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105663004523724267972315497 79247253392793200979236623)
        ·
          refine ⟨118870880089189801468854935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79247253392793200979236623 118870880089189801468854935)
          ·
            refine ⟨178306320133784702203282403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118870880089189801468854935 178306320133784702203282403)
            ·
              refine ⟨267459480200677053304923605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178306320133784702203282403 267459480200677053304923605)
              ·
                refine ⟨6268581567203368436834147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 267459480200677053304923605 6268581567203368436834147)
                ·
                  refine ⟨9402872350805052655251221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268581567203368436834147 9402872350805052655251221)
                  ·
                    refine ⟨440759641443986843214901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9402872350805052655251221 440759641443986843214901)
                    ·
                      rfl

theorem cell23_2575129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_2575129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575129 prefixEnd_2575129 := by exact prefixLift 2575129
  have htrace : WordTrace (prefixWord ++ tailWord_2575129) baseStart_2575129 baseEnd_2575129 := by
    simpa [prefixWord, tailWord_2575129, baseEnd_2575129] using wordTrace_append hprefix tailTrace_2575129
  have hstable : (prefixWord ++ tailWord_2575129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575129).length < 2 ^ (prefixWord ++ tailWord_2575129).sum := by decide
  have hdescent : baseEnd_2575129 < baseStart_2575129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2575139 : Nat := 118140960795 + 2575139 * 2 ^ 59
def prefixEnd_2575139 : Nat := 4983230072969 + 3 ^ 40 * 2575139 * 2
def baseEnd_2575139 : Nat := 1322284059138505490519657

theorem tailTrace_2575139 : CollatzResearch.WordTrace tailWord_2575139 prefixEnd_2575139 1322284059138505490519657 := by
  unfold tailWord_2575139
  simp only [CollatzResearch.WordTrace]
  refine ⟨93923035417718676572144471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62615356945145784381429647 93923035417718676572144471)
  ·
    refine ⟨140884553126578014858216707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93923035417718676572144471 140884553126578014858216707)
    ·
      refine ⟨211326829689867022287325061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140884553126578014858216707 211326829689867022287325061)
      ·
        refine ⟨39623780566850066678873449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211326829689867022287325061 39623780566850066678873449)
        ·
          refine ⟨29717835425137550009155087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39623780566850066678873449 29717835425137550009155087)
          ·
            refine ⟨44576753137706325013732631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29717835425137550009155087 44576753137706325013732631)
            ·
              refine ⟨66865129706559487520598947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44576753137706325013732631 66865129706559487520598947)
              ·
                refine ⟨100297694559839231280898421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66865129706559487520598947 100297694559839231280898421)
                ·
                  refine ⟨9402908864984927932584227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100297694559839231280898421 9402908864984927932584227)
                  ·
                    refine ⟨14104363297477391898876341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402908864984927932584227 14104363297477391898876341)
                    ·
                      refine ⟨1322284059138505490519657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14104363297477391898876341 1322284059138505490519657)
                      ·
                        rfl

theorem cell23_2575139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2575139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575139 prefixEnd_2575139 := by exact prefixLift 2575139
  have htrace : WordTrace (prefixWord ++ tailWord_2575139) baseStart_2575139 baseEnd_2575139 := by
    simpa [prefixWord, tailWord_2575139, baseEnd_2575139] using wordTrace_append hprefix tailTrace_2575139
  have hstable : (prefixWord ++ tailWord_2575139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575139).length < 2 ^ (prefixWord ++ tailWord_2575139).sum := by decide
  have hdescent : baseEnd_2575139 < baseStart_2575139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575180 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_2575180 : Nat := 118140960795 + 2575180 * 2 ^ 59
def prefixEnd_2575180 : Nat := 4983230072969 + 3 ^ 40 * 2575180 * 2
def baseEnd_2575180 : Nat := 440768370615113276702323

theorem tailTrace_2575180 : CollatzResearch.WordTrace tailWord_2575180 prefixEnd_2575180 440768370615113276702323 := by
  unfold tailWord_2575180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46962265405285070287193497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62616353873713427049591329 46962265405285070287193497)
  ·
    refine ⟨35221699053963802715395123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46962265405285070287193497 35221699053963802715395123)
    ·
      refine ⟨52832548580945704073092685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35221699053963802715395123 52832548580945704073092685)
      ·
        refine ⟨19812205717854639027409757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52832548580945704073092685 19812205717854639027409757)
        ·
          refine ⟨7429577144195489635278659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19812205717854639027409757 7429577144195489635278659)
          ·
            refine ⟨11144365716293234452917989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429577144195489635278659 11144365716293234452917989)
            ·
              refine ⟨2089568571804981459922123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11144365716293234452917989 2089568571804981459922123)
              ·
                refine ⟨3134352857707472189883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089568571804981459922123 3134352857707472189883185)
                ·
                  refine ⟨2350764643280604142412389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134352857707472189883185 2350764643280604142412389)
                  ·
                    refine ⟨440768370615113276702323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350764643280604142412389 440768370615113276702323)
                    ·
                      rfl

theorem cell23_2575180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_2575180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575180 prefixEnd_2575180 := by exact prefixLift 2575180
  have htrace : WordTrace (prefixWord ++ tailWord_2575180) baseStart_2575180 baseEnd_2575180 := by
    simpa [prefixWord, tailWord_2575180, baseEnd_2575180] using wordTrace_append hprefix tailTrace_2575180
  have hstable : (prefixWord ++ tailWord_2575180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575180).length < 2 ^ (prefixWord ++ tailWord_2575180).sum := by decide
  have hdescent : baseEnd_2575180 < baseStart_2575180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575203 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2575203 : Nat := 118140960795 + 2575203 * 2 ^ 59
def prefixEnd_2575203 : Nat := 4983230072969 + 3 ^ 40 * 2575203 * 2
def baseEnd_2575203 : Nat := 1322316921900393240119363

theorem tailTrace_2575203 : CollatzResearch.WordTrace tailWord_2575203 prefixEnd_2575203 1322316921900393240119363 := by
  unfold tailWord_2575203
  simp only [CollatzResearch.WordTrace]
  refine ⟨93925369689486815502474263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62616913126324543668316175 93925369689486815502474263)
  ·
    refine ⟨140888054534230223253711395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93925369689486815502474263 140888054534230223253711395)
    ·
      refine ⟨211332081801345334880567093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140888054534230223253711395 211332081801345334880567093)
      ·
        refine ⟨19812382668876125145053165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211332081801345334880567093 19812382668876125145053165)
        ·
          refine ⟨7429643500828546929394937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19812382668876125145053165 7429643500828546929394937)
          ·
            refine ⟨5572232625621410197046203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7429643500828546929394937 5572232625621410197046203)
            ·
              refine ⟨8358348938432115295569305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572232625621410197046203 8358348938432115295569305)
              ·
                refine ⟨6268761703824086471676979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8358348938432115295569305 6268761703824086471676979)
                ·
                  refine ⟨9403142555736129707515469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268761703824086471676979 9403142555736129707515469)
                  ·
                    refine ⟨3526178458401048640318301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9403142555736129707515469 3526178458401048640318301)
                    ·
                      refine ⟨1322316921900393240119363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526178458401048640318301 1322316921900393240119363)
                      ·
                        rfl

theorem cell23_2575203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2575203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575203 prefixEnd_2575203 := by exact prefixLift 2575203
  have htrace : WordTrace (prefixWord ++ tailWord_2575203) baseStart_2575203 baseEnd_2575203 := by
    simpa [prefixWord, tailWord_2575203, baseEnd_2575203] using wordTrace_append hprefix tailTrace_2575203
  have hstable : (prefixWord ++ tailWord_2575203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575203).length < 2 ^ (prefixWord ++ tailWord_2575203).sum := by decide
  have hdescent : baseEnd_2575203 < baseStart_2575203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575221 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2575221 : Nat := 118140960795 + 2575221 * 2 ^ 59
def prefixEnd_2575221 : Nat := 4983230072969 + 3 ^ 40 * 2575221 * 2
def baseEnd_2575221 : Nat := 1322326164552174169694281

theorem tailTrace_2575221 : CollatzResearch.WordTrace tailWord_2575221 prefixEnd_2575221 1322326164552174169694281 := by
  unfold tailWord_2575221
  simp only [CollatzResearch.WordTrace]
  refine ⟨93926026203421604576629517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62617350802281069717753011 93926026203421604576629517)
  ·
    refine ⟨35222259826283101716236069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93926026203421604576629517 35222259826283101716236069)
    ·
      refine ⟨6604173717428081571794263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35222259826283101716236069 6604173717428081571794263)
      ·
        refine ⟨9906260576142122357691395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604173717428081571794263 9906260576142122357691395)
        ·
          refine ⟨14859390864213183536537093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9906260576142122357691395 14859390864213183536537093)
          ·
            refine ⟨2786135787039971913100705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14859390864213183536537093 2786135787039971913100705)
            ·
              refine ⟨2089601840279978934825529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786135787039971913100705 2089601840279978934825529)
              ·
                refine ⟨1567201380209984201119147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089601840279978934825529 1567201380209984201119147)
                ·
                  refine ⟨2350802070314976301678721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567201380209984201119147 2350802070314976301678721)
                  ·
                    refine ⟨1763101552736232226259041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350802070314976301678721 1763101552736232226259041)
                    ·
                      refine ⟨1322326164552174169694281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763101552736232226259041 1322326164552174169694281)
                      ·
                        rfl

theorem cell23_2575221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2575221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575221 prefixEnd_2575221 := by exact prefixLift 2575221
  have htrace : WordTrace (prefixWord ++ tailWord_2575221) baseStart_2575221 baseEnd_2575221 := by
    simpa [prefixWord, tailWord_2575221, baseEnd_2575221] using wordTrace_append hprefix tailTrace_2575221
  have hstable : (prefixWord ++ tailWord_2575221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575221).length < 2 ^ (prefixWord ++ tailWord_2575221).sum := by decide
  have hdescent : baseEnd_2575221 < baseStart_2575221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575243 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 4, 2]
def baseStart_2575243 : Nat := 118140960795 + 2575243 * 2 ^ 59
def prefixEnd_2575243 : Nat := 4983230072969 + 3 ^ 40 * 2575243 * 2
def baseEnd_2575243 : Nat := 1322337461126573083619179

theorem tailTrace_2575243 : CollatzResearch.WordTrace tailWord_2575243 prefixEnd_2575243 1322337461126573083619179 := by
  unfold tailWord_2575243
  simp only [CollatzResearch.WordTrace]
  refine ⟨93926828609341902333930383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62617885739561268222620255 93926828609341902333930383)
  ·
    refine ⟨140890242914012853500895575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93926828609341902333930383 140890242914012853500895575)
    ·
      refine ⟨211335364371019280251343363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140890242914012853500895575 211335364371019280251343363)
      ·
        refine ⟨317003046556528920377015045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211335364371019280251343363 317003046556528920377015045)
        ·
          refine ⟨59438071229349172570690321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317003046556528920377015045 59438071229349172570690321)
          ·
            refine ⟨44578553422011879428017741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59438071229349172570690321 44578553422011879428017741)
            ·
              refine ⟨16716957533254454785506653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44578553422011879428017741 16716957533254454785506653)
              ·
                refine ⟨6268859074970420544564995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16716957533254454785506653 6268859074970420544564995)
                ·
                  refine ⟨9403288612455630816847493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268859074970420544564995 9403288612455630816847493)
                  ·
                    refine ⟨1763116614835430778158905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9403288612455630816847493 1763116614835430778158905)
                    ·
                      refine ⟨1322337461126573083619179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763116614835430778158905 1322337461126573083619179)
                      ·
                        rfl

theorem cell23_2575243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4, 2].length) (baseStart_2575243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575243 prefixEnd_2575243 := by exact prefixLift 2575243
  have htrace : WordTrace (prefixWord ++ tailWord_2575243) baseStart_2575243 baseEnd_2575243 := by
    simpa [prefixWord, tailWord_2575243, baseEnd_2575243] using wordTrace_append hprefix tailTrace_2575243
  have hstable : (prefixWord ++ tailWord_2575243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575243).length < 2 ^ (prefixWord ++ tailWord_2575243).sum := by decide
  have hdescent : baseEnd_2575243 < baseStart_2575243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575276 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2575276 : Nat := 118140960795 + 2575276 * 2 ^ 59
def prefixEnd_2575276 : Nat := 4983230072969 + 3 ^ 40 * 2575276 * 2
def baseEnd_2575276 : Nat := 1322354405988171454506527

theorem tailTrace_2575276 : CollatzResearch.WordTrace tailWord_2575276 prefixEnd_2575276 1322354405988171454506527 := by
  unfold tailWord_2575276
  simp only [CollatzResearch.WordTrace]
  refine ⟨46964016109111174484940841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62618688145481565979921121 46964016109111174484940841)
  ·
    refine ⟨35223012081833380863705631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46964016109111174484940841 35223012081833380863705631)
    ·
      refine ⟨52834518122750071295558447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35223012081833380863705631 52834518122750071295558447)
      ·
        refine ⟨79251777184125106943337671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52834518122750071295558447 79251777184125106943337671)
        ·
          refine ⟨118877665776187660415006507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79251777184125106943337671 118877665776187660415006507)
          ·
            refine ⟨178316498664281490622509761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118877665776187660415006507 178316498664281490622509761)
            ·
              refine ⟨133737373998211117966882321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178316498664281490622509761 133737373998211117966882321)
              ·
                refine ⟨100303030498658338475161741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133737373998211117966882321 100303030498658338475161741)
                ·
                  refine ⟨37613636436996876928185653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100303030498658338475161741 37613636436996876928185653)
                  ·
                    refine ⟨3526278415968457212017405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37613636436996876928185653 3526278415968457212017405)
                    ·
                      refine ⟨1322354405988171454506527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526278415968457212017405 1322354405988171454506527)
                      ·
                        rfl

theorem cell23_2575276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2575276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575276 prefixEnd_2575276 := by exact prefixLift 2575276
  have htrace : WordTrace (prefixWord ++ tailWord_2575276) baseStart_2575276 baseEnd_2575276 := by
    simpa [prefixWord, tailWord_2575276, baseEnd_2575276] using wordTrace_append hprefix tailTrace_2575276
  have hstable : (prefixWord ++ tailWord_2575276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575276).length < 2 ^ (prefixWord ++ tailWord_2575276).sum := by decide
  have hdescent : baseEnd_2575276 < baseStart_2575276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575294 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_2575294 : Nat := 118140960795 + 2575294 * 2 ^ 59
def prefixEnd_2575294 : Nat := 4983230072969 + 3 ^ 40 * 2575294 * 2
def baseEnd_2575294 : Nat := 1322363648639952384081445

theorem tailTrace_2575294 : CollatzResearch.WordTrace tailWord_2575294 prefixEnd_2575294 1322363648639952384081445 := by
  unfold tailWord_2575294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741086091519642255504617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62619125821438092029357957 11741086091519642255504617)
  ·
    refine ⟨8805814568639731691628463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11741086091519642255504617 8805814568639731691628463)
    ·
      refine ⟨13208721852959597537442695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8805814568639731691628463 13208721852959597537442695)
      ·
        refine ⟨19813082779439396306164043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13208721852959597537442695 19813082779439396306164043)
        ·
          refine ⟨29719624169159094459246065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19813082779439396306164043 29719624169159094459246065)
          ·
            refine ⟨22289718126869320844434549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29719624169159094459246065 22289718126869320844434549)
            ·
              refine ⟨2089661074393998829165739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22289718126869320844434549 2089661074393998829165739)
              ·
                refine ⟨3134491611590998243748609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089661074393998829165739 3134491611590998243748609)
                ·
                  refine ⟨2350868708693248682811457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134491611590998243748609 2350868708693248682811457)
                  ·
                    refine ⟨1763151531519936512108593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350868708693248682811457 1763151531519936512108593)
                    ·
                      refine ⟨1322363648639952384081445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763151531519936512108593 1322363648639952384081445)
                      ·
                        rfl

theorem cell23_2575294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_2575294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575294 prefixEnd_2575294 := by exact prefixLift 2575294
  have htrace : WordTrace (prefixWord ++ tailWord_2575294) baseStart_2575294 baseEnd_2575294 := by
    simpa [prefixWord, tailWord_2575294, baseEnd_2575294] using wordTrace_append hprefix tailTrace_2575294
  have hstable : (prefixWord ++ tailWord_2575294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575294).length < 2 ^ (prefixWord ++ tailWord_2575294).sum := by decide
  have hdescent : baseEnd_2575294 < baseStart_2575294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575296 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_2575296 : Nat := 118140960795 + 2575296 * 2 ^ 59
def prefixEnd_2575296 : Nat := 4983230072969 + 3 ^ 40 * 2575296 * 2
def baseEnd_2575296 : Nat := 440788225200420458752145

theorem tailTrace_2575296 : CollatzResearch.WordTrace tailWord_2575296 prefixEnd_2575296 440788225200420458752145 := by
  unfold tailWord_2575296
  simp only [CollatzResearch.WordTrace]
  refine ⟨46964380839074946192804871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62619174452099928257073161 46964380839074946192804871)
  ·
    refine ⟨70446571258612419289207307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46964380839074946192804871 70446571258612419289207307)
    ·
      refine ⟨105669856887918628933810961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70446571258612419289207307 105669856887918628933810961)
      ·
        refine ⟨79252392665938971700358221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105669856887918628933810961 79252392665938971700358221)
        ·
          refine ⟨29719647249727114387634333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79252392665938971700358221 29719647249727114387634333)
          ·
            refine ⟨11144867718647667895362875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29719647249727114387634333 11144867718647667895362875)
            ·
              refine ⟨16717301577971501843044313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11144867718647667895362875 16717301577971501843044313)
              ·
                refine ⟨12537976183478626382283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16717301577971501843044313 12537976183478626382283235)
                ·
                  refine ⟨18806964275217939573424853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12537976183478626382283235 18806964275217939573424853)
                  ·
                    refine ⟨440788225200420458752145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18806964275217939573424853 440788225200420458752145)
                    ·
                      rfl

theorem cell23_2575296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_2575296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575296 prefixEnd_2575296 := by exact prefixLift 2575296
  have htrace : WordTrace (prefixWord ++ tailWord_2575296) baseStart_2575296 baseEnd_2575296 := by
    simpa [prefixWord, tailWord_2575296, baseEnd_2575296] using wordTrace_append hprefix tailTrace_2575296
  have hstable : (prefixWord ++ tailWord_2575296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575296).length < 2 ^ (prefixWord ++ tailWord_2575296).sum := by decide
  have hdescent : baseEnd_2575296 < baseStart_2575296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575303 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_2575303 : Nat := 118140960795 + 2575303 * 2 ^ 59
def prefixEnd_2575303 : Nat := 4983230072969 + 3 ^ 40 * 2575303 * 2
def baseEnd_2575303 : Nat := 1322368269965842848868903

theorem tailTrace_2575303 : CollatzResearch.WordTrace tailWord_2575303 prefixEnd_2575303 1322368269965842848868903 := by
  unfold tailWord_2575303
  simp only [CollatzResearch.WordTrace]
  refine ⟨93929016989124532581114563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62619344659416355054076375 93929016989124532581114563)
  ·
    refine ⟨140893525483686798871671845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93929016989124532581114563 140893525483686798871671845)
    ·
      refine ⟨26417536028191274788438471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140893525483686798871671845 26417536028191274788438471)
      ·
        refine ⟨39626304042286912182657707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26417536028191274788438471 39626304042286912182657707)
        ·
          refine ⟨59439456063430368273986561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39626304042286912182657707 59439456063430368273986561)
          ·
            refine ⟨44579592047572776205489921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59439456063430368273986561 44579592047572776205489921)
            ·
              refine ⟨33434694035679582154117441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44579592047572776205489921 33434694035679582154117441)
              ·
                refine ⟨25076020526759686615588081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33434694035679582154117441 25076020526759686615588081)
                ·
                  refine ⟨18807015395069764961691061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25076020526759686615588081 18807015395069764961691061)
                  ·
                    refine ⟨1763157693287790465158537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18807015395069764961691061 1763157693287790465158537)
                    ·
                      refine ⟨1322368269965842848868903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763157693287790465158537 1322368269965842848868903)
                      ·
                        rfl

theorem cell23_2575303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_2575303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575303 prefixEnd_2575303 := by exact prefixLift 2575303
  have htrace : WordTrace (prefixWord ++ tailWord_2575303) baseStart_2575303 baseEnd_2575303 := by
    simpa [prefixWord, tailWord_2575303, baseEnd_2575303] using wordTrace_append hprefix tailTrace_2575303
  have hstable : (prefixWord ++ tailWord_2575303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575303).length < 2 ^ (prefixWord ++ tailWord_2575303).sum := by decide
  have hdescent : baseEnd_2575303 < baseStart_2575303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575306 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_2575306 : Nat := 118140960795 + 2575306 * 2 ^ 59
def prefixEnd_2575306 : Nat := 4983230072969 + 3 ^ 40 * 2575306 * 2
def baseEnd_2575306 : Nat := 1322369810407806337131389

theorem tailTrace_2575306 : CollatzResearch.WordTrace tailWord_2575306 prefixEnd_2575306 1322369810407806337131389 := by
  unfold tailWord_2575306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23482281602028416023368443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62619417605409109395649181 23482281602028416023368443)
  ·
    refine ⟨35223422403042624035052665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23482281602028416023368443 35223422403042624035052665)
    ·
      refine ⟨26417566802281968026289499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35223422403042624035052665 26417566802281968026289499)
      ·
        refine ⟨39626350203422952039434249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26417566802281968026289499 39626350203422952039434249)
        ·
          refine ⟨29719762652567214029575687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39626350203422952039434249 29719762652567214029575687)
          ·
            refine ⟨44579643978850821044363531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29719762652567214029575687 44579643978850821044363531)
            ·
              refine ⟨66869465968276231566545297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44579643978850821044363531 66869465968276231566545297)
              ·
                refine ⟨50152099476207173674908973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66869465968276231566545297 50152099476207173674908973)
                ·
                  refine ⟨18807037303577690128090865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50152099476207173674908973 18807037303577690128090865)
                  ·
                    refine ⟨14105277977683267596068149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18807037303577690128090865 14105277977683267596068149)
                    ·
                      refine ⟨1322369810407806337131389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14105277977683267596068149 1322369810407806337131389)
                      ·
                        rfl

theorem cell23_2575306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_2575306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575306 prefixEnd_2575306 := by exact prefixLift 2575306
  have htrace : WordTrace (prefixWord ++ tailWord_2575306) baseStart_2575306 baseEnd_2575306 := by
    simpa [prefixWord, tailWord_2575306, baseEnd_2575306] using wordTrace_append hprefix tailTrace_2575306
  have hstable : (prefixWord ++ tailWord_2575306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575306).length < 2 ^ (prefixWord ++ tailWord_2575306).sum := by decide
  have hdescent : baseEnd_2575306 < baseStart_2575306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575317 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 5]
def baseStart_2575317 : Nat := 118140960795 + 2575317 * 2 ^ 59
def prefixEnd_2575317 : Nat := 4983230072969 + 3 ^ 40 * 2575317 * 2
def baseEnd_2575317 : Nat := 146930606521667310454871

theorem tailTrace_2575317 : CollatzResearch.WordTrace tailWord_2575317 prefixEnd_2575317 146930606521667310454871 := by
  unfold tailWord_2575317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93929527611073812972124205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62619685074049208648082803 93929527611073812972124205)
  ·
    refine ⟨35223572854152679864546577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93929527611073812972124205 35223572854152679864546577)
    ·
      refine ⟨26417679640614509898409933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35223572854152679864546577 26417679640614509898409933)
      ·
        refine ⟨9906629865230441211903725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26417679640614509898409933 9906629865230441211903725)
        ·
          refine ⟨3714986199461415454463897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9906629865230441211903725 3714986199461415454463897)
          ·
            refine ⟨2786239649596061590847923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3714986199461415454463897 2786239649596061590847923)
            ·
              refine ⟨4179359474394092386271885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786239649596061590847923 4179359474394092386271885)
              ·
                refine ⟨1567259802897784644851957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4179359474394092386271885 1567259802897784644851957)
                ·
                  refine ⟨146930606521667310454871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567259802897784644851957 146930606521667310454871)
                  ·
                    rfl

theorem cell23_2575317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_2575317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575317 prefixEnd_2575317 := by exact prefixLift 2575317
  have htrace : WordTrace (prefixWord ++ tailWord_2575317) baseStart_2575317 baseEnd_2575317 := by
    simpa [prefixWord, tailWord_2575317, baseEnd_2575317] using wordTrace_append hprefix tailTrace_2575317
  have hstable : (prefixWord ++ tailWord_2575317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575317).length < 2 ^ (prefixWord ++ tailWord_2575317).sum := by decide
  have hdescent : baseEnd_2575317 < baseStart_2575317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575330 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2575330 : Nat := 118140960795 + 2575330 * 2 ^ 59
def prefixEnd_2575330 : Nat := 4983230072969 + 3 ^ 40 * 2575330 * 2
def baseEnd_2575330 : Nat := 440794044647838081077093

theorem tailTrace_2575330 : CollatzResearch.WordTrace tailWord_2575330 prefixEnd_2575330 440794044647838081077093 := by
  unfold tailWord_2575330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23482500440006679048086861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62620001173351144128231629 23482500440006679048086861)
  ·
    refine ⟨8805937665002504643032573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23482500440006679048086861 8805937665002504643032573)
    ·
      refine ⟨3302226624375939241137215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8805937665002504643032573 3302226624375939241137215)
      ·
        refine ⟨4953339936563908861705823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302226624375939241137215 4953339936563908861705823)
        ·
          refine ⟨7430009904845863292558735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953339936563908861705823 7430009904845863292558735)
          ·
            refine ⟨11145014857268794938838103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7430009904845863292558735 11145014857268794938838103)
            ·
              refine ⟨16717522285903192408257155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145014857268794938838103 16717522285903192408257155)
              ·
                refine ⟨25076283428854788612385733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16717522285903192408257155 25076283428854788612385733)
                ·
                  refine ⟨4701803142910272864822325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25076283428854788612385733 4701803142910272864822325)
                  ·
                    refine ⟨440794044647838081077093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4701803142910272864822325 440794044647838081077093)
                    ·
                      rfl

theorem cell23_2575330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2575330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575330 prefixEnd_2575330 := by exact prefixLift 2575330
  have htrace : WordTrace (prefixWord ++ tailWord_2575330) baseStart_2575330 baseEnd_2575330 := by
    simpa [prefixWord, tailWord_2575330, baseEnd_2575330] using wordTrace_append hprefix tailTrace_2575330
  have hstable : (prefixWord ++ tailWord_2575330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575330).length < 2 ^ (prefixWord ++ tailWord_2575330).sum := by decide
  have hdescent : baseEnd_2575330 < baseStart_2575330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575353 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2575353 : Nat := 118140960795 + 2575353 * 2 ^ 59
def prefixEnd_2575353 : Nat := 4983230072969 + 3 ^ 40 * 2575353 * 2
def baseEnd_2575353 : Nat := 1322393943998567653243673

theorem tailTrace_2575353 : CollatzResearch.WordTrace tailWord_2575353 prefixEnd_2575353 1322393943998567653243673 := by
  unfold tailWord_2575353
  simp only [CollatzResearch.WordTrace]
  refine ⟨93930840638943391120434713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62620560425962260746956475 93930840638943391120434713)
  ·
    refine ⟨70448130479207543340326035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93930840638943391120434713 70448130479207543340326035)
    ·
      refine ⟨105672195718811315010489053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70448130479207543340326035 105672195718811315010489053)
      ·
        refine ⟨39627073394554243128933395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105672195718811315010489053 39627073394554243128933395)
        ·
          refine ⟨59440610091831364693400093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39627073394554243128933395 59440610091831364693400093)
          ·
            refine ⟨22290228784436761760025035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59440610091831364693400093 22290228784436761760025035)
            ·
              refine ⟨33435343176655142640037553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22290228784436761760025035 33435343176655142640037553)
              ·
                refine ⟨25076507382491356980028165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33435343176655142640037553 25076507382491356980028165)
                ·
                  refine ⟨4701845134217129433755281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25076507382491356980028165 4701845134217129433755281)
                  ·
                    refine ⟨3526383850662847075316461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4701845134217129433755281 3526383850662847075316461)
                    ·
                      refine ⟨1322393943998567653243673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526383850662847075316461 1322393943998567653243673)
                      ·
                        rfl

theorem cell23_2575353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2575353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575353 prefixEnd_2575353 := by exact prefixLift 2575353
  have htrace : WordTrace (prefixWord ++ tailWord_2575353) baseStart_2575353 baseEnd_2575353 := by
    simpa [prefixWord, tailWord_2575353, baseEnd_2575353] using wordTrace_append hprefix tailTrace_2575353
  have hstable : (prefixWord ++ tailWord_2575353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575353).length < 2 ^ (prefixWord ++ tailWord_2575353).sum := by decide
  have hdescent : baseEnd_2575353 < baseStart_2575353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575370 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2575370 : Nat := 118140960795 + 2575370 * 2 ^ 59
def prefixEnd_2575370 : Nat := 4983230072969 + 3 ^ 40 * 2575370 * 2
def baseEnd_2575370 : Nat := 1322402673169694086731095

theorem tailTrace_2575370 : CollatzResearch.WordTrace tailWord_2575370 prefixEnd_2575370 1322402673169694086731095 := by
  unfold tailWord_2575370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23482865169970450755950891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62620973786587868682535709 23482865169970450755950891)
  ·
    refine ⟨35224297754955676133926337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23482865169970450755950891 35224297754955676133926337)
    ·
      refine ⟨26418223316216757100444753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35224297754955676133926337 26418223316216757100444753)
      ·
        refine ⟨19813667487162567825333565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26418223316216757100444753 19813667487162567825333565)
        ·
          refine ⟨7430125307685962934500087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19813667487162567825333565 7430125307685962934500087)
          ·
            refine ⟨11145187961528944401750131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7430125307685962934500087 11145187961528944401750131)
            ·
              refine ⟨16717781942293416602625197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145187961528944401750131 16717781942293416602625197)
              ·
                refine ⟨6269168228360031225984449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16717781942293416602625197 6269168228360031225984449)
                ·
                  refine ⟨4701876171270023419488337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6269168228360031225984449 4701876171270023419488337)
                  ·
                    refine ⟨3526407128452517564616253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4701876171270023419488337 3526407128452517564616253)
                    ·
                      refine ⟨1322402673169694086731095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526407128452517564616253 1322402673169694086731095)
                      ·
                        rfl

theorem cell23_2575370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2575370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575370 prefixEnd_2575370 := by exact prefixLift 2575370
  have htrace : WordTrace (prefixWord ++ tailWord_2575370) baseStart_2575370 baseEnd_2575370 := by
    simpa [prefixWord, tailWord_2575370, baseEnd_2575370] using wordTrace_append hprefix tailTrace_2575370
  have hstable : (prefixWord ++ tailWord_2575370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575370).length < 2 ^ (prefixWord ++ tailWord_2575370).sum := by decide
  have hdescent : baseEnd_2575370 < baseStart_2575370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575394 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2575394 : Nat := 118140960795 + 2575394 * 2 ^ 59
def prefixEnd_2575394 : Nat := 4983230072969 + 3 ^ 40 * 2575394 * 2
def baseEnd_2575394 : Nat := 440804998901800664276995

theorem tailTrace_2575394 : CollatzResearch.WordTrace tailWord_2575394 prefixEnd_2575394 440804998901800664276995 := by
  unfold tailWord_2575394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23483084007948713780669309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62621557354529903415118157 23483084007948713780669309)
  ·
    refine ⟨8806156502980767667750991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23483084007948713780669309 8806156502980767667750991)
    ·
      refine ⟨13209234754471151501626487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8806156502980767667750991 13209234754471151501626487)
      ·
        refine ⟨19813852131706727252439731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13209234754471151501626487 19813852131706727252439731)
        ·
          refine ⟨29720778197560090878659597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19813852131706727252439731 29720778197560090878659597)
          ·
            refine ⟨11145291824085034079497349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29720778197560090878659597 11145291824085034079497349)
            ·
              refine ⟨2089742217015943889905753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11145291824085034079497349 2089742217015943889905753)
              ·
                refine ⟨1567306662761957917429315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089742217015943889905753 1567306662761957917429315)
                ·
                  refine ⟨2350959994142936876143973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567306662761957917429315 2350959994142936876143973)
                  ·
                    refine ⟨440804998901800664276995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350959994142936876143973 440804998901800664276995)
                    ·
                      rfl

theorem cell23_2575394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2575394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575394 prefixEnd_2575394 := by exact prefixLift 2575394
  have htrace : WordTrace (prefixWord ++ tailWord_2575394) baseStart_2575394 baseEnd_2575394 := by
    simpa [prefixWord, tailWord_2575394, baseEnd_2575394] using wordTrace_append hprefix tailTrace_2575394
  have hstable : (prefixWord ++ tailWord_2575394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575394).length < 2 ^ (prefixWord ++ tailWord_2575394).sum := by decide
  have hdescent : baseEnd_2575394 < baseStart_2575394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575410 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_2575410 : Nat := 118140960795 + 2575410 * 2 ^ 59
def prefixEnd_2575410 : Nat := 4983230072969 + 3 ^ 40 * 2575410 * 2
def baseEnd_2575410 : Nat := 1322423212395873930230911

theorem tailTrace_2575410 : CollatzResearch.WordTrace tailWord_2575410 prefixEnd_2575410 1322423212395873930230911 := by
  unfold tailWord_2575410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23483229899934222463814921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62621946399824593236839789 23483229899934222463814921)
  ·
    refine ⟨17612422424950666847861191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23483229899934222463814921 17612422424950666847861191)
    ·
      refine ⟨26418633637426000271791787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17612422424950666847861191 26418633637426000271791787)
      ·
        refine ⟨39627950456139000407687681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26418633637426000271791787 39627950456139000407687681)
        ·
          refine ⟨29720962842104250305765761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39627950456139000407687681 29720962842104250305765761)
          ·
            refine ⟨22290722131578187729324321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29720962842104250305765761 22290722131578187729324321)
            ·
              refine ⟨16718041598683640796993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22290722131578187729324321 16718041598683640796993241)
              ·
                refine ⟨12538531199012730597744931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16718041598683640796993241 12538531199012730597744931)
                ·
                  refine ⟨18807796798519095896617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12538531199012730597744931 18807796798519095896617397)
                  ·
                    refine ⟨1763230949861165240307881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18807796798519095896617397 1763230949861165240307881)
                    ·
                      refine ⟨1322423212395873930230911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763230949861165240307881 1322423212395873930230911)
                      ·
                        rfl

theorem cell23_2575410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_2575410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575410 prefixEnd_2575410 := by exact prefixLift 2575410
  have htrace : WordTrace (prefixWord ++ tailWord_2575410) baseStart_2575410 baseEnd_2575410 := by
    simpa [prefixWord, tailWord_2575410, baseEnd_2575410] using wordTrace_append hprefix tailTrace_2575410
  have hstable : (prefixWord ++ tailWord_2575410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575410).length < 2 ^ (prefixWord ++ tailWord_2575410).sum := by decide
  have hdescent : baseEnd_2575410 < baseStart_2575410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575417 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2575417 : Nat := 118140960795 + 2575417 * 2 ^ 59
def prefixEnd_2575417 : Nat := 4983230072969 + 3 ^ 40 * 2575417 * 2
def baseEnd_2575417 : Nat := 1322426806760455402843379

theorem tailTrace_2575417 : CollatzResearch.WordTrace tailWord_2575417 prefixEnd_2575417 1322426806760455402843379 := by
  unfold tailWord_2575417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93933174910711530050764505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62622116607141020033843003 93933174910711530050764505)
  ·
    refine ⟨70449881183033647538073379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93933174910711530050764505 70449881183033647538073379)
    ·
      refine ⟨105674821774550471307110069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70449881183033647538073379 105674821774550471307110069)
      ·
        refine ⟨9907014541364106685041569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105674821774550471307110069 9907014541364106685041569)
        ·
          refine ⟨7430260906023080013781177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9907014541364106685041569 7430260906023080013781177)
          ·
            refine ⟨5572695679517310010335883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7430260906023080013781177 5572695679517310010335883)
            ·
              refine ⟨8359043519275965015503825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572695679517310010335883 8359043519275965015503825)
              ·
                refine ⟨6269282639456973761627869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8359043519275965015503825 6269282639456973761627869)
                ·
                  refine ⟨2350980989796365160610451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6269282639456973761627869 2350980989796365160610451)
                  ·
                    refine ⟨3526471484694547740915677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350980989796365160610451 3526471484694547740915677)
                    ·
                      refine ⟨1322426806760455402843379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526471484694547740915677 1322426806760455402843379)
                      ·
                        rfl

theorem cell23_2575417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2575417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575417 prefixEnd_2575417 := by exact prefixLift 2575417
  have htrace : WordTrace (prefixWord ++ tailWord_2575417) baseStart_2575417 baseEnd_2575417 := by
    simpa [prefixWord, tailWord_2575417, baseEnd_2575417] using wordTrace_append hprefix tailTrace_2575417
  have hstable : (prefixWord ++ tailWord_2575417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575417).length < 2 ^ (prefixWord ++ tailWord_2575417).sum := by decide
  have hdescent : baseEnd_2575417 < baseStart_2575417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575437 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2575437 : Nat := 118140960795 + 2575437 * 2 ^ 59
def prefixEnd_2575437 : Nat := 4983230072969 + 3 ^ 40 * 2575437 * 2
def baseEnd_2575437 : Nat := 440812358791181774864429

theorem tailTrace_2575437 : CollatzResearch.WordTrace tailWord_2575437 prefixEnd_2575437 440812358791181774864429 := by
  unfold tailWord_2575437
  simp only [CollatzResearch.WordTrace]
  refine ⟨93933904370639073466492565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62622602913759382310995043 93933904370639073466492565)
  ·
    refine ⟨4403151767373706568741839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93933904370639073466492565 4403151767373706568741839)
    ·
      refine ⟨6604727651060559853112759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403151767373706568741839 6604727651060559853112759)
      ·
        refine ⟨9907091476590839779669139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604727651060559853112759 9907091476590839779669139)
        ·
          refine ⟨14860637214886259669503709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907091476590839779669139 14860637214886259669503709)
          ·
            refine ⟨5572738955582347376063891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14860637214886259669503709 5572738955582347376063891)
            ·
              refine ⟨8359108433373521064095837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572738955582347376063891 8359108433373521064095837)
              ·
                refine ⟨3134665662515070399035939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8359108433373521064095837 3134665662515070399035939)
                ·
                  refine ⟨4701998493772605598553909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134665662515070399035939 4701998493772605598553909)
                  ·
                    refine ⟨440812358791181774864429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4701998493772605598553909 440812358791181774864429)
                    ·
                      rfl

theorem cell23_2575437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2575437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575437 prefixEnd_2575437 := by exact prefixLift 2575437
  have htrace : WordTrace (prefixWord ++ tailWord_2575437) baseStart_2575437 baseEnd_2575437 := by
    simpa [prefixWord, tailWord_2575437, baseEnd_2575437] using wordTrace_append hprefix tailTrace_2575437
  have hstable : (prefixWord ++ tailWord_2575437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575437).length < 2 ^ (prefixWord ++ tailWord_2575437).sum := by decide
  have hdescent : baseEnd_2575437 < baseStart_2575437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575450 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_2575450 : Nat := 118140960795 + 2575450 * 2 ^ 59
def prefixEnd_2575450 : Nat := 4983230072969 + 3 ^ 40 * 2575450 * 2
def baseEnd_2575450 : Nat := 440814583874017924576909

theorem tailTrace_2575450 : CollatzResearch.WordTrace tailWord_2575450 prefixEnd_2575450 440814583874017924576909 := by
  unfold tailWord_2575450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23483594629897994171678951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62622919013061317791143869 23483594629897994171678951)
  ·
    refine ⟨35225391944846991257518427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23483594629897994171678951 35225391944846991257518427)
    ·
      refine ⟨52838087917270486886277641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35225391944846991257518427 52838087917270486886277641)
      ·
        refine ⟨39628565937952865164708231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52838087917270486886277641 39628565937952865164708231)
        ·
          refine ⟨59442848906929297747062347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39628565937952865164708231 59442848906929297747062347)
          ·
            refine ⟨89164273360393946620593521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59442848906929297747062347 89164273360393946620593521)
            ·
              refine ⟨66873205020295459965445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89164273360393946620593521 66873205020295459965445141)
              ·
                refine ⟨3134681485326349685880241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66873205020295459965445141 3134681485326349685880241)
                ·
                  refine ⟨2351011113994762264410181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134681485326349685880241 2351011113994762264410181)
                  ·
                    refine ⟨440814583874017924576909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351011113994762264410181 440814583874017924576909)
                    ·
                      rfl

theorem cell23_2575450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_2575450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575450 prefixEnd_2575450 := by exact prefixLift 2575450
  have htrace : WordTrace (prefixWord ++ tailWord_2575450) baseStart_2575450 baseEnd_2575450 := by
    simpa [prefixWord, tailWord_2575450, baseEnd_2575450] using wordTrace_append hprefix tailTrace_2575450
  have hstable : (prefixWord ++ tailWord_2575450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575450).length < 2 ^ (prefixWord ++ tailWord_2575450).sum := by decide
  have hdescent : baseEnd_2575450 < baseStart_2575450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575457 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_2575457 : Nat := 118140960795 + 2575457 * 2 ^ 59
def prefixEnd_2575457 : Nat := 4983230072969 + 3 ^ 40 * 2575457 * 2
def baseEnd_2575457 : Nat := 1322447345986635246343195

theorem tailTrace_2575457 : CollatzResearch.WordTrace tailWord_2575457 prefixEnd_2575457 1322447345986635246343195 := by
  unfold tailWord_2575457
  simp only [CollatzResearch.WordTrace]
  refine ⟨93934633830566616882220625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62623089220377744588147083 93934633830566616882220625)
  ·
    refine ⟨70450975372924962661665469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93934633830566616882220625 70450975372924962661665469)
    ·
      refine ⟨26419115764846860998124551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70450975372924962661665469 26419115764846860998124551)
      ·
        refine ⟨39628673647270291497186827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26419115764846860998124551 39628673647270291497186827)
        ·
          refine ⟨59443010470905437245780241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39628673647270291497186827 59443010470905437245780241)
          ·
            refine ⟨44582257853179077934335181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59443010470905437245780241 44582257853179077934335181)
            ·
              refine ⟨16718346694942154225375693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44582257853179077934335181 16718346694942154225375693)
              ·
                refine ⟨6269380010603307834515885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16718346694942154225375693 6269380010603307834515885)
                ·
                  refine ⟨2351017503976240437943457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6269380010603307834515885 2351017503976240437943457)
                  ·
                    refine ⟨1763263127982180328457593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351017503976240437943457 1763263127982180328457593)
                    ·
                      refine ⟨1322447345986635246343195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763263127982180328457593 1322447345986635246343195)
                      ·
                        rfl

theorem cell23_2575457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_2575457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575457 prefixEnd_2575457 := by exact prefixLift 2575457
  have htrace : WordTrace (prefixWord ++ tailWord_2575457) baseStart_2575457 baseEnd_2575457 := by
    simpa [prefixWord, tailWord_2575457, baseEnd_2575457] using wordTrace_append hprefix tailTrace_2575457
  have hstable : (prefixWord ++ tailWord_2575457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575457).length < 2 ^ (prefixWord ++ tailWord_2575457).sum := by decide
  have hdescent : baseEnd_2575457 < baseStart_2575457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575470 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2575470 : Nat := 118140960795 + 2575470 * 2 ^ 59
def prefixEnd_2575470 : Nat := 4983230072969 + 3 ^ 40 * 2575470 * 2
def baseEnd_2575470 : Nat := 1322454021235143695480635

theorem tailTrace_2575470 : CollatzResearch.WordTrace tailWord_2575470 prefixEnd_2575470 1322454021235143695480635 := by
  unfold tailWord_2575470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741888497439940012805483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62623405319679680068295909 11741888497439940012805483)
  ·
    refine ⟨17612832746159910019208225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11741888497439940012805483 17612832746159910019208225)
    ·
      refine ⟨13209624559619932514406169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17612832746159910019208225 13209624559619932514406169)
      ·
        refine ⟨9907218419714949385804627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13209624559619932514406169 9907218419714949385804627)
        ·
          refine ⟨14860827629572424078706941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907218419714949385804627 14860827629572424078706941)
          ·
            refine ⟨5572810361089659029515103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14860827629572424078706941 5572810361089659029515103)
            ·
              refine ⟨8359215541634488544272655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572810361089659029515103 8359215541634488544272655)
              ·
                refine ⟨12538823312451732816408983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359215541634488544272655 12538823312451732816408983)
                ·
                  refine ⟨18808234968677599224613475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12538823312451732816408983 18808234968677599224613475)
                  ·
                    refine ⟨28212352453016398836920213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18808234968677599224613475 28212352453016398836920213)
                    ·
                      refine ⟨1322454021235143695480635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28212352453016398836920213 1322454021235143695480635)
                      ·
                        rfl

theorem cell23_2575470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2575470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575470 prefixEnd_2575470 := by exact prefixLift 2575470
  have htrace : WordTrace (prefixWord ++ tailWord_2575470) baseStart_2575470 baseEnd_2575470 := by
    simpa [prefixWord, tailWord_2575470, baseEnd_2575470] using wordTrace_append hprefix tailTrace_2575470
  have hstable : (prefixWord ++ tailWord_2575470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575470).length < 2 ^ (prefixWord ++ tailWord_2575470).sum := by decide
  have hdescent : baseEnd_2575470 < baseStart_2575470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575517 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_2575517 : Nat := 118140960795 + 2575517 * 2 ^ 59
def prefixEnd_2575517 : Nat := 4983230072969 + 3 ^ 40 * 2575517 * 2
def baseEnd_2575517 : Nat := 1322478154825905011592919

theorem tailTrace_2575517 : CollatzResearch.WordTrace tailWord_2575517 prefixEnd_2575517 1322478154825905011592919 := by
  unfold tailWord_2575517
  simp only [CollatzResearch.WordTrace]
  refine ⟨93936822210349247129404805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62624548140232831419603203 93936822210349247129404805)
  ·
    refine ⟨17613154164440483836763401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93936822210349247129404805 17613154164440483836763401)
    ·
      refine ⟨13209865623330362877572551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17613154164440483836763401 13209865623330362877572551)
      ·
        refine ⟨19814798434995544316358827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13209865623330362877572551 19814798434995544316358827)
        ·
          refine ⟨29722197652493316474538241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19814798434995544316358827 29722197652493316474538241)
          ·
            refine ⟨22291648239369987355903681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29722197652493316474538241 22291648239369987355903681)
            ·
              refine ⟨16718736179527490516927761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22291648239369987355903681 16718736179527490516927761)
              ·
                refine ⟨12539052134645617887695821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16718736179527490516927761 12539052134645617887695821)
                ·
                  refine ⟨4702144550492106707885933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12539052134645617887695821 4702144550492106707885933)
                  ·
                    refine ⟨1763304206434540015457225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4702144550492106707885933 1763304206434540015457225)
                    ·
                      refine ⟨1322478154825905011592919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763304206434540015457225 1322478154825905011592919)
                      ·
                        rfl

theorem cell23_2575517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_2575517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575517 prefixEnd_2575517 := by exact prefixLift 2575517
  have htrace : WordTrace (prefixWord ++ tailWord_2575517) baseStart_2575517 baseEnd_2575517 := by
    simpa [prefixWord, tailWord_2575517, baseEnd_2575517] using wordTrace_append hprefix tailTrace_2575517
  have hstable : (prefixWord ++ tailWord_2575517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575517).length < 2 ^ (prefixWord ++ tailWord_2575517).sum := by decide
  have hdescent : baseEnd_2575517 < baseStart_2575517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575523 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 6]
def baseStart_2575523 : Nat := 118140960795 + 2575523 * 2 ^ 59
def prefixEnd_2575523 : Nat := 4983230072969 + 3 ^ 40 * 2575523 * 2
def baseEnd_2575523 : Nat := 440827078569943996039297

theorem tailTrace_2575523 : CollatzResearch.WordTrace tailWord_2575523 prefixEnd_2575523 440827078569943996039297 := by
  unfold tailWord_2575523
  simp only [CollatzResearch.WordTrace]
  refine ⟨93937041048327510154123223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62624694032218340102748815 93937041048327510154123223)
  ·
    refine ⟨140905561572491265231184835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93937041048327510154123223 140905561572491265231184835)
    ·
      refine ⟨211358342358736897846777253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140905561572491265231184835 211358342358736897846777253)
      ·
        refine ⟨39629689192263168346270735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211358342358736897846777253 39629689192263168346270735)
        ·
          refine ⟨59444533788394752519406103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39629689192263168346270735 59444533788394752519406103)
          ·
            refine ⟨89166800682592128779109155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59444533788394752519406103 89166800682592128779109155)
            ·
              refine ⟨133750201023888193168663733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89166800682592128779109155 133750201023888193168663733)
              ·
                refine ⟨12539081345989518109562225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133750201023888193168663733 12539081345989518109562225)
                ·
                  refine ⟨9404311009492138582171669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12539081345989518109562225 9404311009492138582171669)
                  ·
                    refine ⟨440827078569943996039297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9404311009492138582171669 440827078569943996039297)
                    ·
                      rfl

theorem cell23_2575523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_2575523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575523 prefixEnd_2575523 := by exact prefixLift 2575523
  have htrace : WordTrace (prefixWord ++ tailWord_2575523) baseStart_2575523 baseEnd_2575523 := by
    simpa [prefixWord, tailWord_2575523, baseEnd_2575523] using wordTrace_append hprefix tailTrace_2575523
  have hstable : (prefixWord ++ tailWord_2575523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575523).length < 2 ^ (prefixWord ++ tailWord_2575523).sum := by decide
  have hdescent : baseEnd_2575523 < baseStart_2575523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575524 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_2575524 : Nat := 118140960795 + 2575524 * 2 ^ 59
def prefixEnd_2575524 : Nat := 4983230072969 + 3 ^ 40 * 2575524 * 2
def baseEnd_2575524 : Nat := 1322481749190486484205387

theorem tailTrace_2575524 : CollatzResearch.WordTrace tailWord_2575524 prefixEnd_2575524 1322481749190486484205387 := by
  unfold tailWord_2575524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46968538760661943662454813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62624718347549258216606417 46968538760661943662454813)
  ·
    refine ⟨17613202035248228873420555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46968538760661943662454813 17613202035248228873420555)
    ·
      refine ⟨26419803052872343310130833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17613202035248228873420555 26419803052872343310130833)
      ·
        refine ⟨19814852289654257482598125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26419803052872343310130833 19814852289654257482598125)
        ·
          refine ⟨7430569608620346555974297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19814852289654257482598125 7430569608620346555974297)
          ·
            refine ⟨5572927206465259916980723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7430569608620346555974297 5572927206465259916980723)
            ·
              refine ⟨8359390809697889875471085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572927206465259916980723 8359390809697889875471085)
              ·
                refine ⟨3134771553636708703301657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8359390809697889875471085 3134771553636708703301657)
                ·
                  refine ⟨2351078665227531527476243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134771553636708703301657 2351078665227531527476243)
                  ·
                    refine ⟨3526617997841297291214365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351078665227531527476243 3526617997841297291214365)
                    ·
                      refine ⟨1322481749190486484205387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3526617997841297291214365 1322481749190486484205387)
                      ·
                        rfl

theorem cell23_2575524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_2575524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575524 prefixEnd_2575524 := by exact prefixLift 2575524
  have htrace : WordTrace (prefixWord ++ tailWord_2575524) baseStart_2575524 baseEnd_2575524 := by
    simpa [prefixWord, tailWord_2575524, baseEnd_2575524] using wordTrace_append hprefix tailTrace_2575524
  have hstable : (prefixWord ++ tailWord_2575524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575524).length < 2 ^ (prefixWord ++ tailWord_2575524).sum := by decide
  have hdescent : baseEnd_2575524 < baseStart_2575524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575547 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 4, 2, 2]
def baseStart_2575547 : Nat := 118140960795 + 2575547 * 2 ^ 59
def prefixEnd_2575547 : Nat := 4983230072969 + 3 ^ 40 * 2575547 * 2
def baseEnd_2575547 : Nat := 1322493559245539894217781

theorem tailTrace_2575547 : CollatzResearch.WordTrace tailWord_2575547 prefixEnd_2575547 1322493559245539894217781 := by
  unfold tailWord_2575547
  simp only [CollatzResearch.WordTrace]
  refine ⟨93937916400240562252996895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62625277600160374835331263 93937916400240562252996895)
  ·
    refine ⟨140906874600360843379495343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93937916400240562252996895 140906874600360843379495343)
    ·
      refine ⟨211360311900541265069243015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140906874600360843379495343 211360311900541265069243015)
      ·
        refine ⟨317040467850811897603864523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211360311900541265069243015 317040467850811897603864523)
        ·
          refine ⟨475560701776217846405796785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317040467850811897603864523 475560701776217846405796785)
          ·
            refine ⟨356670526332163384804347589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475560701776217846405796785 356670526332163384804347589)
            ·
              refine ⟨66875723687280634650815173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356670526332163384804347589 66875723687280634650815173)
              ·
                refine ⟨12539198191365118997027845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66875723687280634650815173 12539198191365118997027845)
                ·
                  refine ⟨2351099660880959811942721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12539198191365118997027845 2351099660880959811942721)
                  ·
                    refine ⟨1763324745660719858957041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351099660880959811942721 1763324745660719858957041)
                    ·
                      refine ⟨1322493559245539894217781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763324745660719858957041 1322493559245539894217781)
                      ·
                        rfl

theorem cell23_2575547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2, 2].length) (baseStart_2575547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575547 prefixEnd_2575547 := by exact prefixLift 2575547
  have htrace : WordTrace (prefixWord ++ tailWord_2575547) baseStart_2575547 baseEnd_2575547 := by
    simpa [prefixWord, tailWord_2575547, baseEnd_2575547] using wordTrace_append hprefix tailTrace_2575547
  have hstable : (prefixWord ++ tailWord_2575547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575547).length < 2 ^ (prefixWord ++ tailWord_2575547).sum := by decide
  have hdescent : baseEnd_2575547 < baseStart_2575547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575570 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_2575570 : Nat := 118140960795 + 2575570 * 2 ^ 59
def prefixEnd_2575570 : Nat := 4983230072969 + 3 ^ 40 * 2575570 * 2
def baseEnd_2575570 : Nat := 146945041033399256025575

theorem tailTrace_2575570 : CollatzResearch.WordTrace tailWord_2575570 prefixEnd_2575570 146945041033399256025575 := by
  unfold tailWord_2575570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23484688819789309295271041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62625836852771491454056109 23484688819789309295271041)
  ·
    refine ⟨17613516614841981971453281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23484688819789309295271041 17613516614841981971453281)
    ·
      refine ⟨13210137461131486478589961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17613516614841981971453281 13210137461131486478589961)
      ·
        refine ⟨9907603095848614858942471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13210137461131486478589961 9907603095848614858942471)
        ·
          refine ⟨14861404643772922288413707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907603095848614858942471 14861404643772922288413707)
          ·
            refine ⟨22292106965659383432620561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14861404643772922288413707 22292106965659383432620561)
            ·
              refine ⟨16719080224244537574465421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22292106965659383432620561 16719080224244537574465421)
              ·
                refine ⟨6269655084091701590424533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16719080224244537574465421 6269655084091701590424533)
                ·
                  refine ⟨146945041033399256025575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6269655084091701590424533 146945041033399256025575)
                  ·
                    rfl

theorem cell23_2575570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_2575570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575570 prefixEnd_2575570 := by exact prefixLift 2575570
  have htrace : WordTrace (prefixWord ++ tailWord_2575570) baseStart_2575570 baseEnd_2575570 := by
    simpa [prefixWord, tailWord_2575570, baseEnd_2575570] using wordTrace_append hprefix tailTrace_2575570
  have hstable : (prefixWord ++ tailWord_2575570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575570).length < 2 ^ (prefixWord ++ tailWord_2575570).sum := by decide
  have hdescent : baseEnd_2575570 < baseStart_2575570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575574 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2575574 : Nat := 118140960795 + 2575574 * 2 ^ 59
def prefixEnd_2575574 : Nat := 4983230072969 + 3 ^ 40 * 2575574 * 2
def baseEnd_2575574 : Nat := 440835807741070429526719

theorem tailTrace_2575574 : CollatzResearch.WordTrace tailWord_2575574 prefixEnd_2575574 440835807741070429526719 := by
  unfold tailWord_2575574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871181323196421616514361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62625934114095163909486517 5871181323196421616514361)
  ·
    refine ⟨4403385992397316212385771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5871181323196421616514361 4403385992397316212385771)
    ·
      refine ⟨6605078988595974318578657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403385992397316212385771 6605078988595974318578657)
      ·
        refine ⟨4953809241446980738933993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605078988595974318578657 4953809241446980738933993)
        ·
          refine ⟨3715356931085235554200495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4953809241446980738933993 3715356931085235554200495)
          ·
            refine ⟨5573035396627853331300743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715356931085235554200495 5573035396627853331300743)
            ·
              refine ⟨8359553094941779996951115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573035396627853331300743 8359553094941779996951115)
              ·
                refine ⟨12539329642412669995426673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359553094941779996951115 12539329642412669995426673)
                ·
                  refine ⟨9404497231809502496570005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12539329642412669995426673 9404497231809502496570005)
                  ·
                    refine ⟨440835807741070429526719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9404497231809502496570005 440835807741070429526719)
                    ·
                      rfl

theorem cell23_2575574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2575574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575574 prefixEnd_2575574 := by exact prefixLift 2575574
  have htrace : WordTrace (prefixWord ++ tailWord_2575574) baseStart_2575574 baseEnd_2575574 := by
    simpa [prefixWord, tailWord_2575574, baseEnd_2575574] using wordTrace_append hprefix tailTrace_2575574
  have hstable : (prefixWord ++ tailWord_2575574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575574).length < 2 ^ (prefixWord ++ tailWord_2575574).sum := by decide
  have hdescent : baseEnd_2575574 < baseStart_2575574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575581 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2575581 : Nat := 118140960795 + 2575581 * 2 ^ 59
def prefixEnd_2575581 : Nat := 4983230072969 + 3 ^ 40 * 2575581 * 2
def baseEnd_2575581 : Nat := 1322511017587792761192625

theorem tailTrace_2575581 : CollatzResearch.WordTrace tailWord_2575581 prefixEnd_2575581 1322511017587792761192625 := by
  unfold tailWord_2575581
  simp only [CollatzResearch.WordTrace]
  refine ⟨93939156482117386059734597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62626104321411590706489731 93939156482117386059734597)
  ·
    refine ⟨17613591840397009886200237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93939156482117386059734597 17613591840397009886200237)
    ·
      refine ⟨6605096940148878707325089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17613591840397009886200237 6605096940148878707325089)
      ·
        refine ⟨4953822705111659030493817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605096940148878707325089 4953822705111659030493817)
        ·
          refine ⟨3715367028833744272870363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4953822705111659030493817 3715367028833744272870363)
          ·
            refine ⟨5573050543250616409305545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715367028833744272870363 5573050543250616409305545)
            ·
              refine ⟨4179787907437962306979159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573050543250616409305545 4179787907437962306979159)
              ·
                refine ⟨6269681861156943460468739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179787907437962306979159 6269681861156943460468739)
                ·
                  refine ⟨9404522791735415190703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269681861156943460468739 9404522791735415190703109)
                  ·
                    refine ⟨1763348023450390348256833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9404522791735415190703109 1763348023450390348256833)
                    ·
                      refine ⟨1322511017587792761192625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763348023450390348256833 1322511017587792761192625)
                      ·
                        rfl

theorem cell23_2575581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2575581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575581 prefixEnd_2575581 := by exact prefixLift 2575581
  have htrace : WordTrace (prefixWord ++ tailWord_2575581) baseStart_2575581 baseEnd_2575581 := by
    simpa [prefixWord, tailWord_2575581, baseEnd_2575581] using wordTrace_append hprefix tailTrace_2575581
  have hstable : (prefixWord ++ tailWord_2575581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575581).length < 2 ^ (prefixWord ++ tailWord_2575581).sum := by decide
  have hdescent : baseEnd_2575581 < baseStart_2575581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575681 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2575681 : Nat := 118140960795 + 2575681 * 2 ^ 59
def prefixEnd_2575681 : Nat := 4983230072969 + 3 ^ 40 * 2575681 * 2
def baseEnd_2575681 : Nat := 440854121884414123314055

theorem tailTrace_2575681 : CollatzResearch.WordTrace tailWord_2575681 prefixEnd_2575681 440854121884414123314055 := by
  unfold tailWord_2575681
  simp only [CollatzResearch.WordTrace]
  refine ⟨93942803781755103138374897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62628535854503402092249931 93942803781755103138374897)
  ·
    refine ⟨70457102836316327353781173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93942803781755103138374897 70457102836316327353781173)
    ·
      refine ⟨6605353390904655689416985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70457102836316327353781173 6605353390904655689416985)
      ·
        refine ⟨4954015043178491767062739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605353390904655689416985 4954015043178491767062739)
        ·
          refine ⟨7431022564767737650594109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954015043178491767062739 7431022564767737650594109)
          ·
            refine ⟨2786633461787901618972791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7431022564767737650594109 2786633461787901618972791)
            ·
              refine ⟨4179950192681852428459187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786633461787901618972791 4179950192681852428459187)
              ·
                refine ⟨6269925289022778642688781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179950192681852428459187 6269925289022778642688781)
                ·
                  refine ⟨2351221983383541991008293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6269925289022778642688781 2351221983383541991008293)
                  ·
                    refine ⟨440854121884414123314055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351221983383541991008293 440854121884414123314055)
                    ·
                      rfl

theorem cell23_2575681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2575681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575681 prefixEnd_2575681 := by exact prefixLift 2575681
  have htrace : WordTrace (prefixWord ++ tailWord_2575681) baseStart_2575681 baseEnd_2575681 := by
    simpa [prefixWord, tailWord_2575681, baseEnd_2575681] using wordTrace_append hprefix tailTrace_2575681
  have hstable : (prefixWord ++ tailWord_2575681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575681).length < 2 ^ (prefixWord ++ tailWord_2575681).sum := by decide
  have hdescent : baseEnd_2575681 < baseStart_2575681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575737 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_2575737 : Nat := 118140960795 + 2575737 * 2 ^ 59
def prefixEnd_2575737 : Nat := 4983230072969 + 3 ^ 40 * 2575737 * 2
def baseEnd_2575737 : Nat := 440863706856631383613969

theorem tailTrace_2575737 : CollatzResearch.WordTrace tailWord_2575737 prefixEnd_2575737 440863706856631383613969 := by
  unfold tailWord_2575737
  simp only [CollatzResearch.WordTrace]
  refine ⟨93944846269552224702413465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62629897513034816468275643 93944846269552224702413465)
  ·
    refine ⟨70458634702164168526810099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93944846269552224702413465 70458634702164168526810099)
    ·
      refine ⟨105687952053246252790215149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70458634702164168526810099 105687952053246252790215149)
      ·
        refine ⟨39632982019967344796330681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105687952053246252790215149 39632982019967344796330681)
        ·
          refine ⟨29724736514975508597248011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39632982019967344796330681 29724736514975508597248011)
          ·
            refine ⟨44587104772463262895872017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29724736514975508597248011 44587104772463262895872017)
            ·
              refine ⟨33440328579347447171904013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44587104772463262895872017 33440328579347447171904013)
              ·
                refine ⟨12540123217255292689464005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33440328579347447171904013 12540123217255292689464005)
                ·
                  refine ⟨2351273103235367379274501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12540123217255292689464005 2351273103235367379274501)
                  ·
                    refine ⟨440863706856631383613969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351273103235367379274501 440863706856631383613969)
                    ·
                      rfl

theorem cell23_2575737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_2575737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575737 prefixEnd_2575737 := by exact prefixLift 2575737
  have htrace : WordTrace (prefixWord ++ tailWord_2575737) baseStart_2575737 baseEnd_2575737 := by
    simpa [prefixWord, tailWord_2575737, baseEnd_2575737] using wordTrace_append hprefix tailTrace_2575737
  have hstable : (prefixWord ++ tailWord_2575737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575737).length < 2 ^ (prefixWord ++ tailWord_2575737).sum := by decide
  have hdescent : baseEnd_2575737 < baseStart_2575737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575744 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2]
def baseStart_2575744 : Nat := 118140960795 + 2575744 * 2 ^ 59
def prefixEnd_2575744 : Nat := 4983230072969 + 3 ^ 40 * 2575744 * 2
def baseEnd_2575744 : Nat := 1322594714934475623454375

theorem tailTrace_2575744 : CollatzResearch.WordTrace tailWord_2575744 prefixEnd_2575744 1322594714934475623454375 := by
  unfold tailWord_2575744
  simp only [CollatzResearch.WordTrace]
  refine ⟨46972550790263432448959143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62630067720351243265278857 46972550790263432448959143)
  ·
    refine ⟨70458826185395148673438715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46972550790263432448959143 70458826185395148673438715)
    ·
      refine ⟨105688239278092723010158073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70458826185395148673438715 105688239278092723010158073)
      ·
        refine ⟨79266179458569542257618555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105688239278092723010158073 79266179458569542257618555)
        ·
          refine ⟨118899269187854313386427833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79266179458569542257618555 118899269187854313386427833)
          ·
            refine ⟨89174451890890735039820875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118899269187854313386427833 89174451890890735039820875)
            ·
              refine ⟨133761677836336102559731313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89174451890890735039820875 133761677836336102559731313)
              ·
                refine ⟨100321258377252076919798485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133761677836336102559731313 100321258377252076919798485)
                ·
                  refine ⟨2351279493216845552807777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100321258377252076919798485 2351279493216845552807777)
                  ·
                    refine ⟨1763459619912634164605833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351279493216845552807777 1763459619912634164605833)
                    ·
                      refine ⟨1322594714934475623454375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763459619912634164605833 1322594714934475623454375)
                      ·
                        rfl

theorem cell23_2575744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_2575744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575744 prefixEnd_2575744 := by exact prefixLift 2575744
  have htrace : WordTrace (prefixWord ++ tailWord_2575744) baseStart_2575744 baseEnd_2575744 := by
    simpa [prefixWord, tailWord_2575744, baseEnd_2575744] using wordTrace_append hprefix tailTrace_2575744
  have hstable : (prefixWord ++ tailWord_2575744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575744).length < 2 ^ (prefixWord ++ tailWord_2575744).sum := by decide
  have hdescent : baseEnd_2575744 < baseStart_2575744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575778 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2575778 : Nat := 118140960795 + 2575778 * 2 ^ 59
def prefixEnd_2575778 : Nat := 4983230072969 + 3 ^ 40 * 2575778 * 2
def baseEnd_2575778 : Nat := 1322612173276728490429219

theorem tailTrace_2575778 : CollatzResearch.WordTrace tailWord_2575778 prefixEnd_2575778 1322612173276728490429219 := by
  unfold tailWord_2575778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23486585415600922176163997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62630894441602459136437325 23486585415600922176163997)
  ·
    refine ⟨8807469530850345816061499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23486585415600922176163997 8807469530850345816061499)
    ·
      refine ⟨13211204296275518724092249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807469530850345816061499 13211204296275518724092249)
      ·
        refine ⟨9908403222206639043069187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13211204296275518724092249 9908403222206639043069187)
        ·
          refine ⟨14862604833309958564603781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908403222206639043069187 14862604833309958564603781)
          ·
            refine ⟨2786738406245617230863209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14862604833309958564603781 2786738406245617230863209)
            ·
              refine ⟨2090053804684212923147407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786738406245617230863209 2090053804684212923147407)
              ·
                refine ⟨3135080707026319384721111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090053804684212923147407 3135080707026319384721111)
                ·
                  refine ⟨4702621060539479077081667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135080707026319384721111 4702621060539479077081667)
                  ·
                    refine ⟨7053931590809218615622501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4702621060539479077081667 7053931590809218615622501)
                    ·
                      refine ⟨1322612173276728490429219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7053931590809218615622501 1322612173276728490429219)
                      ·
                        rfl

theorem cell23_2575778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2575778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575778 prefixEnd_2575778 := by exact prefixLift 2575778
  have htrace : WordTrace (prefixWord ++ tailWord_2575778) baseStart_2575778 baseEnd_2575778 := by
    simpa [prefixWord, tailWord_2575778, baseEnd_2575778] using wordTrace_append hprefix tailTrace_2575778
  have hstable : (prefixWord ++ tailWord_2575778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575778).length < 2 ^ (prefixWord ++ tailWord_2575778).sum := by decide
  have hdescent : baseEnd_2575778 < baseStart_2575778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575784 : List Nat := [2, 1, 6, 1, 2, 1, 10]
def baseStart_2575784 : Nat := 118140960795 + 2575784 * 2 ^ 59
def prefixEnd_2575784 : Nat := 4983230072969 + 3 ^ 40 * 2575784 * 2
def baseEnd_2575784 : Nat := 16328583384699450209311

theorem tailTrace_2575784 : CollatzResearch.WordTrace tailWord_2575784 prefixEnd_2575784 16328583384699450209311 := by
  unfold tailWord_2575784
  simp only [CollatzResearch.WordTrace]
  refine ⟨46973280250190975864687203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62631040333587967819582937 46973280250190975864687203)
  ·
    refine ⟨70459920375286463797030805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46973280250190975864687203 70459920375286463797030805)
    ·
      refine ⟨3302808767591552990485819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70459920375286463797030805 3302808767591552990485819)
      ·
        refine ⟨4954213151387329485728729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302808767591552990485819 4954213151387329485728729)
        ·
          refine ⟨3715659863540497114296547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4954213151387329485728729 3715659863540497114296547)
          ·
            refine ⟨5573489795310745671444821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715659863540497114296547 5573489795310745671444821)
            ·
              refine ⟨16328583384699450209311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5573489795310745671444821 16328583384699450209311)
              ·
                rfl

theorem cell23_2575784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 10].length) (baseStart_2575784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575784 prefixEnd_2575784 := by exact prefixLift 2575784
  have htrace : WordTrace (prefixWord ++ tailWord_2575784) baseStart_2575784 baseEnd_2575784 := by
    simpa [prefixWord, tailWord_2575784, baseEnd_2575784] using wordTrace_append hprefix tailTrace_2575784
  have hstable : (prefixWord ++ tailWord_2575784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575784).length < 2 ^ (prefixWord ++ tailWord_2575784).sum := by decide
  have hdescent : baseEnd_2575784 < baseStart_2575784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575854 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2575854 : Nat := 118140960795 + 2575854 * 2 ^ 59
def prefixEnd_2575854 : Nat := 4983230072969 + 3 ^ 40 * 2575854 * 2
def baseEnd_2575854 : Nat := 1322651197806470193078869

theorem tailTrace_2575854 : CollatzResearch.WordTrace tailWord_2575854 prefixEnd_2575854 1322651197806470193078869 := by
  unfold tailWord_2575854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743639201266044210552827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62632742406752235789615077 11743639201266044210552827)
  ·
    refine ⟨17615458801899066315829241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11743639201266044210552827 17615458801899066315829241)
    ·
      refine ⟨13211594101424299736871931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17615458801899066315829241 13211594101424299736871931)
      ·
        refine ⟨19817391152136449605307897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13211594101424299736871931 19817391152136449605307897)
        ·
          refine ⟨14863043364102337203980923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19817391152136449605307897 14863043364102337203980923)
          ·
            refine ⟨22294565046153505805971385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863043364102337203980923 22294565046153505805971385)
            ·
              refine ⟨16720923784615129354478539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22294565046153505805971385 16720923784615129354478539)
              ·
                refine ⟨25081385676922694031717809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16720923784615129354478539 25081385676922694031717809)
                ·
                  refine ⟨18811039257692020523788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25081385676922694031717809 18811039257692020523788357)
                  ·
                    refine ⟨3527069860817253848210317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18811039257692020523788357 3527069860817253848210317)
                    ·
                      refine ⟨1322651197806470193078869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527069860817253848210317 1322651197806470193078869)
                      ·
                        rfl

theorem cell23_2575854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2575854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575854 prefixEnd_2575854 := by exact prefixLift 2575854
  have htrace : WordTrace (prefixWord ++ tailWord_2575854) baseStart_2575854 baseEnd_2575854 := by
    simpa [prefixWord, tailWord_2575854, baseEnd_2575854] using wordTrace_append hprefix tailTrace_2575854
  have hstable : (prefixWord ++ tailWord_2575854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575854).length < 2 ^ (prefixWord ++ tailWord_2575854).sum := by decide
  have hdescent : baseEnd_2575854 < baseStart_2575854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575914 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2575914 : Nat := 118140960795 + 2575914 * 2 ^ 59
def prefixEnd_2575914 : Nat := 4983230072969 + 3 ^ 40 * 2575914 * 2
def baseEnd_2575914 : Nat := 1322682006645739958328593

theorem tailTrace_2575914 : CollatzResearch.WordTrace tailWord_2575914 prefixEnd_2575914 1322682006645739958328593 := by
  unfold tailWord_2575914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23487825497477745982901699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62634201326607322621071197 23487825497477745982901699)
  ·
    refine ⟨35231738246216618974352549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23487825497477745982901699 35231738246216618974352549)
    ·
      refine ⟨6605950921165616057691103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35231738246216618974352549 6605950921165616057691103)
      ·
        refine ⟨9908926381748424086536655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605950921165616057691103 9908926381748424086536655)
        ·
          refine ⟨14863389572622636129804983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908926381748424086536655 14863389572622636129804983)
          ·
            refine ⟨22295084358933954194707475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863389572622636129804983 22295084358933954194707475)
            ·
              refine ⟨33442626538400931292061213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22295084358933954194707475 33442626538400931292061213)
              ·
                refine ⟨12540984951900349234522955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33442626538400931292061213 12540984951900349234522955)
                ·
                  refine ⟨18811477427850523851784433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540984951900349234522955 18811477427850523851784433)
                  ·
                    refine ⟨14108608070887892888838325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18811477427850523851784433 14108608070887892888838325)
                    ·
                      refine ⟨1322682006645739958328593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14108608070887892888838325 1322682006645739958328593)
                      ·
                        rfl

theorem cell23_2575914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2575914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575914 prefixEnd_2575914 := by exact prefixLift 2575914
  have htrace : WordTrace (prefixWord ++ tailWord_2575914) baseStart_2575914 baseEnd_2575914 := by
    simpa [prefixWord, tailWord_2575914, baseEnd_2575914] using wordTrace_append hprefix tailTrace_2575914
  have hstable : (prefixWord ++ tailWord_2575914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575914).length < 2 ^ (prefixWord ++ tailWord_2575914).sum := by decide
  have hdescent : baseEnd_2575914 < baseStart_2575914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575947 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 8]
def baseStart_2575947 : Nat := 118140960795 + 2575947 * 2 ^ 59
def prefixEnd_2575947 : Nat := 4983230072969 + 3 ^ 40 * 2575947 * 2
def baseEnd_2575947 : Nat := 146966550167482036579549

theorem tailTrace_2575947 : CollatzResearch.WordTrace tailWord_2575947 prefixEnd_2575947 146966550167482036579549 := by
  unfold tailWord_2575947
  simp only [CollatzResearch.WordTrace]
  refine ⟨93952505598791430567558095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62635003732527620378372063 93952505598791430567558095)
  ·
    refine ⟨140928758398187145851337143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93952505598791430567558095 140928758398187145851337143)
    ·
      refine ⟨211393137597280718777005715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140928758398187145851337143 211393137597280718777005715)
      ·
        refine ⟨317089706395921078165508573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211393137597280718777005715 317089706395921078165508573)
        ·
          refine ⟨118908639898470404312065715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317089706395921078165508573 118908639898470404312065715)
          ·
            refine ⟨178362959847705606468098573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118908639898470404312065715 178362959847705606468098573)
            ·
              refine ⟨66886109942889602425536965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178362959847705606468098573 66886109942889602425536965)
              ·
                refine ⟨12541145614291800454788181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66886109942889602425536965 12541145614291800454788181)
                ·
                  refine ⟨146966550167482036579549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12541145614291800454788181 146966550167482036579549)
                  ·
                    rfl

theorem cell23_2575947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_2575947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575947 prefixEnd_2575947 := by exact prefixLift 2575947
  have htrace : WordTrace (prefixWord ++ tailWord_2575947) baseStart_2575947 baseEnd_2575947 := by
    simpa [prefixWord, tailWord_2575947, baseEnd_2575947] using wordTrace_append hprefix tailTrace_2575947
  have hstable : (prefixWord ++ tailWord_2575947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575947).length < 2 ^ (prefixWord ++ tailWord_2575947).sum := by decide
  have hdescent : baseEnd_2575947 < baseStart_2575947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575954 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2575954 : Nat := 118140960795 + 2575954 * 2 ^ 59
def prefixEnd_2575954 : Nat := 4983230072969 + 3 ^ 40 * 2575954 * 2
def baseEnd_2575954 : Nat := 1322702545871919801828409

theorem tailTrace_2575954 : CollatzResearch.WordTrace tailWord_2575954 prefixEnd_2575954 1322702545871919801828409 := by
  unfold tailWord_2575954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23488190227441517690765729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62635173939844047175375277 23488190227441517690765729)
  ·
    refine ⟨17616142670581138268074297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23488190227441517690765729 17616142670581138268074297)
    ·
      refine ⟨13212107002935853701055723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17616142670581138268074297 13212107002935853701055723)
      ·
        refine ⟨19818160504403780551583585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13212107002935853701055723 19818160504403780551583585)
        ·
          refine ⟨14863620378302835413687689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19818160504403780551583585 14863620378302835413687689)
          ·
            refine ⟨11147715283727126560265767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14863620378302835413687689 11147715283727126560265767)
            ·
              refine ⟨16721572925590689840398651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11147715283727126560265767 16721572925590689840398651)
              ·
                refine ⟨25082359388386034760597977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16721572925590689840398651 25082359388386034760597977)
                ·
                  refine ⟨18811769541289526070448483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25082359388386034760597977 18811769541289526070448483)
                  ·
                    refine ⟨28217654311934289105672725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18811769541289526070448483 28217654311934289105672725)
                    ·
                      refine ⟨1322702545871919801828409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28217654311934289105672725 1322702545871919801828409)
                      ·
                        rfl

theorem cell23_2575954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2575954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2575954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2575954 prefixEnd_2575954 := by exact prefixLift 2575954
  have htrace : WordTrace (prefixWord ++ tailWord_2575954) baseStart_2575954 baseEnd_2575954 := by
    simpa [prefixWord, tailWord_2575954, baseEnd_2575954] using wordTrace_append hprefix tailTrace_2575954
  have hstable : (prefixWord ++ tailWord_2575954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575954).length < 2 ^ (prefixWord ++ tailWord_2575954).sum := by decide
  have hdescent : baseEnd_2575954 < baseStart_2575954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576044 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2576044 : Nat := 118140960795 + 2576044 * 2 ^ 59
def prefixEnd_2576044 : Nat := 4983230072969 + 3 ^ 40 * 2576044 * 2
def baseEnd_2576044 : Nat := 1322748759130824449702995

theorem tailTrace_2576044 : CollatzResearch.WordTrace tailWord_2576044 prefixEnd_2576044 1322748759130824449702995 := by
  unfold tailWord_2576044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978021739720008066919593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62637362319626677422559457 46978021739720008066919593)
  ·
    refine ⟨35233516304790006050189695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46978021739720008066919593 35233516304790006050189695)
    ·
      refine ⟨52850274457185009075284543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35233516304790006050189695 52850274457185009075284543)
      ·
        refine ⟨79275411685777513612926815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52850274457185009075284543 79275411685777513612926815)
        ·
          refine ⟨118913117528666270419390223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79275411685777513612926815 118913117528666270419390223)
          ·
            refine ⟨178369676292999405629085335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118913117528666270419390223 178369676292999405629085335)
            ·
              refine ⟨267554514439499108443628003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178369676292999405629085335 267554514439499108443628003)
              ·
                refine ⟨401331771659248662665442005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267554514439499108443628003 401331771659248662665442005)
                ·
                  refine ⟨9406213398263640531221297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 401331771659248662665442005 9406213398263640531221297)
                  ·
                    refine ⟨7054660048697730398415973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9406213398263640531221297 7054660048697730398415973)
                    ·
                      refine ⟨1322748759130824449702995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7054660048697730398415973 1322748759130824449702995)
                      ·
                        rfl

theorem cell23_2576044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2576044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576044 prefixEnd_2576044 := by exact prefixLift 2576044
  have htrace : WordTrace (prefixWord ++ tailWord_2576044) baseStart_2576044 baseEnd_2576044 := by
    simpa [prefixWord, tailWord_2576044, baseEnd_2576044] using wordTrace_append hprefix tailTrace_2576044
  have hstable : (prefixWord ++ tailWord_2576044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576044).length < 2 ^ (prefixWord ++ tailWord_2576044).sum := by decide
  have hdescent : baseEnd_2576044 < baseStart_2576044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576048 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2]
def baseStart_2576048 : Nat := 118140960795 + 2576048 * 2 ^ 59
def prefixEnd_2576048 : Nat := 4983230072969 + 3 ^ 40 * 2576048 * 2
def baseEnd_2576048 : Nat := 1322750813053442434052977

theorem tailTrace_2576048 : CollatzResearch.WordTrace tailWord_2576048 prefixEnd_2576048 1322750813053442434052977 := by
  unfold tailWord_2576048
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978094685712762408492399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62637459580950349877989865 46978094685712762408492399)
  ·
    refine ⟨70467142028569143612738599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46978094685712762408492399 70467142028569143612738599)
    ·
      refine ⟨105700713042853715419107899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70467142028569143612738599 105700713042853715419107899)
      ·
        refine ⟨158551069564280573128661849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105700713042853715419107899 158551069564280573128661849)
        ·
          refine ⟨118913302173210429846496387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158551069564280573128661849 118913302173210429846496387)
          ·
            refine ⟨178369953259815644769744581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118913302173210429846496387 178369953259815644769744581)
            ·
              refine ⟨33444366236215433394327109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178369953259815644769744581 33444366236215433394327109)
              ·
                refine ⟨6270818669290393761436333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33444366236215433394327109 6270818669290393761436333)
                ·
                  refine ⟨2351557000983897660538625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6270818669290393761436333 2351557000983897660538625)
                  ·
                    refine ⟨1763667750737923245403969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351557000983897660538625 1763667750737923245403969)
                    ·
                      refine ⟨1322750813053442434052977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763667750737923245403969 1322750813053442434052977)
                      ·
                        rfl

theorem cell23_2576048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2].length) (baseStart_2576048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576048 prefixEnd_2576048 := by exact prefixLift 2576048
  have htrace : WordTrace (prefixWord ++ tailWord_2576048) baseStart_2576048 baseEnd_2576048 := by
    simpa [prefixWord, tailWord_2576048, baseEnd_2576048] using wordTrace_append hprefix tailTrace_2576048
  have hstable : (prefixWord ++ tailWord_2576048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576048).length < 2 ^ (prefixWord ++ tailWord_2576048).sum := by decide
  have hdescent : baseEnd_2576048 < baseStart_2576048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576051 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3]
def baseStart_2576051 : Nat := 118140960795 + 2576051 * 2 ^ 59
def prefixEnd_2576051 : Nat := 4983230072969 + 3 ^ 40 * 2576051 * 2
def baseEnd_2576051 : Nat := 1322752353495405922315463

theorem tailTrace_2576051 : CollatzResearch.WordTrace tailWord_2576051 prefixEnd_2576051 1322752353495405922315463 := by
  unfold tailWord_2576051
  simp only [CollatzResearch.WordTrace]
  refine ⟨93956298790414656329344007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62637532526943104219562671 93956298790414656329344007)
  ·
    refine ⟨140934448185621984494016011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93956298790414656329344007 140934448185621984494016011)
    ·
      refine ⟨211401672278432976741024017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140934448185621984494016011 211401672278432976741024017)
      ·
        refine ⟨158551254208824732555768013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211401672278432976741024017 158551254208824732555768013)
        ·
          refine ⟨59456720328309274708413005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158551254208824732555768013 59456720328309274708413005)
          ·
            refine ⟨22296270123115978015654877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59456720328309274708413005 22296270123115978015654877)
            ·
              refine ⟨8361101296168491755870579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22296270123115978015654877 8361101296168491755870579)
              ·
                refine ⟨12541651944252737633805869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361101296168491755870579 12541651944252737633805869)
                ·
                  refine ⟨4703119479094776612677201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12541651944252737633805869 4703119479094776612677201)
                  ·
                    refine ⟨3527339609321082459507901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4703119479094776612677201 3527339609321082459507901)
                    ·
                      refine ⟨1322752353495405922315463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527339609321082459507901 1322752353495405922315463)
                      ·
                        rfl

theorem cell23_2576051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_2576051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576051 prefixEnd_2576051 := by exact prefixLift 2576051
  have htrace : WordTrace (prefixWord ++ tailWord_2576051) baseStart_2576051 baseEnd_2576051 := by
    simpa [prefixWord, tailWord_2576051, baseEnd_2576051] using wordTrace_append hprefix tailTrace_2576051
  have hstable : (prefixWord ++ tailWord_2576051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576051).length < 2 ^ (prefixWord ++ tailWord_2576051).sum := by decide
  have hdescent : baseEnd_2576051 < baseStart_2576051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576061 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2576061 : Nat := 118140960795 + 2576061 * 2 ^ 59
def prefixEnd_2576061 : Nat := 4983230072969 + 3 ^ 40 * 2576061 * 2
def baseEnd_2576061 : Nat := 1322757488301950883190417

theorem tailTrace_2576061 : CollatzResearch.WordTrace tailWord_2576061 prefixEnd_2576061 1322757488301950883190417 := by
  unfold tailWord_2576061
  simp only [CollatzResearch.WordTrace]
  refine ⟨93956663520378428037208037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62637775680252285358138691 93956663520378428037208037)
  ·
    refine ⟨17616874410070955256976507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93956663520378428037208037 17616874410070955256976507)
    ·
      refine ⟨26425311615106432885464761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17616874410070955256976507 26425311615106432885464761)
      ·
        refine ⟨19818983711329824664098571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26425311615106432885464761 19818983711329824664098571)
        ·
          refine ⟨29728475566994736996147857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19818983711329824664098571 29728475566994736996147857)
          ·
            refine ⟨22296356675246052747110893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29728475566994736996147857 22296356675246052747110893)
            ·
              refine ⟨8361133753217269780166585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22296356675246052747110893 8361133753217269780166585)
              ·
                refine ⟨6270850314912952335124939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8361133753217269780166585 6270850314912952335124939)
                ·
                  refine ⟨9406275472369428502687409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6270850314912952335124939 9406275472369428502687409)
                  ·
                    refine ⟨7054706604277071377015557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9406275472369428502687409 7054706604277071377015557)
                    ·
                      refine ⟨1322757488301950883190417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7054706604277071377015557 1322757488301950883190417)
                      ·
                        rfl

theorem cell23_2576061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2576061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576061 prefixEnd_2576061 := by exact prefixLift 2576061
  have htrace : WordTrace (prefixWord ++ tailWord_2576061) baseStart_2576061 baseEnd_2576061 := by
    simpa [prefixWord, tailWord_2576061, baseEnd_2576061] using wordTrace_append hprefix tailTrace_2576061
  have hstable : (prefixWord ++ tailWord_2576061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576061).length < 2 ^ (prefixWord ++ tailWord_2576061).sum := by decide
  have hdescent : baseEnd_2576061 < baseStart_2576061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576076 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2576076 : Nat := 118140960795 + 2576076 * 2 ^ 59
def prefixEnd_2576076 : Nat := 4983230072969 + 3 ^ 40 * 2576076 * 2
def baseEnd_2576076 : Nat := 1322765190511768324502849

theorem tailTrace_2576076 : CollatzResearch.WordTrace tailWord_2576076 prefixEnd_2576076 1322765190511768324502849 := by
  unfold tailWord_2576076
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978605307662042799502041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62638140410216057066002721 46978605307662042799502041)
  ·
    refine ⟨35233953980746532099626531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46978605307662042799502041 35233953980746532099626531)
    ·
      refine ⟨52850930971119798149439797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35233953980746532099626531 52850930971119798149439797)
      ·
        refine ⟨4954774778542481076509981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52850930971119798149439797 4954774778542481076509981)
        ·
          refine ⟨1858040541953430403691243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4954774778542481076509981 1858040541953430403691243)
          ·
            refine ⟨2787060812930145605536865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858040541953430403691243 2787060812930145605536865)
            ·
              refine ⟨2090295609697609204152649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787060812930145605536865 2090295609697609204152649)
              ·
                refine ⟨1567721707273206903114487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090295609697609204152649 1567721707273206903114487)
                ·
                  refine ⟨2351582560909810354671731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567721707273206903114487 2351582560909810354671731)
                  ·
                    refine ⟨3527373841364715532007597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351582560909810354671731 3527373841364715532007597)
                    ·
                      refine ⟨1322765190511768324502849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527373841364715532007597 1322765190511768324502849)
                      ·
                        rfl

theorem cell23_2576076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2576076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576076 prefixEnd_2576076 := by exact prefixLift 2576076
  have htrace : WordTrace (prefixWord ++ tailWord_2576076) baseStart_2576076 baseEnd_2576076 := by
    simpa [prefixWord, tailWord_2576076, baseEnd_2576076] using wordTrace_append hprefix tailTrace_2576076
  have hstable : (prefixWord ++ tailWord_2576076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576076).length < 2 ^ (prefixWord ++ tailWord_2576076).sum := by decide
  have hdescent : baseEnd_2576076 < baseStart_2576076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576108 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_2576108 : Nat := 118140960795 + 2576108 * 2 ^ 59
def prefixEnd_2576108 : Nat := 4983230072969 + 3 ^ 40 * 2576108 * 2
def baseEnd_2576108 : Nat := 1322781621892712199302701

theorem tailTrace_2576108 : CollatzResearch.WordTrace tailWord_2576108 prefixEnd_2576108 1322781621892712199302701 := by
  unfold tailWord_2576108
  simp only [CollatzResearch.WordTrace]
  refine ⟨46979188875604077532084489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62638918500805436709445985 46979188875604077532084489)
  ·
    refine ⟨35234391656703058149063367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46979188875604077532084489 35234391656703058149063367)
    ·
      refine ⟨52851587485054587223595051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35234391656703058149063367 52851587485054587223595051)
      ·
        refine ⟨79277381227581880835392577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52851587485054587223595051 79277381227581880835392577)
        ·
          refine ⟨59458035920686410626544433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79277381227581880835392577 59458035920686410626544433)
          ·
            refine ⟨44593526940514807969908325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59458035920686410626544433 44593526940514807969908325)
            ·
              refine ⟨8361286301346526494357811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44593526940514807969908325 8361286301346526494357811)
              ·
                refine ⟨12541929452019789741536717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361286301346526494357811 12541929452019789741536717)
                ·
                  refine ⟨4703223544507421153076269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12541929452019789741536717 4703223544507421153076269)
                  ·
                    refine ⟨1763708829190282932403601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4703223544507421153076269 1763708829190282932403601)
                    ·
                      refine ⟨1322781621892712199302701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763708829190282932403601 1322781621892712199302701)
                      ·
                        rfl

theorem cell23_2576108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_2576108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576108 prefixEnd_2576108 := by exact prefixLift 2576108
  have htrace : WordTrace (prefixWord ++ tailWord_2576108) baseStart_2576108 baseEnd_2576108 := by
    simpa [prefixWord, tailWord_2576108, baseEnd_2576108] using wordTrace_append hprefix tailTrace_2576108
  have hstable : (prefixWord ++ tailWord_2576108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576108).length < 2 ^ (prefixWord ++ tailWord_2576108).sum := by decide
  have hdescent : baseEnd_2576108 < baseStart_2576108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576116 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2576116 : Nat := 118140960795 + 2576116 * 2 ^ 59
def prefixEnd_2576116 : Nat := 4983230072969 + 3 ^ 40 * 2576116 * 2
def baseEnd_2576116 : Nat := 1322785729737948168002665

theorem tailTrace_2576116 : CollatzResearch.WordTrace tailWord_2576116 prefixEnd_2576116 1322785729737948168002665 := by
  unfold tailWord_2576116
  simp only [CollatzResearch.WordTrace]
  refine ⟨46979334767589586215230101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62639113023452781620306801 46979334767589586215230101)
  ·
    refine ⟨2202156317230761853838911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46979334767589586215230101 2202156317230761853838911)
    ·
      refine ⟨3303234475846142780758367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202156317230761853838911 3303234475846142780758367)
      ·
        refine ⟨4954851713769214171137551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303234475846142780758367 4954851713769214171137551)
        ·
          refine ⟨7432277570653821256706327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954851713769214171137551 7432277570653821256706327)
          ·
            refine ⟨11148416355980731885059491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432277570653821256706327 11148416355980731885059491)
            ·
              refine ⟨16722624533971097827589237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148416355980731885059491 16722624533971097827589237)
              ·
                refine ⟨1567746050059790421336491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16722624533971097827589237 1567746050059790421336491)
                ·
                  refine ⟨2351619075089685632004737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567746050059790421336491 2351619075089685632004737)
                  ·
                    refine ⟨1763714306317264224003553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351619075089685632004737 1763714306317264224003553)
                    ·
                      refine ⟨1322785729737948168002665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763714306317264224003553 1322785729737948168002665)
                      ·
                        rfl

theorem cell23_2576116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2576116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576116 prefixEnd_2576116 := by exact prefixLift 2576116
  have htrace : WordTrace (prefixWord ++ tailWord_2576116) baseStart_2576116 baseEnd_2576116 := by
    simpa [prefixWord, tailWord_2576116, baseEnd_2576116] using wordTrace_append hprefix tailTrace_2576116
  have hstable : (prefixWord ++ tailWord_2576116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576116).length < 2 ^ (prefixWord ++ tailWord_2576116).sum := by decide
  have hdescent : baseEnd_2576116 < baseStart_2576116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576132 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2576132 : Nat := 118140960795 + 2576132 * 2 ^ 59
def prefixEnd_2576132 : Nat := 4983230072969 + 3 ^ 40 * 2576132 * 2
def baseEnd_2576132 : Nat := 1322793945428420105402591

theorem tailTrace_2576132 : CollatzResearch.WordTrace tailWord_2576132 prefixEnd_2576132 1322793945428420105402591 := by
  unfold tailWord_2576132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46979626551560603581521325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62639502068747471442028433 46979626551560603581521325)
  ·
    refine ⟨17617359956835226343070497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46979626551560603581521325 17617359956835226343070497)
    ·
      refine ⟨13213019967626419757302873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17617359956835226343070497 13213019967626419757302873)
      ·
        refine ⟨9909764975719814817977155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13213019967626419757302873 9909764975719814817977155)
        ·
          refine ⟨14864647463579722226965733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909764975719814817977155 14864647463579722226965733)
          ·
            refine ⟨2787121399421197917556075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14864647463579722226965733 2787121399421197917556075)
            ·
              refine ⟨4180682099131796876334113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787121399421197917556075 4180682099131796876334113)
              ·
                refine ⟨3135511574348847657250585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4180682099131796876334113 3135511574348847657250585)
                ·
                  refine ⟨2351633680761635742937939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135511574348847657250585 2351633680761635742937939)
                  ·
                    refine ⟨3527450521142453614406909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351633680761635742937939 3527450521142453614406909)
                    ·
                      refine ⟨1322793945428420105402591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527450521142453614406909 1322793945428420105402591)
                      ·
                        rfl

theorem cell23_2576132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2576132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576132 prefixEnd_2576132 := by exact prefixLift 2576132
  have htrace : WordTrace (prefixWord ++ tailWord_2576132) baseStart_2576132 baseEnd_2576132 := by
    simpa [prefixWord, tailWord_2576132, baseEnd_2576132] using wordTrace_append hprefix tailTrace_2576132
  have hstable : (prefixWord ++ tailWord_2576132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576132).length < 2 ^ (prefixWord ++ tailWord_2576132).sum := by decide
  have hdescent : baseEnd_2576132 < baseStart_2576132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576161 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 7]
def baseStart_2576161 : Nat := 118140960795 + 2576161 * 2 ^ 59
def prefixEnd_2576161 : Nat := 4983230072969 + 3 ^ 40 * 2576161 * 2
def baseEnd_2576161 : Nat := 146978759596377832437773

theorem tailTrace_2576161 : CollatzResearch.WordTrace tailWord_2576161 prefixEnd_2576161 146978759596377832437773 := by
  unfold tailWord_2576161
  simp only [CollatzResearch.WordTrace]
  refine ⟨93960310820016145115848337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62640207213344096743898891 93960310820016145115848337)
  ·
    refine ⟨70470233115012108836886253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93960310820016145115848337 70470233115012108836886253)
    ·
      refine ⟨26426337418129540813832345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70470233115012108836886253 26426337418129540813832345)
      ·
        refine ⟨19819753063597155610374259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26426337418129540813832345 19819753063597155610374259)
        ·
          refine ⟨29729629595395733415561389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19819753063597155610374259 29729629595395733415561389)
          ·
            refine ⟨11148611098273400030835521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29729629595395733415561389 11148611098273400030835521)
            ·
              refine ⟨8361458323705050023126641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11148611098273400030835521 8361458323705050023126641)
              ·
                refine ⟨6271093742778787517344981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8361458323705050023126641 6271093742778787517344981)
                ·
                  refine ⟨146978759596377832437773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6271093742778787517344981 146978759596377832437773)
                  ·
                    rfl

theorem cell23_2576161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_2576161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576161 prefixEnd_2576161 := by exact prefixLift 2576161
  have htrace : WordTrace (prefixWord ++ tailWord_2576161) baseStart_2576161 baseEnd_2576161 := by
    simpa [prefixWord, tailWord_2576161, baseEnd_2576161] using wordTrace_append hprefix tailTrace_2576161
  have hstable : (prefixWord ++ tailWord_2576161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576161).length < 2 ^ (prefixWord ++ tailWord_2576161).sum := by decide
  have hdescent : baseEnd_2576161 < baseStart_2576161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576195 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 5]
def baseStart_2576195 : Nat := 118140960795 + 2576195 * 2 ^ 59
def prefixEnd_2576195 : Nat := 4983230072969 + 3 ^ 40 * 2576195 * 2
def baseEnd_2576195 : Nat := 146980699412183706546089

theorem tailTrace_2576195 : CollatzResearch.WordTrace tailWord_2576195 prefixEnd_2576195 146980699412183706546089 := by
  unfold tailWord_2576195
  simp only [CollatzResearch.WordTrace]
  refine ⟨93961550901892968922586039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62641033934595312615057359 93961550901892968922586039)
  ·
    refine ⟨140942326352839453383879059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93961550901892968922586039 140942326352839453383879059)
    ·
      refine ⟨211413489529259180075818589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140942326352839453383879059 211413489529259180075818589)
      ·
        refine ⟨79280058573472192528431971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211413489529259180075818589 79280058573472192528431971)
        ·
          refine ⟨118920087860208288792647957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79280058573472192528431971 118920087860208288792647957)
          ·
            refine ⟨5574379118447263537155373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118920087860208288792647957 5574379118447263537155373)
            ·
              refine ⟨2090392169417723826433265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5574379118447263537155373 2090392169417723826433265)
              ·
                refine ⟨1567794127063292869824949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090392169417723826433265 1567794127063292869824949)
                ·
                  refine ⟨146980699412183706546089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567794127063292869824949 146980699412183706546089)
                  ·
                    rfl

theorem cell23_2576195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 5].length) (baseStart_2576195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576195 prefixEnd_2576195 := by exact prefixLift 2576195
  have htrace : WordTrace (prefixWord ++ tailWord_2576195) baseStart_2576195 baseEnd_2576195 := by
    simpa [prefixWord, tailWord_2576195, baseEnd_2576195] using wordTrace_append hprefix tailTrace_2576195
  have hstable : (prefixWord ++ tailWord_2576195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576195).length < 2 ^ (prefixWord ++ tailWord_2576195).sum := by decide
  have hdescent : baseEnd_2576195 < baseStart_2576195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576201 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_2576201 : Nat := 118140960795 + 2576201 * 2 ^ 59
def prefixEnd_2576201 : Nat := 4983230072969 + 3 ^ 40 * 2576201 * 2
def baseEnd_2576201 : Nat := 1322829375593580335439773

theorem tailTrace_2576201 : CollatzResearch.WordTrace tailWord_2576201 prefixEnd_2576201 1322829375593580335439773 := by
  unfold tailWord_2576201
  simp only [CollatzResearch.WordTrace]
  refine ⟨93961769739871231947304457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62641179826580821298202971 93961769739871231947304457)
  ·
    refine ⟨70471327304903423960478343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93961769739871231947304457 70471327304903423960478343)
    ·
      refine ⟨105706990957355135940717515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70471327304903423960478343 105706990957355135940717515)
      ·
        refine ⟨158560486436032703911076273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105706990957355135940717515 158560486436032703911076273)
        ·
          refine ⟨118920364827024527933307205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158560486436032703911076273 118920364827024527933307205)
          ·
            refine ⟨22297568405067098987495101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118920364827024527933307205 22297568405067098987495101)
            ·
              refine ⟨8361588151900162120310663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22297568405067098987495101 8361588151900162120310663)
              ·
                refine ⟨12542382227850243180465995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361588151900162120310663 12542382227850243180465995)
                ·
                  refine ⟨18813573341775364770698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542382227850243180465995 18813573341775364770698993)
                  ·
                    refine ⟨14110180006331523578024245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18813573341775364770698993 14110180006331523578024245)
                    ·
                      refine ⟨1322829375593580335439773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14110180006331523578024245 1322829375593580335439773)
                      ·
                        rfl

theorem cell23_2576201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_2576201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576201 prefixEnd_2576201 := by exact prefixLift 2576201
  have htrace : WordTrace (prefixWord ++ tailWord_2576201) baseStart_2576201 baseEnd_2576201 := by
    simpa [prefixWord, tailWord_2576201, baseEnd_2576201] using wordTrace_append hprefix tailTrace_2576201
  have hstable : (prefixWord ++ tailWord_2576201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576201).length < 2 ^ (prefixWord ++ tailWord_2576201).sum := by decide
  have hdescent : baseEnd_2576201 < baseStart_2576201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576241 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2576241 : Nat := 118140960795 + 2576241 * 2 ^ 59
def prefixEnd_2576241 : Nat := 4983230072969 + 3 ^ 40 * 2576241 * 2
def baseEnd_2576241 : Nat := 1322849914819760178939589

theorem tailTrace_2576241 : CollatzResearch.WordTrace tailWord_2576241 prefixEnd_2576241 1322849914819760178939589 := by
  unfold tailWord_2576241
  simp only [CollatzResearch.WordTrace]
  refine ⟨93963228659726318778760577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62642152439817545852507051 93963228659726318778760577)
  ·
    refine ⟨70472421494794739084070433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93963228659726318778760577 70472421494794739084070433)
    ·
      refine ⟨52854316121096054313052825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70472421494794739084070433 52854316121096054313052825)
      ·
        refine ⟨39640737090822040734789619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52854316121096054313052825 39640737090822040734789619)
        ·
          refine ⟨59461105636233061102184429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39640737090822040734789619 59461105636233061102184429)
          ·
            refine ⟨22297914613587397913319161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59461105636233061102184429 22297914613587397913319161)
            ·
              refine ⟨16723435960190548434989371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22297914613587397913319161 16723435960190548434989371)
              ·
                refine ⟨25085153940285822652484057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723435960190548434989371 25085153940285822652484057)
                ·
                  refine ⟨18813865455214366989363043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25085153940285822652484057 18813865455214366989363043)
                  ·
                    refine ⟨28220798182821550484044565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18813865455214366989363043 28220798182821550484044565)
                    ·
                      refine ⟨1322849914819760178939589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28220798182821550484044565 1322849914819760178939589)
                      ·
                        rfl

theorem cell23_2576241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2576241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576241 prefixEnd_2576241 := by exact prefixLift 2576241
  have htrace : WordTrace (prefixWord ++ tailWord_2576241) baseStart_2576241 baseEnd_2576241 := by
    simpa [prefixWord, tailWord_2576241, baseEnd_2576241] using wordTrace_append hprefix tailTrace_2576241
  have hstable : (prefixWord ++ tailWord_2576241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576241).length < 2 ^ (prefixWord ++ tailWord_2576241).sum := by decide
  have hdescent : baseEnd_2576241 < baseStart_2576241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576245 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2576245 : Nat := 118140960795 + 2576245 * 2 ^ 59
def prefixEnd_2576245 : Nat := 4983230072969 + 3 ^ 40 * 2576245 * 2
def baseEnd_2576245 : Nat := 1322851968742378163289571

theorem tailTrace_2576245 : CollatzResearch.WordTrace tailWord_2576245 prefixEnd_2576245 1322851968742378163289571 := by
  unfold tailWord_2576245
  simp only [CollatzResearch.WordTrace]
  refine ⟨93963374551711827461906189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62642249701141218307937459 93963374551711827461906189)
  ·
    refine ⟨35236265456891935298214821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93963374551711827461906189 35236265456891935298214821)
    ·
      refine ⟨6606799773167237868415279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35236265456891935298214821 6606799773167237868415279)
      ·
        refine ⟨9910199659750856802622919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606799773167237868415279 9910199659750856802622919)
        ·
          refine ⟨14865299489626285203934379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910199659750856802622919 14865299489626285203934379)
          ·
            refine ⟨22297949234439427805901569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14865299489626285203934379 22297949234439427805901569)
            ·
              refine ⟨16723461925829570854426177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22297949234439427805901569 16723461925829570854426177)
              ·
                refine ⟨12542596444372178140819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723461925829570854426177 12542596444372178140819633)
                ·
                  refine ⟨9406947333279133605614725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542596444372178140819633 9406947333279133605614725)
                  ·
                    refine ⟨1763802624989837551052761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9406947333279133605614725 1763802624989837551052761)
                    ·
                      refine ⟨1322851968742378163289571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763802624989837551052761 1322851968742378163289571)
                      ·
                        rfl

theorem cell23_2576245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2576245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576245 prefixEnd_2576245 := by exact prefixLift 2576245
  have htrace : WordTrace (prefixWord ++ tailWord_2576245) baseStart_2576245 baseEnd_2576245 := by
    simpa [prefixWord, tailWord_2576245, baseEnd_2576245] using wordTrace_append hprefix tailTrace_2576245
  have hstable : (prefixWord ++ tailWord_2576245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576245).length < 2 ^ (prefixWord ++ tailWord_2576245).sum := by decide
  have hdescent : baseEnd_2576245 < baseStart_2576245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576246 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2576246 : Nat := 118140960795 + 2576246 * 2 ^ 59
def prefixEnd_2576246 : Nat := 4983230072969 + 3 ^ 40 * 2576246 * 2
def baseEnd_2576246 : Nat := 146983609135892517708563

theorem tailTrace_2576246 : CollatzResearch.WordTrace tailWord_2576246 prefixEnd_2576246 146983609135892517708563 := by
  unfold tailWord_2576246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872713189044262789543287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62642274016472136421795061 5872713189044262789543287)
  ·
    refine ⟨8809069783566394184314931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5872713189044262789543287 8809069783566394184314931)
    ·
      refine ⟨13213604675349591276472397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8809069783566394184314931 13213604675349591276472397)
      ·
        refine ⟨4955101753256096728677149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13213604675349591276472397 4955101753256096728677149)
        ·
          refine ⟨1858163157471036273253931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4955101753256096728677149 1858163157471036273253931)
          ·
            refine ⟨2787244736206554409880897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858163157471036273253931 2787244736206554409880897)
            ·
              refine ⟨2090433552154915807410673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787244736206554409880897 2090433552154915807410673)
              ·
                refine ⟨1567825164116186855558005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090433552154915807410673 1567825164116186855558005)
                ·
                  refine ⟨146983609135892517708563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567825164116186855558005 146983609135892517708563)
                  ·
                    rfl

theorem cell23_2576246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2576246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576246 prefixEnd_2576246 := by exact prefixLift 2576246
  have htrace : WordTrace (prefixWord ++ tailWord_2576246) baseStart_2576246 baseEnd_2576246 := by
    simpa [prefixWord, tailWord_2576246, baseEnd_2576246] using wordTrace_append hprefix tailTrace_2576246
  have hstable : (prefixWord ++ tailWord_2576246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576246).length < 2 ^ (prefixWord ++ tailWord_2576246).sum := by decide
  have hdescent : baseEnd_2576246 < baseStart_2576246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576282 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2576282 : Nat := 118140960795 + 2576282 * 2 ^ 59
def prefixEnd_2576282 : Nat := 4983230072969 + 3 ^ 40 * 2576282 * 2
def baseEnd_2576282 : Nat := 1322870967526594518526901

theorem tailTrace_2576282 : CollatzResearch.WordTrace tailWord_2576282 prefixEnd_2576282 1322870967526594518526901 := by
  unfold tailWord_2576282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491181013144445695250775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62643149368385188520668733 23491181013144445695250775)
  ·
    refine ⟨35236771519716668542876163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23491181013144445695250775 35236771519716668542876163)
    ·
      refine ⟨52855157279575002814314245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35236771519716668542876163 52855157279575002814314245)
      ·
        refine ⟨9910341989920313027683921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52855157279575002814314245 9910341989920313027683921)
        ·
          refine ⟨7432756492440234770762941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9910341989920313027683921 7432756492440234770762941)
          ·
            refine ⟨2787283684665088039036103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7432756492440234770762941 2787283684665088039036103)
            ·
              refine ⟨4180925526997632058554155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787283684665088039036103 4180925526997632058554155)
              ·
                refine ⟨6271388290496448087831233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180925526997632058554155 6271388290496448087831233)
                ·
                  refine ⟨4703541217872336065873425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6271388290496448087831233 4703541217872336065873425)
                  ·
                    refine ⟨3527655913404252049405069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4703541217872336065873425 3527655913404252049405069)
                    ·
                      refine ⟨1322870967526594518526901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527655913404252049405069 1322870967526594518526901)
                      ·
                        rfl

theorem cell23_2576282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2576282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576282 prefixEnd_2576282 := by exact prefixLift 2576282
  have htrace : WordTrace (prefixWord ++ tailWord_2576282) baseStart_2576282 baseEnd_2576282 := by
    simpa [prefixWord, tailWord_2576282, baseEnd_2576282] using wordTrace_append hprefix tailTrace_2576282
  have hstable : (prefixWord ++ tailWord_2576282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576282).length < 2 ^ (prefixWord ++ tailWord_2576282).sum := by decide
  have hdescent : baseEnd_2576282 < baseStart_2576282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576289 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2576289 : Nat := 118140960795 + 2576289 * 2 ^ 59
def prefixEnd_2576289 : Nat := 4983230072969 + 3 ^ 40 * 2576289 * 2
def baseEnd_2576289 : Nat := 440958187297058663713123

theorem tailTrace_2576289 : CollatzResearch.WordTrace tailWord_2576289 prefixEnd_2576289 440958187297058663713123 := by
  unfold tailWord_2576289
  simp only [CollatzResearch.WordTrace]
  refine ⟨93964979363552422976507921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62643319575701615317671947 93964979363552422976507921)
  ·
    refine ⟨70473734522664317232380941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93964979363552422976507921 70473734522664317232380941)
    ·
      refine ⟨26427650445999118962142853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70473734522664317232380941 26427650445999118962142853)
      ·
        refine ⟨4955184458624834805401785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26427650445999118962142853 4955184458624834805401785)
        ·
          refine ⟨3716388343968626104051339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955184458624834805401785 3716388343968626104051339)
          ·
            refine ⟨5574582515952939156077009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716388343968626104051339 5574582515952939156077009)
            ·
              refine ⟨4180936886964704367057757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574582515952939156077009 4180936886964704367057757)
              ·
                refine ⟨1567851332611764137646659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4180936886964704367057757 1567851332611764137646659)
                ·
                  refine ⟨2351776998917646206469989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567851332611764137646659 2351776998917646206469989)
                  ·
                    refine ⟨440958187297058663713123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351776998917646206469989 440958187297058663713123)
                    ·
                      rfl

theorem cell23_2576289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2576289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576289 prefixEnd_2576289 := by exact prefixLift 2576289
  have htrace : WordTrace (prefixWord ++ tailWord_2576289) baseStart_2576289 baseEnd_2576289 := by
    simpa [prefixWord, tailWord_2576289, baseEnd_2576289] using wordTrace_append hprefix tailTrace_2576289
  have hstable : (prefixWord ++ tailWord_2576289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576289).length < 2 ^ (prefixWord ++ tailWord_2576289).sum := by decide
  have hdescent : baseEnd_2576289 < baseStart_2576289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576291 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2576291 : Nat := 118140960795 + 2576291 * 2 ^ 59
def prefixEnd_2576291 : Nat := 4983230072969 + 3 ^ 40 * 2576291 * 2
def baseEnd_2576291 : Nat := 1322875588852484983314359

theorem tailTrace_2576291 : CollatzResearch.WordTrace tailWord_2576291 prefixEnd_2576291 1322875588852484983314359 := by
  unfold tailWord_2576291
  simp only [CollatzResearch.WordTrace]
  refine ⟨93965052309545177318080727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62643368206363451545387151 93965052309545177318080727)
  ·
    refine ⟨140947578464317765977121091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93965052309545177318080727 140947578464317765977121091)
    ·
      refine ⟨211421367696476648965681637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140947578464317765977121091 211421367696476648965681637)
      ·
        refine ⟨39641506443089371681065307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211421367696476648965681637 39641506443089371681065307)
        ·
          refine ⟨59462259664634057521597961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39641506443089371681065307 59462259664634057521597961)
          ·
            refine ⟨44596694748475543141198471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59462259664634057521597961 44596694748475543141198471)
            ·
              refine ⟨66895042122713314711797707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44596694748475543141198471 66895042122713314711797707)
              ·
                refine ⟨100342563184069972067696561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66895042122713314711797707 100342563184069972067696561)
                ·
                  refine ⟨75256922388052479050772421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100342563184069972067696561 75256922388052479050772421)
                  ·
                    refine ⟨14110672947759839822019829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75256922388052479050772421 14110672947759839822019829)
                    ·
                      refine ⟨1322875588852484983314359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14110672947759839822019829 1322875588852484983314359)
                      ·
                        rfl

theorem cell23_2576291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2576291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576291 prefixEnd_2576291 := by exact prefixLift 2576291
  have htrace : WordTrace (prefixWord ++ tailWord_2576291) baseStart_2576291 baseEnd_2576291 := by
    simpa [prefixWord, tailWord_2576291, baseEnd_2576291] using wordTrace_append hprefix tailTrace_2576291
  have hstable : (prefixWord ++ tailWord_2576291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576291).length < 2 ^ (prefixWord ++ tailWord_2576291).sum := by decide
  have hdescent : baseEnd_2576291 < baseStart_2576291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576312 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_2576312 : Nat := 118140960795 + 2576312 * 2 ^ 59
def prefixEnd_2576312 : Nat := 4983230072969 + 3 ^ 40 * 2576312 * 2
def baseEnd_2576312 : Nat := 1322886371946229401151763

theorem tailTrace_2576312 : CollatzResearch.WordTrace tailWord_2576312 prefixEnd_2576312 1322886371946229401151763 := by
  unfold tailWord_2576312
  simp only [CollatzResearch.WordTrace]
  refine ⟨46982909121234548952297595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62643878828312731936396793 46982909121234548952297595)
  ·
    refine ⟨70474363681851823428446393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46982909121234548952297595 70474363681851823428446393)
    ·
      refine ⟨52855772761388867571334795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70474363681851823428446393 52855772761388867571334795)
      ·
        refine ⟨79283659142083301357002193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52855772761388867571334795 79283659142083301357002193)
        ·
          refine ⟨59462744356562476017751645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79283659142083301357002193 59462744356562476017751645)
          ·
            refine ⟨22298529133710928506656867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59462744356562476017751645 22298529133710928506656867)
            ·
              refine ⟨33447793700566392759985301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22298529133710928506656867 33447793700566392759985301)
              ·
                refine ⟨1567865329714049660624311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33447793700566392759985301 1567865329714049660624311)
                ·
                  refine ⟨2351797994571074490936467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567865329714049660624311 2351797994571074490936467)
                  ·
                    refine ⟨3527696991856611736404701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351797994571074490936467 3527696991856611736404701)
                    ·
                      refine ⟨1322886371946229401151763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527696991856611736404701 1322886371946229401151763)
                      ·
                        rfl

theorem cell23_2576312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_2576312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576312 prefixEnd_2576312 := by exact prefixLift 2576312
  have htrace : WordTrace (prefixWord ++ tailWord_2576312) baseStart_2576312 baseEnd_2576312 := by
    simpa [prefixWord, tailWord_2576312, baseEnd_2576312] using wordTrace_append hprefix tailTrace_2576312
  have hstable : (prefixWord ++ tailWord_2576312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576312).length < 2 ^ (prefixWord ++ tailWord_2576312).sum := by decide
  have hdescent : baseEnd_2576312 < baseStart_2576312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576335 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_2576335 : Nat := 118140960795 + 2576335 * 2 ^ 59
def prefixEnd_2576335 : Nat := 4983230072969 + 3 ^ 40 * 2576335 * 2
def baseEnd_2576335 : Nat := 1322898182001282811164157

theorem tailTrace_2576335 : CollatzResearch.WordTrace tailWord_2576335 prefixEnd_2576335 1322898182001282811164157 := by
  unfold tailWord_2576335
  simp only [CollatzResearch.WordTrace]
  refine ⟨93966657121385772832682459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62644438080923848555121639 93966657121385772832682459)
  ·
    refine ⟨140949985682078659249023689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93966657121385772832682459 140949985682078659249023689)
    ·
      refine ⟨105712489261558994436767767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140949985682078659249023689 105712489261558994436767767)
      ·
        refine ⟨158568733892338491655151651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105712489261558994436767767 158568733892338491655151651)
        ·
          refine ⟨237853100838507737482727477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158568733892338491655151651 237853100838507737482727477)
          ·
            refine ⟨22298728203610100389005701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237853100838507737482727477 22298728203610100389005701)
            ·
              refine ⟨4181011538176893822938569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22298728203610100389005701 4181011538176893822938569)
              ·
                refine ⟨3135758653632670367203927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181011538176893822938569 3135758653632670367203927)
                ·
                  refine ⟨4703637980449005550805891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135758653632670367203927 4703637980449005550805891)
                  ·
                    refine ⟨7055456970673508326208837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703637980449005550805891 7055456970673508326208837)
                    ·
                      refine ⟨1322898182001282811164157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7055456970673508326208837 1322898182001282811164157)
                      ·
                        rfl

theorem cell23_2576335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_2576335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576335 prefixEnd_2576335 := by exact prefixLift 2576335
  have htrace : WordTrace (prefixWord ++ tailWord_2576335) baseStart_2576335 baseEnd_2576335 := by
    simpa [prefixWord, tailWord_2576335, baseEnd_2576335] using wordTrace_append hprefix tailTrace_2576335
  have hstable : (prefixWord ++ tailWord_2576335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576335).length < 2 ^ (prefixWord ++ tailWord_2576335).sum := by decide
  have hdescent : baseEnd_2576335 < baseStart_2576335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576346 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_2576346 : Nat := 118140960795 + 2576346 * 2 ^ 59
def prefixEnd_2576346 : Nat := 4983230072969 + 3 ^ 40 * 2576346 * 2
def baseEnd_2576346 : Nat := 1322903830288482268126607

theorem tailTrace_2576346 : CollatzResearch.WordTrace tailWord_2576346 prefixEnd_2576346 1322903830288482268126607 := by
  unfold tailWord_2576346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491764581086480427833223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62644705549563947807555261 23491764581086480427833223)
  ·
    refine ⟨35237646871629720641749835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23491764581086480427833223 35237646871629720641749835)
    ·
      refine ⟨52856470307444580962624753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35237646871629720641749835 52856470307444580962624753)
      ·
        refine ⟨39642352730583435721968565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52856470307444580962624753 39642352730583435721968565)
        ·
          refine ⟨3716470568492197098934553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39642352730583435721968565 3716470568492197098934553)
          ·
            refine ⟨2787352926369147824200915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3716470568492197098934553 2787352926369147824200915)
            ·
              refine ⟨4181029389553721736301373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787352926369147824200915 4181029389553721736301373)
              ·
                refine ⟨1567886021082645651113015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181029389553721736301373 1567886021082645651113015)
                ·
                  refine ⟨2351829031623968476669523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567886021082645651113015 2351829031623968476669523)
                  ·
                    refine ⟨3527743547435952715004285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351829031623968476669523 3527743547435952715004285)
                    ·
                      refine ⟨1322903830288482268126607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527743547435952715004285 1322903830288482268126607)
                      ·
                        rfl

theorem cell23_2576346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_2576346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576346 prefixEnd_2576346 := by exact prefixLift 2576346
  have htrace : WordTrace (prefixWord ++ tailWord_2576346) baseStart_2576346 baseEnd_2576346 := by
    simpa [prefixWord, tailWord_2576346, baseEnd_2576346] using wordTrace_append hprefix tailTrace_2576346
  have hstable : (prefixWord ++ tailWord_2576346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576346).length < 2 ^ (prefixWord ++ tailWord_2576346).sum := by decide
  have hdescent : baseEnd_2576346 < baseStart_2576346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576355 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2576355 : Nat := 118140960795 + 2576355 * 2 ^ 59
def prefixEnd_2576355 : Nat := 4983230072969 + 3 ^ 40 * 2576355 * 2
def baseEnd_2576355 : Nat := 1322908451614372732914065

theorem tailTrace_2576355 : CollatzResearch.WordTrace tailWord_2576355 prefixEnd_2576355 1322908451614372732914065 := by
  unfold tailWord_2576355
  simp only [CollatzResearch.WordTrace]
  refine ⟨93967386581313316248410519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62644924387542210832273679 93967386581313316248410519)
  ·
    refine ⟨140951079871969974372615779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93967386581313316248410519 140951079871969974372615779)
    ·
      refine ⟨211426619807954961558923669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140951079871969974372615779 211426619807954961558923669)
      ·
        refine ⟨9910622803497888823074547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211426619807954961558923669 9910622803497888823074547)
        ·
          refine ⟨14865934205246833234611821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910622803497888823074547 14865934205246833234611821)
          ·
            refine ⟨5574725326967562462979433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14865934205246833234611821 5574725326967562462979433)
            ·
              refine ⟨4181043995225671847234575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574725326967562462979433 4181043995225671847234575)
              ·
                refine ⟨6271565992838507770851863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181043995225671847234575 6271565992838507770851863)
                ·
                  refine ⟨9407348989257761656277795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271565992838507770851863 9407348989257761656277795)
                  ·
                    refine ⟨14111023483886642484416693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9407348989257761656277795 14111023483886642484416693)
                    ·
                      refine ⟨1322908451614372732914065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14111023483886642484416693 1322908451614372732914065)
                      ·
                        rfl

theorem cell23_2576355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2576355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576355 prefixEnd_2576355 := by exact prefixLift 2576355
  have htrace : WordTrace (prefixWord ++ tailWord_2576355) baseStart_2576355 baseEnd_2576355 := by
    simpa [prefixWord, tailWord_2576355, baseEnd_2576355] using wordTrace_append hprefix tailTrace_2576355
  have hstable : (prefixWord ++ tailWord_2576355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576355).length < 2 ^ (prefixWord ++ tailWord_2576355).sum := by decide
  have hdescent : baseEnd_2576355 < baseStart_2576355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576385 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2576385 : Nat := 118140960795 + 2576385 * 2 ^ 59
def prefixEnd_2576385 : Nat := 4983230072969 + 3 ^ 40 * 2576385 * 2
def baseEnd_2576385 : Nat := 1322923856034007615538927

theorem tailTrace_2576385 : CollatzResearch.WordTrace tailWord_2576385 prefixEnd_2576385 1322923856034007615538927 := by
  unfold tailWord_2576385
  simp only [CollatzResearch.WordTrace]
  refine ⟨93968480771204631372002609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62645653847469754248001739 93968480771204631372002609)
  ·
    refine ⟨70476360578403473529001957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93968480771204631372002609 70476360578403473529001957)
    ·
      refine ⟨13214317608450651286687867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70476360578403473529001957 13214317608450651286687867)
      ·
        refine ⟨19821476412675976930031801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13214317608450651286687867 19821476412675976930031801)
        ·
          refine ⟨14866107309506982697523851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19821476412675976930031801 14866107309506982697523851)
          ·
            refine ⟨22299160964260474046285777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866107309506982697523851 22299160964260474046285777)
            ·
              refine ⟨16724370723195355534714333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22299160964260474046285777 16724370723195355534714333)
              ·
                refine ⟨6271639021198258325517875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16724370723195355534714333 6271639021198258325517875)
                ·
                  refine ⟨9407458531797387488276813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271639021198258325517875 9407458531797387488276813)
                  ·
                    refine ⟨3527796949424020308103805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9407458531797387488276813 3527796949424020308103805)
                    ·
                      refine ⟨1322923856034007615538927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527796949424020308103805 1322923856034007615538927)
                      ·
                        rfl

theorem cell23_2576385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2576385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576385 prefixEnd_2576385 := by exact prefixLift 2576385
  have htrace : WordTrace (prefixWord ++ tailWord_2576385) baseStart_2576385 baseEnd_2576385 := by
    simpa [prefixWord, tailWord_2576385, baseEnd_2576385] using wordTrace_append hprefix tailTrace_2576385
  have hstable : (prefixWord ++ tailWord_2576385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576385).length < 2 ^ (prefixWord ++ tailWord_2576385).sum := by decide
  have hdescent : baseEnd_2576385 < baseStart_2576385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576390 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2576390 : Nat := 118140960795 + 2576390 * 2 ^ 59
def prefixEnd_2576390 : Nat := 4983230072969 + 3 ^ 40 * 2576390 * 2
def baseEnd_2576390 : Nat := 1322926423437280095976405

theorem tailTrace_2576390 : CollatzResearch.WordTrace tailWord_2576390 prefixEnd_2576390 1322926423437280095976405 := by
  unfold tailWord_2576390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936520723005828663310457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62645775424124344817289749 2936520723005828663310457)
  ·
    refine ⟨2202390542254371497482843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2936520723005828663310457 2202390542254371497482843)
    ·
      refine ⟨3303585813381557246224265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202390542254371497482843 3303585813381557246224265)
      ·
        refine ⟨2477689360036167934668199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303585813381557246224265 2477689360036167934668199)
        ·
          refine ⟨3716534040054251902002299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477689360036167934668199 3716534040054251902002299)
          ·
            refine ⟨5574801060081377853003449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716534040054251902002299 5574801060081377853003449)
            ·
              refine ⟨4181100795061033389752587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574801060081377853003449 4181100795061033389752587)
              ·
                refine ⟨6271651192591550084628881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181100795061033389752587 6271651192591550084628881)
                ·
                  refine ⟨4703738394443662563471661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6271651192591550084628881 4703738394443662563471661)
                  ·
                    refine ⟨1763901897916373461301873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4703738394443662563471661 1763901897916373461301873)
                    ·
                      refine ⟨1322926423437280095976405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763901897916373461301873 1322926423437280095976405)
                      ·
                        rfl

theorem cell23_2576390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2576390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576390 prefixEnd_2576390 := by exact prefixLift 2576390
  have htrace : WordTrace (prefixWord ++ tailWord_2576390) baseStart_2576390 baseEnd_2576390 := by
    simpa [prefixWord, tailWord_2576390, baseEnd_2576390] using wordTrace_append hprefix tailTrace_2576390
  have hstable : (prefixWord ++ tailWord_2576390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576390).length < 2 ^ (prefixWord ++ tailWord_2576390).sum := by decide
  have hdescent : baseEnd_2576390 < baseStart_2576390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576420 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2576420 : Nat := 118140960795 + 2576420 * 2 ^ 59
def prefixEnd_2576420 : Nat := 4983230072969 + 3 ^ 40 * 2576420 * 2
def baseEnd_2576420 : Nat := 1322941827856914978601267

theorem tailTrace_2576420 : CollatzResearch.WordTrace tailWord_2576420 prefixEnd_2576420 1322941827856914978601267 := by
  unfold tailWord_2576420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46984878663038916174763357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62646504884051888233017809 46984878663038916174763357)
  ·
    refine ⟨17619329498639593565536259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46984878663038916174763357 17619329498639593565536259)
    ·
      refine ⟨26428994247959390348304389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17619329498639593565536259 26428994247959390348304389)
      ·
        refine ⟨4955436421492385690307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26428994247959390348304389 4955436421492385690307073)
        ·
          refine ⟨3716577316119289267730305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955436421492385690307073 3716577316119289267730305)
          ·
            refine ⟨2787432987089466950797729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3716577316119289267730305 2787432987089466950797729)
            ·
              refine ⟨2090574740317100213098297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787432987089466950797729 2090574740317100213098297)
              ·
                refine ⟨1567931055237825159823723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090574740317100213098297 1567931055237825159823723)
                ·
                  refine ⟨2351896582856737739735585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567931055237825159823723 2351896582856737739735585)
                  ·
                    refine ⟨1763922437142553304801689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351896582856737739735585 1763922437142553304801689)
                    ·
                      refine ⟨1322941827856914978601267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763922437142553304801689 1322941827856914978601267)
                      ·
                        rfl

theorem cell23_2576420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2576420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576420 prefixEnd_2576420 := by exact prefixLift 2576420
  have htrace : WordTrace (prefixWord ++ tailWord_2576420) baseStart_2576420 baseEnd_2576420 := by
    simpa [prefixWord, tailWord_2576420, baseEnd_2576420] using wordTrace_append hprefix tailTrace_2576420
  have hstable : (prefixWord ++ tailWord_2576420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576420).length < 2 ^ (prefixWord ++ tailWord_2576420).sum := by decide
  have hdescent : baseEnd_2576420 < baseStart_2576420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2576428 : Nat := 118140960795 + 2576428 * 2 ^ 59
def prefixEnd_2576428 : Nat := 4983230072969 + 3 ^ 40 * 2576428 * 2
def baseEnd_2576428 : Nat := 1322945935702150947301229

theorem tailTrace_2576428 : CollatzResearch.WordTrace tailWord_2576428 prefixEnd_2576428 1322945935702150947301229 := by
  unfold tailWord_2576428
  simp only [CollatzResearch.WordTrace]
  refine ⟨46985024555024424857908969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62646699406699233143878625 46985024555024424857908969)
  ·
    refine ⟨35238768416268318643431727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46985024555024424857908969 35238768416268318643431727)
    ·
      refine ⟨52858152624402477965147591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35238768416268318643431727 52858152624402477965147591)
      ·
        refine ⟨79287228936603716947721387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52858152624402477965147591 79287228936603716947721387)
        ·
          refine ⟨118930843404905575421582081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79287228936603716947721387 118930843404905575421582081)
          ·
            refine ⟨89198132553679181566186561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118930843404905575421582081 89198132553679181566186561)
            ·
              refine ⟨66898599415259386174639921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89198132553679181566186561 66898599415259386174639921)
              ·
                refine ⟨50173949561444539630979941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66898599415259386174639921 50173949561444539630979941)
                ·
                  refine ⟨9407615542770851180808739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50173949561444539630979941 9407615542770851180808739)
                  ·
                    refine ⟨14111423314156276771213109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9407615542770851180808739 14111423314156276771213109)
                    ·
                      refine ⟨1322945935702150947301229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14111423314156276771213109 1322945935702150947301229)
                      ·
                        rfl

theorem cell23_2576428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2576428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576428 prefixEnd_2576428 := by exact prefixLift 2576428
  have htrace : WordTrace (prefixWord ++ tailWord_2576428) baseStart_2576428 baseEnd_2576428 := by
    simpa [prefixWord, tailWord_2576428, baseEnd_2576428] using wordTrace_append hprefix tailTrace_2576428
  have hstable : (prefixWord ++ tailWord_2576428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576428).length < 2 ^ (prefixWord ++ tailWord_2576428).sum := by decide
  have hdescent : baseEnd_2576428 < baseStart_2576428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576442 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_2576442 : Nat := 118140960795 + 2576442 * 2 ^ 59
def prefixEnd_2576442 : Nat := 4983230072969 + 3 ^ 40 * 2576442 * 2
def baseEnd_2576442 : Nat := 1322953124431313892526165

theorem tailTrace_2576442 : CollatzResearch.WordTrace tailWord_2576442 prefixEnd_2576442 1322953124431313892526165 := by
  unfold tailWord_2576442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492639932999532526706895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62647039821332086737885053 23492639932999532526706895)
  ·
    refine ⟨35238959899499298790060343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23492639932999532526706895 35238959899499298790060343)
    ·
      refine ⟨52858439849248948185090515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35238959899499298790060343 52858439849248948185090515)
      ·
        refine ⟨79287659773873422277635773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52858439849248948185090515 79287659773873422277635773)
        ·
          refine ⟨29732872415202533354113415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79287659773873422277635773 29732872415202533354113415)
          ·
            refine ⟨44599308622803800031170123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29732872415202533354113415 44599308622803800031170123)
            ·
              refine ⟨66898962934205700046755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44599308622803800031170123 66898962934205700046755185)
              ·
                refine ⟨50174222200654275035066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66898962934205700046755185 50174222200654275035066389)
                ·
                  refine ⟨2351916665655669142268737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50174222200654275035066389 2351916665655669142268737)
                  ·
                    refine ⟨1763937499241751856701553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351916665655669142268737 1763937499241751856701553)
                    ·
                      refine ⟨1322953124431313892526165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763937499241751856701553 1322953124431313892526165)
                      ·
                        rfl

theorem cell23_2576442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_2576442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576442 prefixEnd_2576442 := by exact prefixLift 2576442
  have htrace : WordTrace (prefixWord ++ tailWord_2576442) baseStart_2576442 baseEnd_2576442 := by
    simpa [prefixWord, tailWord_2576442, baseEnd_2576442] using wordTrace_append hprefix tailTrace_2576442
  have hstable : (prefixWord ++ tailWord_2576442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576442).length < 2 ^ (prefixWord ++ tailWord_2576442).sum := by decide
  have hdescent : baseEnd_2576442 < baseStart_2576442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576445 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2576445 : Nat := 118140960795 + 2576445 * 2 ^ 59
def prefixEnd_2576445 : Nat := 4983230072969 + 3 ^ 40 * 2576445 * 2
def baseEnd_2576445 : Nat := 1322954664873277380788651

theorem tailTrace_2576445 : CollatzResearch.WordTrace tailWord_2576445 prefixEnd_2576445 1322954664873277380788651 := by
  unfold tailWord_2576445
  simp only [CollatzResearch.WordTrace]
  refine ⟨93970669150987261619186789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62647112767324841079457859 93970669150987261619186789)
  ·
    refine ⟨17619500465810111553597523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93970669150987261619186789 17619500465810111553597523)
    ·
      refine ⟨26429250698715167330396285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17619500465810111553597523 26429250698715167330396285)
      ·
        refine ⟨9910969012018187748898607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26429250698715167330396285 9910969012018187748898607)
        ·
          refine ⟨14866453518027281623347911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910969012018187748898607 14866453518027281623347911)
          ·
            refine ⟨22299680277040922435021867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866453518027281623347911 22299680277040922435021867)
            ·
              refine ⟨33449520415561383652532801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22299680277040922435021867 33449520415561383652532801)
              ·
                refine ⟨25087140311671037739399601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33449520415561383652532801 25087140311671037739399601)
                ·
                  refine ⟨18815355233753278304549701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25087140311671037739399601 18815355233753278304549701)
                  ·
                    refine ⟨3527879106328739682103069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18815355233753278304549701 3527879106328739682103069)
                    ·
                      refine ⟨1322954664873277380788651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3527879106328739682103069 1322954664873277380788651)
                      ·
                        rfl

theorem cell23_2576445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2576445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576445 prefixEnd_2576445 := by exact prefixLift 2576445
  have htrace : WordTrace (prefixWord ++ tailWord_2576445) baseStart_2576445 baseEnd_2576445 := by
    simpa [prefixWord, tailWord_2576445, baseEnd_2576445] using wordTrace_append hprefix tailTrace_2576445
  have hstable : (prefixWord ++ tailWord_2576445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576445).length < 2 ^ (prefixWord ++ tailWord_2576445).sum := by decide
  have hdescent : baseEnd_2576445 < baseStart_2576445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576448 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 9]
def baseStart_2576448 : Nat := 118140960795 + 2576448 * 2 ^ 59
def prefixEnd_2576448 : Nat := 4983230072969 + 3 ^ 40 * 2576448 * 2
def baseEnd_2576448 : Nat := 146995133923915652116793

theorem tailTrace_2576448 : CollatzResearch.WordTrace tailWord_2576448 prefixEnd_2576448 146995133923915652116793 := by
  unfold tailWord_2576448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46985389284988196565772999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62647185713317595421030665 46985389284988196565772999)
  ·
    refine ⟨70478083927482294848659499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46985389284988196565772999 70478083927482294848659499)
    ·
      refine ⟨105717125891223442272989249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70478083927482294848659499 105717125891223442272989249)
      ·
        refine ⟨79287844418417581704741937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105717125891223442272989249 79287844418417581704741937)
        ·
          refine ⟨59465883313813186278556453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79287844418417581704741937 59465883313813186278556453)
          ·
            refine ⟨11149853121339972427229335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59465883313813186278556453 11149853121339972427229335)
            ·
              refine ⟨16724779682009958640844003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11149853121339972427229335 16724779682009958640844003)
              ·
                refine ⟨25087169523014937961266005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16724779682009958640844003 25087169523014937961266005)
                ·
                  refine ⟨146995133923915652116793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25087169523014937961266005 146995133923915652116793)
                  ·
                    rfl

theorem cell23_2576448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_2576448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576448 prefixEnd_2576448 := by exact prefixLift 2576448
  have htrace : WordTrace (prefixWord ++ tailWord_2576448) baseStart_2576448 baseEnd_2576448 := by
    simpa [prefixWord, tailWord_2576448, baseEnd_2576448] using wordTrace_append hprefix tailTrace_2576448
  have hstable : (prefixWord ++ tailWord_2576448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576448).length < 2 ^ (prefixWord ++ tailWord_2576448).sum := by decide
  have hdescent : baseEnd_2576448 < baseStart_2576448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_2576458 : Nat := 118140960795 + 2576458 * 2 ^ 59
def prefixEnd_2576458 : Nat := 4983230072969 + 3 ^ 40 * 2576458 * 2
def baseEnd_2576458 : Nat := 1322961340121785829926091

theorem tailTrace_2576458 : CollatzResearch.WordTrace tailWord_2576458 prefixEnd_2576458 1322961340121785829926091 := by
  unfold tailWord_2576458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492785824985041209852507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62647428866626776559606685 23492785824985041209852507)
  ·
    refine ⟨35239178737477561814778761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23492785824985041209852507 35239178737477561814778761)
    ·
      refine ⟨26429384053108171361084071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35239178737477561814778761 26429384053108171361084071)
      ·
        refine ⟨39644076079662257041626107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26429384053108171361084071 39644076079662257041626107)
        ·
          refine ⟨59466114119493385562439161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39644076079662257041626107 59466114119493385562439161)
          ·
            refine ⟨44599585589620039171829371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59466114119493385562439161 44599585589620039171829371)
            ·
              refine ⟨66899378384430058757744057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44599585589620039171829371 66899378384430058757744057)
              ·
                refine ⟨50174533788322544068308043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66899378384430058757744057 50174533788322544068308043)
                ·
                  refine ⟨75261800682483816102462065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50174533788322544068308043 75261800682483816102462065)
                  ·
                    refine ⟨56446350511862862076846549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75261800682483816102462065 56446350511862862076846549)
                    ·
                      refine ⟨1322961340121785829926091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56446350511862862076846549 1322961340121785829926091)
                      ·
                        rfl

theorem cell23_2576458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_2576458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576458 prefixEnd_2576458 := by exact prefixLift 2576458
  have htrace : WordTrace (prefixWord ++ tailWord_2576458) baseStart_2576458 baseEnd_2576458 := by
    simpa [prefixWord, tailWord_2576458, baseEnd_2576458] using wordTrace_append hprefix tailTrace_2576458
  have hstable : (prefixWord ++ tailWord_2576458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576458).length < 2 ^ (prefixWord ++ tailWord_2576458).sum := by decide
  have hdescent : baseEnd_2576458 < baseStart_2576458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576476 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2576476 : Nat := 118140960795 + 2576476 * 2 ^ 59
def prefixEnd_2576476 : Nat := 4983230072969 + 3 ^ 40 * 2576476 * 2
def baseEnd_2576476 : Nat := 1322970582773566759501009

theorem tailTrace_2576476 : CollatzResearch.WordTrace tailWord_2576476 prefixEnd_2576476 1322970582773566759501009 := by
  unfold tailWord_2576476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46985899906937476956782641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62647866542583302609043521 46985899906937476956782641)
  ·
    refine ⟨35239424930203107717586981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46985899906937476956782641 35239424930203107717586981)
    ·
      refine ⟨6607392174413082697047559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35239424930203107717586981 6607392174413082697047559)
      ·
        refine ⟨9911088261619624045571339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607392174413082697047559 9911088261619624045571339)
        ·
          refine ⟨14866632392429436068357009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911088261619624045571339 14866632392429436068357009)
          ·
            refine ⟨11149974294322077051267757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14866632392429436068357009 11149974294322077051267757)
            ·
              refine ⟨4181240360370778894225409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11149974294322077051267757 4181240360370778894225409)
              ·
                refine ⟨3135930270278084170669057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181240360370778894225409 3135930270278084170669057)
                ·
                  refine ⟨2351947702708563128001793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135930270278084170669057 2351947702708563128001793)
                  ·
                    refine ⟨1763960777031422346001345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351947702708563128001793 1763960777031422346001345)
                    ·
                      refine ⟨1322970582773566759501009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1763960777031422346001345 1322970582773566759501009)
                      ·
                        rfl

theorem cell23_2576476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2576476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576476 prefixEnd_2576476 := by exact prefixLift 2576476
  have htrace : WordTrace (prefixWord ++ tailWord_2576476) baseStart_2576476 baseEnd_2576476 := by
    simpa [prefixWord, tailWord_2576476, baseEnd_2576476] using wordTrace_append hprefix tailTrace_2576476
  have hstable : (prefixWord ++ tailWord_2576476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576476).length < 2 ^ (prefixWord ++ tailWord_2576476).sum := by decide
  have hdescent : baseEnd_2576476 < baseStart_2576476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576515 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2576515 : Nat := 118140960795 + 2576515 * 2 ^ 59
def prefixEnd_2576515 : Nat := 4983230072969 + 3 ^ 40 * 2576515 * 2
def baseEnd_2576515 : Nat := 1322990608519092106913329

theorem tailTrace_2576515 : CollatzResearch.WordTrace tailWord_2576515 prefixEnd_2576515 1322990608519092106913329 := by
  unfold tailWord_2576515
  simp only [CollatzResearch.WordTrace]
  refine ⟨93973222260733663574234999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62648814840489109049489999 93973222260733663574234999)
  ·
    refine ⟨140959833391100495361352499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93973222260733663574234999 140959833391100495361352499)
    ·
      refine ⟨211439750086650743042028749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140959833391100495361352499 211439750086650743042028749)
      ·
        refine ⟨79289906282494028640760781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211439750086650743042028749 79289906282494028640760781)
        ·
          refine ⟨29733714855935260740285293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79289906282494028640760781 29733714855935260740285293)
          ·
            refine ⟨11150143070975722777606985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29733714855935260740285293 11150143070975722777606985)
            ·
              refine ⟨8362607303231792083205239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11150143070975722777606985 8362607303231792083205239)
              ·
                refine ⟨12543910954847688124807859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8362607303231792083205239 12543910954847688124807859)
                ·
                  refine ⟨18815866432271532187211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12543910954847688124807859 18815866432271532187211789)
                  ·
                    refine ⟨7055949912101824570204421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18815866432271532187211789 7055949912101824570204421)
                    ·
                      refine ⟨1322990608519092106913329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7055949912101824570204421 1322990608519092106913329)
                      ·
                        rfl

theorem cell23_2576515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2576515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576515 prefixEnd_2576515 := by exact prefixLift 2576515
  have htrace : WordTrace (prefixWord ++ tailWord_2576515) baseStart_2576515 baseEnd_2576515 := by
    simpa [prefixWord, tailWord_2576515, baseEnd_2576515] using wordTrace_append hprefix tailTrace_2576515
  have hstable : (prefixWord ++ tailWord_2576515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576515).length < 2 ^ (prefixWord ++ tailWord_2576515).sum := by decide
  have hdescent : baseEnd_2576515 < baseStart_2576515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576626 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2576626 : Nat := 118140960795 + 2576626 * 2 ^ 59
def prefixEnd_2576626 : Nat := 4983230072969 + 3 ^ 40 * 2576626 * 2
def baseEnd_2576626 : Nat := 1323047604871741172625319

theorem tailTrace_2576626 : CollatzResearch.WordTrace tailWord_2576626 prefixEnd_2576626 1323047604871741172625319 := by
  unfold tailWord_2576626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23494317690832882382881433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62651513842221019687683821 23494317690832882382881433)
  ·
    refine ⟨17620738268124661787161075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23494317690832882382881433 17620738268124661787161075)
    ·
      refine ⟨26431107402186992680741613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17620738268124661787161075 26431107402186992680741613)
      ·
        refine ⟨9911665275820122255278105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26431107402186992680741613 9911665275820122255278105)
        ·
          refine ⟨7433748956865091691458579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9911665275820122255278105 7433748956865091691458579)
          ·
            refine ⟨11150623435297637537187869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433748956865091691458579 11150623435297637537187869)
            ·
              refine ⟨4181483788236614076445451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11150623435297637537187869 4181483788236614076445451)
              ·
                refine ⟨6272225682354921114668177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181483788236614076445451 6272225682354921114668177)
                ·
                  refine ⟨4704169261766190836001133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272225682354921114668177 4704169261766190836001133)
                  ·
                    refine ⟨1764063473162321563500425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4704169261766190836001133 1764063473162321563500425)
                    ·
                      refine ⟨1323047604871741172625319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764063473162321563500425 1323047604871741172625319)
                      ·
                        rfl

theorem cell23_2576626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2576626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576626 prefixEnd_2576626 := by exact prefixLift 2576626
  have htrace : WordTrace (prefixWord ++ tailWord_2576626) baseStart_2576626 baseEnd_2576626 := by
    simpa [prefixWord, tailWord_2576626, baseEnd_2576626] using wordTrace_append hprefix tailTrace_2576626
  have hstable : (prefixWord ++ tailWord_2576626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576626).length < 2 ^ (prefixWord ++ tailWord_2576626).sum := by decide
  have hdescent : baseEnd_2576626 < baseStart_2576626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576636 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_2576636 : Nat := 118140960795 + 2576636 * 2 ^ 59
def prefixEnd_2576636 : Nat := 4983230072969 + 3 ^ 40 * 2576636 * 2
def baseEnd_2576636 : Nat := 441017579892762044500091

theorem tailTrace_2576636 : CollatzResearch.WordTrace tailWord_2576636 prefixEnd_2576636 441017579892762044500091 := by
  unfold tailWord_2576636
  simp only [CollatzResearch.WordTrace]
  refine ⟨46988817746647650619694881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62651756995530200826259841 46988817746647650619694881)
  ·
    refine ⟨35241613309985737964771161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46988817746647650619694881 35241613309985737964771161)
    ·
      refine ⟨26431209982489303473578371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35241613309985737964771161 26431209982489303473578371)
      ·
        refine ⟨39646814973733955210367557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26431209982489303473578371 39646814973733955210367557)
        ·
          refine ⟨7433777807575116601943917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39646814973733955210367557 7433777807575116601943917)
          ·
            refine ⟨2787666677840668725728969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7433777807575116601943917 2787666677840668725728969)
            ·
              refine ⟨2090750008380501544296727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787666677840668725728969 2090750008380501544296727)
              ·
                refine ⟨3136125012570752316445091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090750008380501544296727 3136125012570752316445091)
                ·
                  refine ⟨4704187518856128474667637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136125012570752316445091 4704187518856128474667637)
                  ·
                    refine ⟨441017579892762044500091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4704187518856128474667637 441017579892762044500091)
                    ·
                      rfl

theorem cell23_2576636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_2576636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576636 prefixEnd_2576636 := by exact prefixLift 2576636
  have htrace : WordTrace (prefixWord ++ tailWord_2576636) baseStart_2576636 baseEnd_2576636 := by
    simpa [prefixWord, tailWord_2576636, baseEnd_2576636] using wordTrace_append hprefix tailTrace_2576636
  have hstable : (prefixWord ++ tailWord_2576636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576636).length < 2 ^ (prefixWord ++ tailWord_2576636).sum := by decide
  have hdescent : baseEnd_2576636 < baseStart_2576636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576639 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 5, 2, 2]
def baseStart_2576639 : Nat := 118140960795 + 2576639 * 2 ^ 59
def prefixEnd_2576639 : Nat := 4983230072969 + 3 ^ 40 * 2576639 * 2
def baseEnd_2576639 : Nat := 1323054280120249621762759

theorem tailTrace_2576639 : CollatzResearch.WordTrace tailWord_2576639 prefixEnd_2576639 1323054280120249621762759 := by
  unfold tailWord_2576639
  simp only [CollatzResearch.WordTrace]
  refine ⟨93977744912284432751748971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62651829941522955167832647 93977744912284432751748971)
  ·
    refine ⟨140966617368426649127623457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93977744912284432751748971 140966617368426649127623457)
    ·
      refine ⟨105724963026319986845717593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140966617368426649127623457 105724963026319986845717593)
      ·
        refine ⟨79293722269739990134288195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105724963026319986845717593 79293722269739990134288195)
        ·
          refine ⟨118940583404609985201432293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79293722269739990134288195 118940583404609985201432293)
          ·
            refine ⟨22301359388364372225268555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118940583404609985201432293 22301359388364372225268555)
            ·
              refine ⟨33452039082546558337902833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22301359388364372225268555 33452039082546558337902833)
              ·
                refine ⟨25089029311909918753427125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33452039082546558337902833 25089029311909918753427125)
                ·
                  refine ⟨2352096497991554883133793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25089029311909918753427125 2352096497991554883133793)
                  ·
                    refine ⟨1764072373493666162350345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352096497991554883133793 1764072373493666162350345)
                    ·
                      refine ⟨1323054280120249621762759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764072373493666162350345 1323054280120249621762759)
                      ·
                        rfl

theorem cell23_2576639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_2576639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576639 prefixEnd_2576639 := by exact prefixLift 2576639
  have htrace : WordTrace (prefixWord ++ tailWord_2576639) baseStart_2576639 baseEnd_2576639 := by
    simpa [prefixWord, tailWord_2576639, baseEnd_2576639] using wordTrace_append hprefix tailTrace_2576639
  have hstable : (prefixWord ++ tailWord_2576639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576639).length < 2 ^ (prefixWord ++ tailWord_2576639).sum := by decide
  have hdescent : baseEnd_2576639 < baseStart_2576639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576649 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_2576649 : Nat := 118140960795 + 2576649 * 2 ^ 59
def prefixEnd_2576649 : Nat := 4983230072969 + 3 ^ 40 * 2576649 * 2
def baseEnd_2576649 : Nat := 441019804975598194212571

theorem tailTrace_2576649 : CollatzResearch.WordTrace tailWord_2576649 prefixEnd_2576649 441019804975598194212571 := by
  unfold tailWord_2576649
  simp only [CollatzResearch.WordTrace]
  refine ⟨93978109642248204459613001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62652073094832136306408667 93978109642248204459613001)
  ·
    refine ⟨70483582231686153344709751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93978109642248204459613001 70483582231686153344709751)
    ·
      refine ⟨105725373347529230017064627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70483582231686153344709751 105725373347529230017064627)
      ·
        refine ⟨158588060021293845025596941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105725373347529230017064627 158588060021293845025596941)
        ·
          refine ⟨59470522507985191884598853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158588060021293845025596941 59470522507985191884598853)
          ·
            refine ⟨11150722970247223478362285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59470522507985191884598853 11150722970247223478362285)
            ·
              refine ⟨4181521113842708804385857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11150722970247223478362285 4181521113842708804385857)
              ·
                refine ⟨3136140835382031603289393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181521113842708804385857 3136140835382031603289393)
                ·
                  refine ⟨2352105626536523702467045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136140835382031603289393 2352105626536523702467045)
                  ·
                    refine ⟨441019804975598194212571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352105626536523702467045 441019804975598194212571)
                    ·
                      rfl

theorem cell23_2576649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_2576649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576649 prefixEnd_2576649 := by exact prefixLift 2576649
  have htrace : WordTrace (prefixWord ++ tailWord_2576649) baseStart_2576649 baseEnd_2576649 := by
    simpa [prefixWord, tailWord_2576649, baseEnd_2576649] using wordTrace_append hprefix tailTrace_2576649
  have hstable : (prefixWord ++ tailWord_2576649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576649).length < 2 ^ (prefixWord ++ tailWord_2576649).sum := by decide
  have hdescent : baseEnd_2576649 < baseStart_2576649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576666 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_2576666 : Nat := 118140960795 + 2576666 * 2 ^ 59
def prefixEnd_2576666 : Nat := 4983230072969 + 3 ^ 40 * 2576666 * 2
def baseEnd_2576666 : Nat := 441022714699307005375045

theorem tailTrace_2576666 : CollatzResearch.WordTrace tailWord_2576666 prefixEnd_2576666 441022714699307005375045 := by
  unfold tailWord_2576666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23494682420796654090745463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62652486455457744241987901 23494682420796654090745463)
  ·
    refine ⟨35242023631194981136118195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23494682420796654090745463 35242023631194981136118195)
    ·
      refine ⟨52863035446792471704177293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35242023631194981136118195 52863035446792471704177293)
      ·
        refine ⟨19823638292547176889066485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52863035446792471704177293 19823638292547176889066485)
        ·
          refine ⟨1858466089926297833349983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19823638292547176889066485 1858466089926297833349983)
          ·
            refine ⟨2787699134889446750024975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858466089926297833349983 2787699134889446750024975)
            ·
              refine ⟨4181548702334170125037463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787699134889446750024975 4181548702334170125037463)
              ·
                refine ⟨6272323053501255187556195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181548702334170125037463 6272323053501255187556195)
                ·
                  refine ⟨9408484580251882781334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272323053501255187556195 9408484580251882781334293)
                  ·
                    refine ⟨441022714699307005375045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9408484580251882781334293 441022714699307005375045)
                    ·
                      rfl

theorem cell23_2576666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_2576666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576666 prefixEnd_2576666 := by exact prefixLift 2576666
  have htrace : WordTrace (prefixWord ++ tailWord_2576666) baseStart_2576666 baseEnd_2576666 := by
    simpa [prefixWord, tailWord_2576666, baseEnd_2576666] using wordTrace_append hprefix tailTrace_2576666
  have hstable : (prefixWord ++ tailWord_2576666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576666).length < 2 ^ (prefixWord ++ tailWord_2576666).sum := by decide
  have hdescent : baseEnd_2576666 < baseStart_2576666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576669 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2576669 : Nat := 118140960795 + 2576669 * 2 ^ 59
def prefixEnd_2576669 : Nat := 4983230072969 + 3 ^ 40 * 2576669 * 2
def baseEnd_2576669 : Nat := 1323069684539884504387621

theorem tailTrace_2576669 : CollatzResearch.WordTrace tailWord_2576669 prefixEnd_2576669 1323069684539884504387621 := by
  unfold tailWord_2576669
  simp only [CollatzResearch.WordTrace]
  refine ⟨93978839102175747875341061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62652559401450498583560707 93978839102175747875341061)
  ·
    refine ⟨17621032331657952726626449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93978839102175747875341061 17621032331657952726626449)
    ·
      refine ⟨13215774248743464544969837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17621032331657952726626449 13215774248743464544969837)
      ·
        refine ⟨4955915343278799204363689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13215774248743464544969837 4955915343278799204363689)
        ·
          refine ⟨3716936507459099403272767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955915343278799204363689 3716936507459099403272767)
          ·
            refine ⟨5575404761188649104909151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716936507459099403272767 5575404761188649104909151)
            ·
              refine ⟨8363107141782973657363727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575404761188649104909151 8363107141782973657363727)
              ·
                refine ⟨12544660712674460486045591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363107141782973657363727 12544660712674460486045591)
                ·
                  refine ⟨18816991069011690729068387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12544660712674460486045591 18816991069011690729068387)
                  ·
                    refine ⟨28225486603517536093602581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18816991069011690729068387 28225486603517536093602581)
                    ·
                      refine ⟨1323069684539884504387621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28225486603517536093602581 1323069684539884504387621)
                      ·
                        rfl

theorem cell23_2576669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2576669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576669 prefixEnd_2576669 := by exact prefixLift 2576669
  have htrace : WordTrace (prefixWord ++ tailWord_2576669) baseStart_2576669 baseEnd_2576669 := by
    simpa [prefixWord, tailWord_2576669, baseEnd_2576669] using wordTrace_append hprefix tailTrace_2576669
  have hstable : (prefixWord ++ tailWord_2576669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576669).length < 2 ^ (prefixWord ++ tailWord_2576669).sum := by decide
  have hdescent : baseEnd_2576669 < baseStart_2576669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576676 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2576676 : Nat := 118140960795 + 2576676 * 2 ^ 59
def prefixEnd_2576676 : Nat := 4983230072969 + 3 ^ 40 * 2576676 * 2
def baseEnd_2576676 : Nat := 1323073278904465977000089

theorem tailTrace_2576676 : CollatzResearch.WordTrace tailWord_2576676 prefixEnd_2576676 1323073278904465977000089 := by
  unfold tailWord_2576676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46989547206575194035422941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62652729608766925380563921 46989547206575194035422941)
  ·
    refine ⟨17621080202465697763283603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46989547206575194035422941 17621080202465697763283603)
    ·
      refine ⟨26431620303698546644925405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621080202465697763283603 26431620303698546644925405)
      ·
        refine ⟨9911857613886954991847027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26431620303698546644925405 9911857613886954991847027)
        ·
          refine ⟨14867786420830432487770541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911857613886954991847027 14867786420830432487770541)
          ·
            refine ⟨5575419907811412182913953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14867786420830432487770541 5575419907811412182913953)
            ·
              refine ⟨4181564930858559137185465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575419907811412182913953 4181564930858559137185465)
              ·
                refine ⟨3136173698143919352889099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181564930858559137185465 3136173698143919352889099)
                ·
                  refine ⟨4704260547215879029333649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136173698143919352889099 4704260547215879029333649)
                  ·
                    refine ⟨3528195410411909272000237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704260547215879029333649 3528195410411909272000237)
                    ·
                      refine ⟨1323073278904465977000089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528195410411909272000237 1323073278904465977000089)
                      ·
                        rfl

theorem cell23_2576676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2576676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576676 prefixEnd_2576676 := by exact prefixLift 2576676
  have htrace : WordTrace (prefixWord ++ tailWord_2576676) baseStart_2576676 baseEnd_2576676 := by
    simpa [prefixWord, tailWord_2576676, baseEnd_2576676] using wordTrace_append hprefix tailTrace_2576676
  have hstable : (prefixWord ++ tailWord_2576676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576676).length < 2 ^ (prefixWord ++ tailWord_2576676).sum := by decide
  have hdescent : baseEnd_2576676 < baseStart_2576676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576695 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2576695 : Nat := 118140960795 + 2576695 * 2 ^ 59
def prefixEnd_2576695 : Nat := 4983230072969 + 3 ^ 40 * 2576695 * 2
def baseEnd_2576695 : Nat := 1323083035036901402662501

theorem tailTrace_2576695 : CollatzResearch.WordTrace tailWord_2576695 prefixEnd_2576695 1323083035036901402662501 := by
  unfold tailWord_2576695
  simp only [CollatzResearch.WordTrace]
  refine ⟨93979787400081554315787539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62653191600054369543858359 93979787400081554315787539)
  ·
    refine ⟨140969681100122331473681309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93979787400081554315787539 140969681100122331473681309)
    ·
      refine ⟨52863630412545874302630491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140969681100122331473681309 52863630412545874302630491)
      ·
        refine ⟨79295445618818811453945737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52863630412545874302630491 79295445618818811453945737)
        ·
          refine ⟨59471584214114108590459303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79295445618818811453945737 59471584214114108590459303)
          ·
            refine ⟨89207376321171162885688955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59471584214114108590459303 89207376321171162885688955)
            ·
              refine ⟨133811064481756744328533433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89207376321171162885688955 133811064481756744328533433)
              ·
                refine ⟨100358298361317558246400075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133811064481756744328533433 100358298361317558246400075)
                ·
                  refine ⟨150537447541976337369600113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100358298361317558246400075 150537447541976337369600113)
                  ·
                    refine ⟨112903085656482253027200085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150537447541976337369600113 112903085656482253027200085)
                    ·
                      refine ⟨1323083035036901402662501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112903085656482253027200085 1323083035036901402662501)
                      ·
                        rfl

theorem cell23_2576695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2576695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576695 prefixEnd_2576695 := by exact prefixLift 2576695
  have htrace : WordTrace (prefixWord ++ tailWord_2576695) baseStart_2576695 baseEnd_2576695 := by
    simpa [prefixWord, tailWord_2576695, baseEnd_2576695] using wordTrace_append hprefix tailTrace_2576695
  have hstable : (prefixWord ++ tailWord_2576695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576695).length < 2 ^ (prefixWord ++ tailWord_2576695).sum := by decide
  have hdescent : baseEnd_2576695 < baseStart_2576695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576722 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2576722 : Nat := 118140960795 + 2576722 * 2 ^ 59
def prefixEnd_2576722 : Nat := 4983230072969 + 3 ^ 40 * 2576722 * 2
def baseEnd_2576722 : Nat := 441032299671524265674959

theorem tailTrace_2576722 : CollatzResearch.WordTrace tailWord_2576722 prefixEnd_2576722 441032299671524265674959 := by
  unfold tailWord_2576722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495193042745934481755105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62653848113989158618013613 23495193042745934481755105)
  ·
    refine ⟨17621394782059450861316329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23495193042745934481755105 17621394782059450861316329)
    ·
      refine ⟨13216046086544588145987247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17621394782059450861316329 13216046086544588145987247)
      ·
        refine ⟨19824069129816882218980871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13216046086544588145987247 19824069129816882218980871)
        ·
          refine ⟨29736103694725323328471307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19824069129816882218980871 29736103694725323328471307)
          ·
            refine ⟨44604155542087984992706961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29736103694725323328471307 44604155542087984992706961)
            ·
              refine ⟨33453116656565988744530221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44604155542087984992706961 33453116656565988744530221)
              ·
                refine ⟨12544918746212245779198833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33453116656565988744530221 12544918746212245779198833)
                ·
                  refine ⟨9408689059659184334399125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12544918746212245779198833 9408689059659184334399125)
                  ·
                    refine ⟨441032299671524265674959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9408689059659184334399125 441032299671524265674959)
                    ·
                      rfl

theorem cell23_2576722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2576722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576722 prefixEnd_2576722 := by exact prefixLift 2576722
  have htrace : WordTrace (prefixWord ++ tailWord_2576722) baseStart_2576722 baseEnd_2576722 := by
    simpa [prefixWord, tailWord_2576722, baseEnd_2576722] using wordTrace_append hprefix tailTrace_2576722
  have hstable : (prefixWord ++ tailWord_2576722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576722).length < 2 ^ (prefixWord ++ tailWord_2576722).sum := by decide
  have hdescent : baseEnd_2576722 < baseStart_2576722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576729 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 4, 2]
def baseStart_2576729 : Nat := 118140960795 + 2576729 * 2 ^ 59
def prefixEnd_2576729 : Nat := 4983230072969 + 3 ^ 40 * 2576729 * 2
def baseEnd_2576729 : Nat := 1323100493379154269637345

theorem tailTrace_2576729 : CollatzResearch.WordTrace tailWord_2576729 prefixEnd_2576729 1323100493379154269637345 := by
  unfold tailWord_2576729
  simp only [CollatzResearch.WordTrace]
  refine ⟨93981027481958378122525241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62654018321305585415016827 93981027481958378122525241)
  ·
    refine ⟨70485770611468783591893931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93981027481958378122525241 70485770611468783591893931)
    ·
      refine ⟨105728655917203175387840897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70485770611468783591893931 105728655917203175387840897)
      ·
        refine ⟨79296491937902381540880673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105728655917203175387840897 79296491937902381540880673)
        ·
          refine ⟨59472368953426786155660505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79296491937902381540880673 59472368953426786155660505)
          ·
            refine ⟨44604276715070089616745379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59472368953426786155660505 44604276715070089616745379)
            ·
              refine ⟨66906415072605134425118069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44604276715070089616745379 66906415072605134425118069)
              ·
                refine ⟨6272476413056731352354819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66906415072605134425118069 6272476413056731352354819)
                ·
                  refine ⟨9408714619585097028532229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272476413056731352354819 9408714619585097028532229)
                  ·
                    refine ⟨1764133991172205692849793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9408714619585097028532229 1764133991172205692849793)
                    ·
                      refine ⟨1323100493379154269637345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764133991172205692849793 1323100493379154269637345)
                      ·
                        rfl

theorem cell23_2576729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_2576729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576729 prefixEnd_2576729 := by exact prefixLift 2576729
  have htrace : WordTrace (prefixWord ++ tailWord_2576729) baseStart_2576729 baseEnd_2576729 := by
    simpa [prefixWord, tailWord_2576729, baseEnd_2576729] using wordTrace_append hprefix tailTrace_2576729
  have hstable : (prefixWord ++ tailWord_2576729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576729).length < 2 ^ (prefixWord ++ tailWord_2576729).sum := by decide
  have hdescent : baseEnd_2576729 < baseStart_2576729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576746 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2576746 : Nat := 118140960795 + 2576746 * 2 ^ 59
def prefixEnd_2576746 : Nat := 4983230072969 + 3 ^ 40 * 2576746 * 2
def baseEnd_2576746 : Nat := 1323109222550280703124767

theorem tailTrace_2576746 : CollatzResearch.WordTrace tailWord_2576746 prefixEnd_2576746 1323109222550280703124767 := by
  unfold tailWord_2576746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495411880724197506473523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62654431681931193350596061 23495411880724197506473523)
  ·
    refine ⟨35243117821086296259710285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23495411880724197506473523 35243117821086296259710285)
    ·
      refine ⟨13216169182907361097391357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35243117821086296259710285 13216169182907361097391357)
      ·
        refine ⟨4956063443590260411521759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13216169182907361097391357 4956063443590260411521759)
        ·
          refine ⟨7434095165385390617282639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956063443590260411521759 7434095165385390617282639)
          ·
            refine ⟨11151142748078085925923959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434095165385390617282639 11151142748078085925923959)
            ·
              refine ⟨16726714122117128888885939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151142748078085925923959 16726714122117128888885939)
              ·
                refine ⟨25090071183175693333328909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726714122117128888885939 25090071183175693333328909)
                ·
                  refine ⟨9408776693690884999998341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25090071183175693333328909 9408776693690884999998341)
                  ·
                    refine ⟨1764145630067040937499689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9408776693690884999998341 1764145630067040937499689)
                    ·
                      refine ⟨1323109222550280703124767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764145630067040937499689 1323109222550280703124767)
                      ·
                        rfl

theorem cell23_2576746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2576746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576746 prefixEnd_2576746 := by exact prefixLift 2576746
  have htrace : WordTrace (prefixWord ++ tailWord_2576746) baseStart_2576746 baseEnd_2576746 := by
    simpa [prefixWord, tailWord_2576746, baseEnd_2576746] using wordTrace_append hprefix tailTrace_2576746
  have hstable : (prefixWord ++ tailWord_2576746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576746).length < 2 ^ (prefixWord ++ tailWord_2576746).sum := by decide
  have hdescent : baseEnd_2576746 < baseStart_2576746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576763 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 2, 2, 2]
def baseStart_2576763 : Nat := 118140960795 + 2576763 * 2 ^ 59
def prefixEnd_2576763 : Nat := 4983230072969 + 3 ^ 40 * 2576763 * 2
def baseEnd_2576763 : Nat := 1323117951721407136612189

theorem tailTrace_2576763 : CollatzResearch.WordTrace tailWord_2576763 prefixEnd_2576763 1323117951721407136612189 := by
  unfold tailWord_2576763
  simp only [CollatzResearch.WordTrace]
  refine ⟨93982267563835201929262943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62654845042556801286175295 93982267563835201929262943)
  ·
    refine ⟨140973401345752802893894415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93982267563835201929262943 140973401345752802893894415)
    ·
      refine ⟨211460102018629204340841623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140973401345752802893894415 211460102018629204340841623)
      ·
        refine ⟨317190153027943806511262435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211460102018629204340841623 317190153027943806511262435)
        ·
          refine ⟨475785229541915709766893653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317190153027943806511262435 475785229541915709766893653)
          ·
            refine ⟨5575608158694324723830785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 475785229541915709766893653 5575608158694324723830785)
            ·
              refine ⟨4181706119020743542873089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575608158694324723830785 4181706119020743542873089)
              ·
                refine ⟨3136279589265557657154817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181706119020743542873089 3136279589265557657154817)
                ·
                  refine ⟨2352209691949168242866113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136279589265557657154817 2352209691949168242866113)
                  ·
                    refine ⟨1764157268961876182149585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352209691949168242866113 1764157268961876182149585)
                    ·
                      refine ⟨1323117951721407136612189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764157268961876182149585 1323117951721407136612189)
                      ·
                        rfl

theorem cell23_2576763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2, 2].length) (baseStart_2576763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576763 prefixEnd_2576763 := by exact prefixLift 2576763
  have htrace : WordTrace (prefixWord ++ tailWord_2576763) baseStart_2576763 baseEnd_2576763 := by
    simpa [prefixWord, tailWord_2576763, baseEnd_2576763] using wordTrace_append hprefix tailTrace_2576763
  have hstable : (prefixWord ++ tailWord_2576763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576763).length < 2 ^ (prefixWord ++ tailWord_2576763).sum := by decide
  have hdescent : baseEnd_2576763 < baseStart_2576763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576779 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3]
def baseStart_2576779 : Nat := 118140960795 + 2576779 * 2 ^ 59
def prefixEnd_2576779 : Nat := 4983230072969 + 3 ^ 40 * 2576779 * 2
def baseEnd_2576779 : Nat := 1323126167411879074012115

theorem tailTrace_2576779 : CollatzResearch.WordTrace tailWord_2576779 prefixEnd_2576779 1323126167411879074012115 := by
  unfold tailWord_2576779
  simp only [CollatzResearch.WordTrace]
  refine ⟨93982851131777236661845391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62655234087851491107896927 93982851131777236661845391)
  ·
    refine ⟨140974276697665854992768087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93982851131777236661845391 140974276697665854992768087)
    ·
      refine ⟨211461415046498782489152131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140974276697665854992768087 211461415046498782489152131)
      ·
        refine ⟨317192122569748173733728197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211461415046498782489152131 317192122569748173733728197)
        ·
          refine ⟨59473522981827782575074037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317192122569748173733728197 59473522981827782575074037)
          ·
            refine ⟨5575642779546354616413191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59473522981827782575074037 5575642779546354616413191)
            ·
              refine ⟨8363464169319531924619787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575642779546354616413191 8363464169319531924619787)
              ·
                refine ⟨12545196253979297886929681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363464169319531924619787 12545196253979297886929681)
                ·
                  refine ⟨9408897190484473415197261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12545196253979297886929681 9408897190484473415197261)
                  ·
                    refine ⟨3528336446431677530698973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9408897190484473415197261 3528336446431677530698973)
                    ·
                      refine ⟨1323126167411879074012115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528336446431677530698973 1323126167411879074012115)
                      ·
                        rfl

theorem cell23_2576779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].length) (baseStart_2576779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576779 prefixEnd_2576779 := by exact prefixLift 2576779
  have htrace : WordTrace (prefixWord ++ tailWord_2576779) baseStart_2576779 baseEnd_2576779 := by
    simpa [prefixWord, tailWord_2576779, baseEnd_2576779] using wordTrace_append hprefix tailTrace_2576779
  have hstable : (prefixWord ++ tailWord_2576779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576779).length < 2 ^ (prefixWord ++ tailWord_2576779).sum := by decide
  have hdescent : baseEnd_2576779 < baseStart_2576779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576789 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_2576789 : Nat := 118140960795 + 2576789 * 2 ^ 59
def prefixEnd_2576789 : Nat := 4983230072969 + 3 ^ 40 * 2576789 * 2
def baseEnd_2576789 : Nat := 1323131302218424034887069

theorem tailTrace_2576789 : CollatzResearch.WordTrace tailWord_2576789 prefixEnd_2576789 1323131302218424034887069 := by
  unfold tailWord_2576789
  simp only [CollatzResearch.WordTrace]
  refine ⟨93983215861741008369709421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62655477241160672246472947 93983215861741008369709421)
  ·
    refine ⟨35243705948152878138641033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93983215861741008369709421 35243705948152878138641033)
    ·
      refine ⟨26432779461114658603980775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35243705948152878138641033 26432779461114658603980775)
      ·
        refine ⟨39649169191671987905971163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26432779461114658603980775 39649169191671987905971163)
        ·
          refine ⟨59473753787507981858956745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39649169191671987905971163 59473753787507981858956745)
          ·
            refine ⟨44605315340630986394217559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59473753787507981858956745 44605315340630986394217559)
            ·
              refine ⟨66907973010946479591326339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44605315340630986394217559 66907973010946479591326339)
              ·
                refine ⟨100361959516419719386989509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66907973010946479591326339 100361959516419719386989509)
                ·
                  refine ⟨18817867409328697385060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100361959516419719386989509 18817867409328697385060533)
                  ·
                    refine ⟨1764175069624565379849425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18817867409328697385060533 1764175069624565379849425)
                    ·
                      refine ⟨1323131302218424034887069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764175069624565379849425 1323131302218424034887069)
                      ·
                        rfl

theorem cell23_2576789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_2576789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576789 prefixEnd_2576789 := by exact prefixLift 2576789
  have htrace : WordTrace (prefixWord ++ tailWord_2576789) baseStart_2576789 baseEnd_2576789 := by
    simpa [prefixWord, tailWord_2576789, baseEnd_2576789] using wordTrace_append hprefix tailTrace_2576789
  have hstable : (prefixWord ++ tailWord_2576789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576789).length < 2 ^ (prefixWord ++ tailWord_2576789).sum := by decide
  have hdescent : baseEnd_2576789 < baseStart_2576789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576832 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2576832 : Nat := 118140960795 + 2576832 * 2 ^ 59
def prefixEnd_2576832 : Nat := 4983230072969 + 3 ^ 40 * 2576832 * 2
def baseEnd_2576832 : Nat := 1323153381886567366649371

theorem tailTrace_2576832 : CollatzResearch.WordTrace tailWord_2576832 prefixEnd_2576832 1323153381886567366649371 := by
  unfold tailWord_2576832
  simp only [CollatzResearch.WordTrace]
  refine ⟨46992392100292613356762375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62656522800390151142349833 46992392100292613356762375)
  ·
    refine ⟨70488588150438920035143563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46992392100292613356762375 70488588150438920035143563)
    ·
      refine ⟨105732882225658380052715345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70488588150438920035143563 105732882225658380052715345)
      ·
        refine ⟨79299661669243785039536509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105732882225658380052715345 79299661669243785039536509)
        ·
          refine ⟨29737373125966419389826191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79299661669243785039536509 29737373125966419389826191)
          ·
            refine ⟨44606059688949629084739287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29737373125966419389826191 44606059688949629084739287)
            ·
              refine ⟨66909089533424443627108931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44606059688949629084739287 66909089533424443627108931)
              ·
                refine ⟨100363634300136665440663397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66909089533424443627108931 100363634300136665440663397)
                ·
                  refine ⟨18818181431275624770124387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100363634300136665440663397 18818181431275624770124387)
                  ·
                    refine ⟨28227272146913437155186581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18818181431275624770124387 28227272146913437155186581)
                    ·
                      refine ⟨1323153381886567366649371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28227272146913437155186581 1323153381886567366649371)
                      ·
                        rfl

theorem cell23_2576832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2576832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576832 prefixEnd_2576832 := by exact prefixLift 2576832
  have htrace : WordTrace (prefixWord ++ tailWord_2576832) baseStart_2576832 baseEnd_2576832 := by
    simpa [prefixWord, tailWord_2576832, baseEnd_2576832] using wordTrace_append hprefix tailTrace_2576832
  have hstable : (prefixWord ++ tailWord_2576832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576832).length < 2 ^ (prefixWord ++ tailWord_2576832).sum := by decide
  have hdescent : baseEnd_2576832 < baseStart_2576832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576839 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2576839 : Nat := 118140960795 + 2576839 * 2 ^ 59
def prefixEnd_2576839 : Nat := 4983230072969 + 3 ^ 40 * 2576839 * 2
def baseEnd_2576839 : Nat := 1323156976251148839261839

theorem tailTrace_2576839 : CollatzResearch.WordTrace tailWord_2576839 prefixEnd_2576839 1323156976251148839261839 := by
  unfold tailWord_2576839
  simp only [CollatzResearch.WordTrace]
  refine ⟨93985039511559866909029571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62656693007706577939353047 93985039511559866909029571)
  ·
    refine ⟨140977559267339800363544357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93985039511559866909029571 140977559267339800363544357)
    ·
      refine ⟨26433292362626212568164567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140977559267339800363544357 26433292362626212568164567)
      ·
        refine ⟨39649938543939318852246851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26433292362626212568164567 39649938543939318852246851)
        ·
          refine ⟨59474907815908978278370277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39649938543939318852246851 59474907815908978278370277)
          ·
            refine ⟨11151545215482933427194427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59474907815908978278370277 11151545215482933427194427)
            ·
              refine ⟨16727317823224400140791641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151545215482933427194427 16727317823224400140791641)
              ·
                refine ⟨12545488367418300105593731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16727317823224400140791641 12545488367418300105593731)
                ·
                  refine ⟨18818232551127450158390597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545488367418300105593731 18818232551127450158390597)
                  ·
                    refine ⟨3528418603336396904698237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18818232551127450158390597 3528418603336396904698237)
                    ·
                      refine ⟨1323156976251148839261839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528418603336396904698237 1323156976251148839261839)
                      ·
                        rfl

theorem cell23_2576839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2576839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576839 prefixEnd_2576839 := by exact prefixLift 2576839
  have htrace : WordTrace (prefixWord ++ tailWord_2576839) baseStart_2576839 baseEnd_2576839 := by
    simpa [prefixWord, tailWord_2576839, baseEnd_2576839] using wordTrace_append hprefix tailTrace_2576839
  have hstable : (prefixWord ++ tailWord_2576839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576839).length < 2 ^ (prefixWord ++ tailWord_2576839).sum := by decide
  have hdescent : baseEnd_2576839 < baseStart_2576839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576863 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 1, 4]
def baseStart_2576863 : Nat := 118140960795 + 2576863 * 2 ^ 59
def prefixEnd_2576863 : Nat := 4983230072969 + 3 ^ 40 * 2576863 * 2
def baseEnd_2576863 : Nat := 441056433262285581787243

theorem tailTrace_2576863 : CollatzResearch.WordTrace tailWord_2576863 prefixEnd_2576863 441056433262285581787243 := by
  unfold tailWord_2576863
  simp only [CollatzResearch.WordTrace]
  refine ⟨93985914863472919007903243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62657276575648612671935495 93985914863472919007903243)
  ·
    refine ⟨140978872295209378511854865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93985914863472919007903243 140978872295209378511854865)
    ·
      refine ⟨105734154221407033883891149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140978872295209378511854865 105734154221407033883891149)
      ·
        refine ⟨39650307833027637706459181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105734154221407033883891149 39650307833027637706459181)
        ·
          refine ⟨14868865437385364139922193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39650307833027637706459181 14868865437385364139922193)
          ·
            refine ⟨11151649078039023104941645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14868865437385364139922193 11151649078039023104941645)
            ·
              refine ⟨4181868404264633664353117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11151649078039023104941645 4181868404264633664353117)
              ·
                refine ⟨1568200651599237624132419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181868404264633664353117 1568200651599237624132419)
                ·
                  refine ⟨2352300977398856436198629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568200651599237624132419 2352300977398856436198629)
                  ·
                    refine ⟨441056433262285581787243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352300977398856436198629 441056433262285581787243)
                    ·
                      rfl

theorem cell23_2576863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_2576863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576863 prefixEnd_2576863 := by exact prefixLift 2576863
  have htrace : WordTrace (prefixWord ++ tailWord_2576863) baseStart_2576863 baseEnd_2576863 := by
    simpa [prefixWord, tailWord_2576863, baseEnd_2576863] using wordTrace_append hprefix tailTrace_2576863
  have hstable : (prefixWord ++ tailWord_2576863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576863).length < 2 ^ (prefixWord ++ tailWord_2576863).sum := by decide
  have hdescent : baseEnd_2576863 < baseStart_2576863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576946 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2576946 : Nat := 118140960795 + 2576946 * 2 ^ 59
def prefixEnd_2576946 : Nat := 4983230072969 + 3 ^ 40 * 2576946 * 2
def baseEnd_2576946 : Nat := 1323211918681179920623847

theorem tailTrace_2576946 : CollatzResearch.WordTrace tailWord_2576946 prefixEnd_2576946 1323211918681179920623847 := by
  unfold tailWord_2576946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497235530543056045793673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62659294748114816122116461 23497235530543056045793673)
  ·
    refine ⟨17622926647907292034345255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23497235530543056045793673 17622926647907292034345255)
    ·
      refine ⟨26434389971860938051517883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622926647907292034345255 26434389971860938051517883)
      ·
        refine ⟨39651584957791407077276825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26434389971860938051517883 39651584957791407077276825)
        ·
          refine ⟨29738688718343555307957619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39651584957791407077276825 29738688718343555307957619)
          ·
            refine ⟨44608033077515332961936429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29738688718343555307957619 44608033077515332961936429)
            ·
              refine ⟨16728012404068249860726161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44608033077515332961936429 16728012404068249860726161)
              ·
                refine ⟨12546009303051187395544621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16728012404068249860726161 12546009303051187395544621)
                ·
                  refine ⟨4704753488644195273329233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12546009303051187395544621 4704753488644195273329233)
                  ·
                    refine ⟨3528565116483146454996925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704753488644195273329233 3528565116483146454996925)
                    ·
                      refine ⟨1323211918681179920623847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528565116483146454996925 1323211918681179920623847)
                      ·
                        rfl

theorem cell23_2576946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2576946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576946 prefixEnd_2576946 := by exact prefixLift 2576946
  have htrace : WordTrace (prefixWord ++ tailWord_2576946) baseStart_2576946 baseEnd_2576946 := by
    simpa [prefixWord, tailWord_2576946, baseEnd_2576946] using wordTrace_append hprefix tailTrace_2576946
  have hstable : (prefixWord ++ tailWord_2576946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576946).length < 2 ^ (prefixWord ++ tailWord_2576946).sum := by decide
  have hdescent : baseEnd_2576946 < baseStart_2576946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576956 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2576956 : Nat := 118140960795 + 2576956 * 2 ^ 59
def prefixEnd_2576956 : Nat := 4983230072969 + 3 ^ 40 * 2576956 * 2
def baseEnd_2576956 : Nat := 1323217053487724881498801

theorem tailTrace_2576956 : CollatzResearch.WordTrace tailWord_2576956 prefixEnd_2576956 1323217053487724881498801 := by
  unfold tailWord_2576956
  simp only [CollatzResearch.WordTrace]
  refine ⟨46994653426067997945519361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62659537901423997260692481 46994653426067997945519361)
  ·
    refine ⟨35245990069550998459139521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46994653426067997945519361 35245990069550998459139521)
    ·
      refine ⟨26434492552163248844354641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35245990069550998459139521 26434492552163248844354641)
      ·
        refine ⟨19825869414122436633265981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26434492552163248844354641 19825869414122436633265981)
        ·
          refine ⟨7434701030295913737474743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19825869414122436633265981 7434701030295913737474743)
          ·
            refine ⟨11152051545443870606212115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434701030295913737474743 11152051545443870606212115)
            ·
              refine ⟨16728077318165805909318173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11152051545443870606212115 16728077318165805909318173)
              ·
                refine ⟨6273028994312177215994315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16728077318165805909318173 6273028994312177215994315)
                ·
                  refine ⟨9409543491468265823991473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273028994312177215994315 9409543491468265823991473)
                  ·
                    refine ⟨7057157618601199367993605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9409543491468265823991473 7057157618601199367993605)
                    ·
                      refine ⟨1323217053487724881498801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7057157618601199367993605 1323217053487724881498801)
                      ·
                        rfl

theorem cell23_2576956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2576956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576956 prefixEnd_2576956 := by exact prefixLift 2576956
  have htrace : WordTrace (prefixWord ++ tailWord_2576956) baseStart_2576956 baseEnd_2576956 := by
    simpa [prefixWord, tailWord_2576956, baseEnd_2576956] using wordTrace_append hprefix tailTrace_2576956
  have hstable : (prefixWord ++ tailWord_2576956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576956).length < 2 ^ (prefixWord ++ tailWord_2576956).sum := by decide
  have hdescent : baseEnd_2576956 < baseStart_2576956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576973 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2576973 : Nat := 118140960795 + 2576973 * 2 ^ 59
def prefixEnd_2576973 : Nat := 4983230072969 + 3 ^ 40 * 2576973 * 2
def baseEnd_2576973 : Nat := 1323225782658851314986223

theorem tailTrace_2576973 : CollatzResearch.WordTrace tailWord_2576973 prefixEnd_2576973 1323225782658851314986223 := by
  unfold tailWord_2576973
  simp only [CollatzResearch.WordTrace]
  refine ⟨93989926893074407794407573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62659951262049605196271715 93989926893074407794407573)
  ·
    refine ⟨4405777823112862865362855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93989926893074407794407573 4405777823112862865362855)
    ·
      refine ⟨6608666734669294298044283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405777823112862865362855 6608666734669294298044283)
      ·
        refine ⟨9913000102003941447066425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608666734669294298044283 9913000102003941447066425)
        ·
          refine ⟨7434750076502956085299819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9913000102003941447066425 7434750076502956085299819)
          ·
            refine ⟨11152125114754434127949729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434750076502956085299819 11152125114754434127949729)
            ·
              refine ⟨8364093836065825595962297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11152125114754434127949729 8364093836065825595962297)
              ·
                refine ⟨6273070377049369196971723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8364093836065825595962297 6273070377049369196971723)
                ·
                  refine ⟨9409605565574053795457585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273070377049369196971723 9409605565574053795457585)
                  ·
                    refine ⟨7057204174180540346593189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9409605565574053795457585 7057204174180540346593189)
                    ·
                      refine ⟨1323225782658851314986223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7057204174180540346593189 1323225782658851314986223)
                      ·
                        rfl

theorem cell23_2576973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2576973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576973 prefixEnd_2576973 := by exact prefixLift 2576973
  have htrace : WordTrace (prefixWord ++ tailWord_2576973) baseStart_2576973 baseEnd_2576973 := by
    simpa [prefixWord, tailWord_2576973, baseEnd_2576973] using wordTrace_append hprefix tailTrace_2576973
  have hstable : (prefixWord ++ tailWord_2576973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576973).length < 2 ^ (prefixWord ++ tailWord_2576973).sum := by decide
  have hdescent : baseEnd_2576973 < baseStart_2576973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576977 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_2576977 : Nat := 118140960795 + 2576977 * 2 ^ 59
def prefixEnd_2576977 : Nat := 4983230072969 + 3 ^ 40 * 2576977 * 2
def baseEnd_2576977 : Nat := 1323227836581469299336205

theorem tailTrace_2576977 : CollatzResearch.WordTrace tailWord_2576977 prefixEnd_2576977 1323227836581469299336205 := by
  unfold tailWord_2576977
  simp only [CollatzResearch.WordTrace]
  refine ⟨93990072785059916477553185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62660048523373277651702123 93990072785059916477553185)
  ·
    refine ⟨70492554588794937358164889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93990072785059916477553185 70492554588794937358164889)
    ·
      refine ⟨52869415941596203018623667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70492554588794937358164889 52869415941596203018623667)
      ·
        refine ⟨79304123912394304527935501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52869415941596203018623667 79304123912394304527935501)
        ·
          refine ⟨29739046467147864197975813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79304123912394304527935501 29739046467147864197975813)
          ·
            refine ⟨5576071212590224537120465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29739046467147864197975813 5576071212590224537120465)
            ·
              refine ⟨4182053409442668402840349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576071212590224537120465 4182053409442668402840349)
              ·
                refine ⟨1568270028541000651065131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4182053409442668402840349 1568270028541000651065131)
                ·
                  refine ⟨2352405042811500976597697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568270028541000651065131 2352405042811500976597697)
                  ·
                    refine ⟨1764303782108625732448273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352405042811500976597697 1764303782108625732448273)
                    ·
                      refine ⟨1323227836581469299336205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764303782108625732448273 1323227836581469299336205)
                      ·
                        rfl

theorem cell23_2576977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_2576977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576977 prefixEnd_2576977 := by exact prefixLift 2576977
  have htrace : WordTrace (prefixWord ++ tailWord_2576977) baseStart_2576977 baseEnd_2576977 := by
    simpa [prefixWord, tailWord_2576977, baseEnd_2576977] using wordTrace_append hprefix tailTrace_2576977
  have hstable : (prefixWord ++ tailWord_2576977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576977).length < 2 ^ (prefixWord ++ tailWord_2576977).sum := by decide
  have hdescent : baseEnd_2576977 < baseStart_2576977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576980 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_2576980 : Nat := 118140960795 + 2576980 * 2 ^ 59
def prefixEnd_2576980 : Nat := 4983230072969 + 3 ^ 40 * 2576980 * 2
def baseEnd_2576980 : Nat := 1323229377023432787598691

theorem tailTrace_2576980 : CollatzResearch.WordTrace tailWord_2576980 prefixEnd_2576980 1323229377023432787598691 := by
  unfold tailWord_2576980
  simp only [CollatzResearch.WordTrace]
  refine ⟨46995091102024523994956197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62660121469366031993274929 46995091102024523994956197)
  ·
    refine ⟨8811579581629598249054287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46995091102024523994956197 8811579581629598249054287)
    ·
      refine ⟨13217369372444397373581431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8811579581629598249054287 13217369372444397373581431)
      ·
        refine ⟨19826054058666596060372147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13217369372444397373581431 19826054058666596060372147)
        ·
          refine ⟨29739081087999894090558221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19826054058666596060372147 29739081087999894090558221)
          ·
            refine ⟨11152155407999960283959333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29739081087999894090558221 11152155407999960283959333)
            ·
              refine ⟨2091029138999992553242375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11152155407999960283959333 2091029138999992553242375)
              ·
                refine ⟨3136543708499988829863563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091029138999992553242375 3136543708499988829863563)
                ·
                  refine ⟨4704815562749983244795345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136543708499988829863563 4704815562749983244795345)
                  ·
                    refine ⟨3528611672062487433596509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704815562749983244795345 3528611672062487433596509)
                    ·
                      refine ⟨1323229377023432787598691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528611672062487433596509 1323229377023432787598691)
                      ·
                        rfl

theorem cell23_2576980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_2576980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576980 prefixEnd_2576980 := by exact prefixLift 2576980
  have htrace : WordTrace (prefixWord ++ tailWord_2576980) baseStart_2576980 baseEnd_2576980 := by
    simpa [prefixWord, tailWord_2576980, baseEnd_2576980] using wordTrace_append hprefix tailTrace_2576980
  have hstable : (prefixWord ++ tailWord_2576980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576980).length < 2 ^ (prefixWord ++ tailWord_2576980).sum := by decide
  have hdescent : baseEnd_2576980 < baseStart_2576980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576993 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_2576993 : Nat := 118140960795 + 2576993 * 2 ^ 59
def prefixEnd_2576993 : Nat := 4983230072969 + 3 ^ 40 * 2576993 * 2
def baseEnd_2576993 : Nat := 1323236052271941236736131

theorem tailTrace_2576993 : CollatzResearch.WordTrace tailWord_2576993 prefixEnd_2576993 1323236052271941236736131 := by
  unfold tailWord_2576993
  simp only [CollatzResearch.WordTrace]
  refine ⟨93990656353001951210135633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62660437568667967473423755 93990656353001951210135633)
  ·
    refine ⟨70492992264751463407601725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93990656353001951210135633 70492992264751463407601725)
    ·
      refine ⟨26434872099281798777850647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70492992264751463407601725 26434872099281798777850647)
      ·
        refine ⟨39652308148922698166775971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26434872099281798777850647 39652308148922698166775971)
        ·
          refine ⟨59478462223384047250163957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39652308148922698166775971 59478462223384047250163957)
          ·
            refine ⟨5576105833442254429702871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59478462223384047250163957 5576105833442254429702871)
            ·
              refine ⟨8364158750163381644554307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576105833442254429702871 8364158750163381644554307)
              ·
                refine ⟨12546238125245072466831461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364158750163381644554307 12546238125245072466831461)
                ·
                  refine ⟨2352419648483451087530899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12546238125245072466831461 2352419648483451087530899)
                  ·
                    refine ⟨3528629472725176631296349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352419648483451087530899 3528629472725176631296349)
                    ·
                      refine ⟨1323236052271941236736131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528629472725176631296349 1323236052271941236736131)
                      ·
                        rfl

theorem cell23_2576993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_2576993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576993 prefixEnd_2576993 := by exact prefixLift 2576993
  have htrace : WordTrace (prefixWord ++ tailWord_2576993) baseStart_2576993 baseEnd_2576993 := by
    simpa [prefixWord, tailWord_2576993, baseEnd_2576993] using wordTrace_append hprefix tailTrace_2576993
  have hstable : (prefixWord ++ tailWord_2576993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576993).length < 2 ^ (prefixWord ++ tailWord_2576993).sum := by decide
  have hdescent : baseEnd_2576993 < baseStart_2576993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576994 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2576994 : Nat := 118140960795 + 2576994 * 2 ^ 59
def prefixEnd_2576994 : Nat := 4983230072969 + 3 ^ 40 * 2576994 * 2
def baseEnd_2576994 : Nat := 1323236565752595732823627

theorem tailTrace_2576994 : CollatzResearch.WordTrace tailWord_2576994 prefixEnd_2576994 1323236565752595732823627 := by
  unfold tailWord_2576994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497673206499582095230509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62660461883998885587281357 23497673206499582095230509)
  ·
    refine ⟨8811627452437343285711441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23497673206499582095230509 8811627452437343285711441)
    ·
      refine ⟨6608720589328007464283581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811627452437343285711441 6608720589328007464283581)
      ·
        refine ⟨2478270220998002799106343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6608720589328007464283581 2478270220998002799106343)
        ·
          refine ⟨3717405331497004198659515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478270220998002799106343 3717405331497004198659515)
          ·
            refine ⟨5576107997245506297989273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717405331497004198659515 5576107997245506297989273)
            ·
              refine ⟨4182080997934129723491955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576107997245506297989273 4182080997934129723491955)
              ·
                refine ⟨6273121496901194585237933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182080997934129723491955 6273121496901194585237933)
                ·
                  refine ⟨2352420561337947969464225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6273121496901194585237933 2352420561337947969464225)
                  ·
                    refine ⟨1764315421003460977098169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352420561337947969464225 1764315421003460977098169)
                    ·
                      refine ⟨1323236565752595732823627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764315421003460977098169 1323236565752595732823627)
                      ·
                        rfl

theorem cell23_2576994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2576994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2576994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2576994 prefixEnd_2576994 := by exact prefixLift 2576994
  have htrace : WordTrace (prefixWord ++ tailWord_2576994) baseStart_2576994 baseEnd_2576994 := by
    simpa [prefixWord, tailWord_2576994, baseEnd_2576994] using wordTrace_append hprefix tailTrace_2576994
  have hstable : (prefixWord ++ tailWord_2576994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576994).length < 2 ^ (prefixWord ++ tailWord_2576994).sum := by decide
  have hdescent : baseEnd_2576994 < baseStart_2576994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577010 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2577010 : Nat := 118140960795 + 2577010 * 2 ^ 59
def prefixEnd_2577010 : Nat := 4983230072969 + 3 ^ 40 * 2577010 * 2
def baseEnd_2577010 : Nat := 1323244781443067670223553

theorem tailTrace_2577010 : CollatzResearch.WordTrace tailWord_2577010 prefixEnd_2577010 1323244781443067670223553 := by
  unfold tailWord_2577010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497819098485090778376121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62660850929293575409002989 23497819098485090778376121)
  ·
    refine ⟨17623364323863818083782091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23497819098485090778376121 17623364323863818083782091)
    ·
      refine ⟨26435046485795727125673137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17623364323863818083782091 26435046485795727125673137)
      ·
        refine ⟨19826284864346795344254853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26435046485795727125673137 19826284864346795344254853)
        ·
          refine ⟨3717428412065024127047785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19826284864346795344254853 3717428412065024127047785)
          ·
            refine ⟨2788071309048768095285839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3717428412065024127047785 2788071309048768095285839)
            ·
              refine ⟨4182106963573152142928759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788071309048768095285839 4182106963573152142928759)
              ·
                refine ⟨6273160445359728214393139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182106963573152142928759 6273160445359728214393139)
                ·
                  refine ⟨9409740668039592321589709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273160445359728214393139 9409740668039592321589709)
                  ·
                    refine ⟨3528652750514847120596141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9409740668039592321589709 3528652750514847120596141)
                    ·
                      refine ⟨1323244781443067670223553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528652750514847120596141 1323244781443067670223553)
                      ·
                        rfl

theorem cell23_2577010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2577010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577010 prefixEnd_2577010 := by exact prefixLift 2577010
  have htrace : WordTrace (prefixWord ++ tailWord_2577010) baseStart_2577010 baseEnd_2577010 := by
    simpa [prefixWord, tailWord_2577010, baseEnd_2577010] using wordTrace_append hprefix tailTrace_2577010
  have hstable : (prefixWord ++ tailWord_2577010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577010).length < 2 ^ (prefixWord ++ tailWord_2577010).sum := by decide
  have hdescent : baseEnd_2577010 < baseStart_2577010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577049 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2577049 : Nat := 118140960795 + 2577049 * 2 ^ 59
def prefixEnd_2577049 : Nat := 4983230072969 + 3 ^ 40 * 2577049 * 2
def baseEnd_2577049 : Nat := 1323264807188593017635873

theorem tailTrace_2577049 : CollatzResearch.WordTrace tailWord_2577049 prefixEnd_2577049 1323264807188593017635873 := by
  unfold tailWord_2577049
  simp only [CollatzResearch.WordTrace]
  refine ⟨93992698840799072774174201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62661799227199381849449467 93992698840799072774174201)
  ·
    refine ⟨70494524130599304580630651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93992698840799072774174201 70494524130599304580630651)
    ·
      refine ⟨105741786195898956870945977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70494524130599304580630651 105741786195898956870945977)
      ·
        refine ⟨79306339646924217653209483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105741786195898956870945977 79306339646924217653209483)
        ·
          refine ⟨118959509470386326479814225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79306339646924217653209483 118959509470386326479814225)
          ·
            refine ⟨89219632102789744859860669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118959509470386326479814225 89219632102789744859860669)
            ·
              refine ⟨33457362038546154322447751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89219632102789744859860669 33457362038546154322447751)
              ·
                refine ⟨50186043057819231483671627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33457362038546154322447751 50186043057819231483671627)
                ·
                  refine ⟨75279064586728847225507441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50186043057819231483671627 75279064586728847225507441)
                  ·
                    refine ⟨56459298440046635419130581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75279064586728847225507441 56459298440046635419130581)
                    ·
                      refine ⟨1323264807188593017635873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56459298440046635419130581 1323264807188593017635873)
                      ·
                        rfl

theorem cell23_2577049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2577049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577049 prefixEnd_2577049 := by exact prefixLift 2577049
  have htrace : WordTrace (prefixWord ++ tailWord_2577049) baseStart_2577049 baseEnd_2577049 := by
    simpa [prefixWord, tailWord_2577049, baseEnd_2577049] using wordTrace_append hprefix tailTrace_2577049
  have hstable : (prefixWord ++ tailWord_2577049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577049).length < 2 ^ (prefixWord ++ tailWord_2577049).sum := by decide
  have hdescent : baseEnd_2577049 < baseStart_2577049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577059 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2577059 : Nat := 118140960795 + 2577059 * 2 ^ 59
def prefixEnd_2577059 : Nat := 4983230072969 + 3 ^ 40 * 2577059 * 2
def baseEnd_2577059 : Nat := 1323269941995137978510827

theorem tailTrace_2577059 : CollatzResearch.WordTrace tailWord_2577059 prefixEnd_2577059 1323269941995137978510827 := by
  unfold tailWord_2577059
  simp only [CollatzResearch.WordTrace]
  refine ⟨93993063570762844482038231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62662042380508562988025487 93993063570762844482038231)
  ·
    refine ⟨140989595356144266723057347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93993063570762844482038231 140989595356144266723057347)
    ·
      refine ⟨211484393034216400084586021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140989595356144266723057347 211484393034216400084586021)
      ·
        refine ⟨39653323693915575015859879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211484393034216400084586021 39653323693915575015859879)
        ·
          refine ⟨59479985540873362523789819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39653323693915575015859879 59479985540873362523789819)
          ·
            refine ⟨89219978311310043785684729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59479985540873362523789819 89219978311310043785684729)
            ·
              refine ⟨66914983733482532839263547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89219978311310043785684729 66914983733482532839263547)
              ·
                refine ⟨100372475600223799258895321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66914983733482532839263547 100372475600223799258895321)
                ·
                  refine ⟨75279356700167849444171491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100372475600223799258895321 75279356700167849444171491)
                  ·
                    refine ⟨112919035050251774166257237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75279356700167849444171491 112919035050251774166257237)
                    ·
                      refine ⟨1323269941995137978510827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112919035050251774166257237 1323269941995137978510827)
                      ·
                        rfl

theorem cell23_2577059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2577059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577059 prefixEnd_2577059 := by exact prefixLift 2577059
  have htrace : WordTrace (prefixWord ++ tailWord_2577059) baseStart_2577059 baseEnd_2577059 := by
    simpa [prefixWord, tailWord_2577059, baseEnd_2577059] using wordTrace_append hprefix tailTrace_2577059
  have hstable : (prefixWord ++ tailWord_2577059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577059).length < 2 ^ (prefixWord ++ tailWord_2577059).sum := by decide
  have hdescent : baseEnd_2577059 < baseStart_2577059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577096 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2577096 : Nat := 118140960795 + 2577096 * 2 ^ 59
def prefixEnd_2577096 : Nat := 4983230072969 + 3 ^ 40 * 2577096 * 2
def baseEnd_2577096 : Nat := 1323288940779354333748157

theorem tailTrace_2577096 : CollatzResearch.WordTrace tailWord_2577096 prefixEnd_2577096 1323288940779354333748157 := by
  unfold tailWord_2577096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46997206535814399900567571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62662942047752533200756761 46997206535814399900567571)
  ·
    refine ⟨70495809803721599850851357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46997206535814399900567571 70495809803721599850851357)
    ·
      refine ⟨26435928676395599944069259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70495809803721599850851357 26435928676395599944069259)
      ·
        refine ⟨39653893014593399916103889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26435928676395599944069259 39653893014593399916103889)
        ·
          refine ⟨29740419760945049937077917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39653893014593399916103889 29740419760945049937077917)
          ·
            refine ⟨11152657410354393726404219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29740419760945049937077917 11152657410354393726404219)
            ·
              refine ⟨16728986115531590589606329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11152657410354393726404219 16728986115531590589606329)
              ·
                refine ⟨12546739586648692942204747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16728986115531590589606329 12546739586648692942204747)
                ·
                  refine ⟨18820109379973039413307121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12546739586648692942204747 18820109379973039413307121)
                  ·
                    refine ⟨14115082034979779559980341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18820109379973039413307121 14115082034979779559980341)
                    ·
                      refine ⟨1323288940779354333748157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14115082034979779559980341 1323288940779354333748157)
                      ·
                        rfl

theorem cell23_2577096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2577096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577096 prefixEnd_2577096 := by exact prefixLift 2577096
  have htrace : WordTrace (prefixWord ++ tailWord_2577096) baseStart_2577096 baseEnd_2577096 := by
    simpa [prefixWord, tailWord_2577096, baseEnd_2577096] using wordTrace_append hprefix tailTrace_2577096
  have hstable : (prefixWord ++ tailWord_2577096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577096).length < 2 ^ (prefixWord ++ tailWord_2577096).sum := by decide
  have hdescent : baseEnd_2577096 < baseStart_2577096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577101 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2577101 : Nat := 118140960795 + 2577101 * 2 ^ 59
def prefixEnd_2577101 : Nat := 4983230072969 + 3 ^ 40 * 2577101 * 2
def baseEnd_2577101 : Nat := 1323291508182626814185635

theorem tailTrace_2577101 : CollatzResearch.WordTrace tailWord_2577101 prefixEnd_2577101 1323291508182626814185635 := by
  unfold tailWord_2577101
  simp only [CollatzResearch.WordTrace]
  refine ⟨93994595436610685655067157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62663063624407123770044771 93994595436610685655067157)
  ·
    refine ⟨4405996661091125890081273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93994595436610685655067157 4405996661091125890081273)
    ·
      refine ⟨3304497495818344417560955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405996661091125890081273 3304497495818344417560955)
      ·
        refine ⟨4956746243727516626341433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304497495818344417560955 4956746243727516626341433)
        ·
          refine ⟨3717559682795637469756075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4956746243727516626341433 3717559682795637469756075)
          ·
            refine ⟨5576339524193456204634113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717559682795637469756075 5576339524193456204634113)
            ·
              refine ⟨4182254643145092153475585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576339524193456204634113 4182254643145092153475585)
              ·
                refine ⟨3136690982358819115106689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182254643145092153475585 3136690982358819115106689)
                ·
                  refine ⟨2352518236769114336330017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136690982358819115106689 2352518236769114336330017)
                  ·
                    refine ⟨1764388677576835752247513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352518236769114336330017 1764388677576835752247513)
                    ·
                      refine ⟨1323291508182626814185635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764388677576835752247513 1323291508182626814185635)
                      ·
                        rfl

theorem cell23_2577101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2577101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577101 prefixEnd_2577101 := by exact prefixLift 2577101
  have htrace : WordTrace (prefixWord ++ tailWord_2577101) baseStart_2577101 baseEnd_2577101 := by
    simpa [prefixWord, tailWord_2577101, baseEnd_2577101] using wordTrace_append hprefix tailTrace_2577101
  have hstable : (prefixWord ++ tailWord_2577101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577101).length < 2 ^ (prefixWord ++ tailWord_2577101).sum := by decide
  have hdescent : baseEnd_2577101 < baseStart_2577101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577180 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 6]
def baseStart_2577180 : Nat := 118140960795 + 2577180 * 2 ^ 59
def prefixEnd_2577180 : Nat := 4983230072969 + 3 ^ 40 * 2577180 * 2
def baseEnd_2577180 : Nat := 147036897017148000566419

theorem tailTrace_2577180 : CollatzResearch.WordTrace tailWord_2577180 prefixEnd_2577180 147036897017148000566419 := by
  unfold tailWord_2577180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46998738401662241073596497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62664984535549654764795329 46998738401662241073596497)
  ·
    refine ⟨35249053801246680805197373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46998738401662241073596497 35249053801246680805197373)
    ·
      refine ⟨13218395175467505301949015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35249053801246680805197373 13218395175467505301949015)
      ·
        refine ⟨19827592763201257952923523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13218395175467505301949015 19827592763201257952923523)
        ·
          refine ⟨29741389144801886929385285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827592763201257952923523 29741389144801886929385285)
          ·
            refine ⟨5576510464650353799259741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29741389144801886929385285 5576510464650353799259741)
            ·
              refine ⟨2091191424243882674722403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5576510464650353799259741 2091191424243882674722403)
              ·
                refine ⟨3136787136365824012083605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091191424243882674722403 3136787136365824012083605)
                ·
                  refine ⟨147036897017148000566419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3136787136365824012083605 147036897017148000566419)
                  ·
                    rfl

theorem cell23_2577180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_2577180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577180 prefixEnd_2577180 := by exact prefixLift 2577180
  have htrace : WordTrace (prefixWord ++ tailWord_2577180) baseStart_2577180 baseEnd_2577180 := by
    simpa [prefixWord, tailWord_2577180, baseEnd_2577180] using wordTrace_append hprefix tailTrace_2577180
  have hstable : (prefixWord ++ tailWord_2577180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577180).length < 2 ^ (prefixWord ++ tailWord_2577180).sum := by decide
  have hdescent : baseEnd_2577180 < baseStart_2577180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577224 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_2577224 : Nat := 118140960795 + 2577224 * 2 ^ 59
def prefixEnd_2577224 : Nat := 4983230072969 + 3 ^ 40 * 2577224 * 2
def baseEnd_2577224 : Nat := 1323354666303129832947569

theorem tailTrace_2577224 : CollatzResearch.WordTrace tailWord_2577224 prefixEnd_2577224 1323354666303129832947569 := by
  unfold tailWord_2577224
  simp only [CollatzResearch.WordTrace]
  refine ⟨46999540807582538830897363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62666054410110051774529817 46999540807582538830897363)
  ·
    refine ⟨70499311211373808246346045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46999540807582538830897363 70499311211373808246346045)
    ·
      refine ⟨26437241704265178092379767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70499311211373808246346045 26437241704265178092379767)
      ·
        refine ⟨39655862556397767138569651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26437241704265178092379767 39655862556397767138569651)
        ·
          refine ⟨59483793834596650707854477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39655862556397767138569651 59483793834596650707854477)
          ·
            refine ⟨22306422687973744015445429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59483793834596650707854477 22306422687973744015445429)
            ·
              refine ⟨2091227126997538501448009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22306422687973744015445429 2091227126997538501448009)
              ·
                refine ⟨1568420345248153876086007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091227126997538501448009 1568420345248153876086007)
                ·
                  refine ⟨2352630517872230814129011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568420345248153876086007 2352630517872230814129011)
                  ·
                    refine ⟨3528945776808346221193517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352630517872230814129011 3528945776808346221193517)
                    ·
                      refine ⟨1323354666303129832947569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3528945776808346221193517 1323354666303129832947569)
                      ·
                        rfl

theorem cell23_2577224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_2577224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577224 prefixEnd_2577224 := by exact prefixLift 2577224
  have htrace : WordTrace (prefixWord ++ tailWord_2577224) baseStart_2577224 baseEnd_2577224 := by
    simpa [prefixWord, tailWord_2577224, baseEnd_2577224] using wordTrace_append hprefix tailTrace_2577224
  have hstable : (prefixWord ++ tailWord_2577224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577224).length < 2 ^ (prefixWord ++ tailWord_2577224).sum := by decide
  have hdescent : baseEnd_2577224 < baseStart_2577224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577303 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2577303 : Nat := 118140960795 + 2577303 * 2 ^ 59
def prefixEnd_2577303 : Nat := 4983230072969 + 3 ^ 40 * 2577303 * 2
def baseEnd_2577303 : Nat := 1323395231274835023859705

theorem tailTrace_2577303 : CollatzResearch.WordTrace tailWord_2577303 prefixEnd_2577303 1323395231274835023859705 := by
  unfold tailWord_2577303
  simp only [CollatzResearch.WordTrace]
  refine ⟨94001962981878874153920563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62667975321252582769280375 94001962981878874153920563)
  ·
    refine ⟨141002944472818311230880845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94001962981878874153920563 141002944472818311230880845)
    ·
      refine ⟨52876104177306866711580317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141002944472818311230880845 52876104177306866711580317)
      ·
        refine ⟨19828539066490075016842619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52876104177306866711580317 19828539066490075016842619)
        ·
          refine ⟨29742808599735112525263929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19828539066490075016842619 29742808599735112525263929)
          ·
            refine ⟨22307106449801334393947947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29742808599735112525263929 22307106449801334393947947)
            ·
              refine ⟨33460659674702001590921921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22307106449801334393947947 33460659674702001590921921)
              ·
                refine ⟨25095494756026501193191441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33460659674702001590921921 25095494756026501193191441)
                ·
                  refine ⟨18821621067019875894893581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25095494756026501193191441 18821621067019875894893581)
                  ·
                    refine ⟨7058107900132453460585093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18821621067019875894893581 7058107900132453460585093)
                    ·
                      refine ⟨1323395231274835023859705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7058107900132453460585093 1323395231274835023859705)
                      ·
                        rfl

theorem cell23_2577303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2577303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577303 prefixEnd_2577303 := by exact prefixLift 2577303
  have htrace : WordTrace (prefixWord ++ tailWord_2577303) baseStart_2577303 baseEnd_2577303 := by
    simpa [prefixWord, tailWord_2577303, baseEnd_2577303] using wordTrace_append hprefix tailTrace_2577303
  have hstable : (prefixWord ++ tailWord_2577303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577303).length < 2 ^ (prefixWord ++ tailWord_2577303).sum := by decide
  have hdescent : baseEnd_2577303 < baseStart_2577303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3]
def baseStart_2577323 : Nat := 118140960795 + 2577323 * 2 ^ 59
def prefixEnd_2577323 : Nat := 4983230072969 + 3 ^ 40 * 2577323 * 2
def baseEnd_2577323 : Nat := 1323405500887924945609613

theorem tailTrace_2577323 : CollatzResearch.WordTrace tailWord_2577323 prefixEnd_2577323 1323405500887924945609613 := by
  unfold tailWord_2577323
  simp only [CollatzResearch.WordTrace]
  refine ⟨94002692441806417569648623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62668461627870945046432415 94002692441806417569648623)
  ·
    refine ⟨141004038662709626354472935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94002692441806417569648623 141004038662709626354472935)
    ·
      refine ⟨211506057994064439531709403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141004038662709626354472935 211506057994064439531709403)
      ·
        refine ⟨317259086991096659297564105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211506057994064439531709403 317259086991096659297564105)
        ·
          refine ⟨237944315243322494473173079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317259086991096659297564105 237944315243322494473173079)
          ·
            refine ⟨356916472864983741709759619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237944315243322494473173079 356916472864983741709759619)
            ·
              refine ⟨535374709297475612564639429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356916472864983741709759619 535374709297475612564639429)
              ·
                refine ⟨100382757993276677355869893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535374709297475612564639429 100382757993276677355869893)
                ·
                  refine ⟨18821767123739377004225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100382757993276677355869893 18821767123739377004225605)
                  ·
                    refine ⟨3529081335701133188292301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18821767123739377004225605 3529081335701133188292301)
                    ·
                      refine ⟨1323405500887924945609613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529081335701133188292301 1323405500887924945609613)
                      ·
                        rfl

theorem cell23_2577323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].length) (baseStart_2577323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577323 prefixEnd_2577323 := by exact prefixLift 2577323
  have htrace : WordTrace (prefixWord ++ tailWord_2577323) baseStart_2577323 baseEnd_2577323 := by
    simpa [prefixWord, tailWord_2577323, baseEnd_2577323] using wordTrace_append hprefix tailTrace_2577323
  have hstable : (prefixWord ++ tailWord_2577323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577323).length < 2 ^ (prefixWord ++ tailWord_2577323).sum := by decide
  have hdescent : baseEnd_2577323 < baseStart_2577323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577348 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2577348 : Nat := 118140960795 + 2577348 * 2 ^ 59
def prefixEnd_2577348 : Nat := 4983230072969 + 3 ^ 40 * 2577348 * 2
def baseEnd_2577348 : Nat := 1323418337904287347796999

theorem tailTrace_2577348 : CollatzResearch.WordTrace tailWord_2577348 prefixEnd_2577348 1323418337904287347796999 := by
  unfold tailWord_2577348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47001802133357923419654349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62669069511143897892872465 47001802133357923419654349)
  ·
    refine ⟨17625675800009221282370381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47001802133357923419654349 17625675800009221282370381)
    ·
      refine ⟨6609628425003457980888893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17625675800009221282370381 6609628425003457980888893)
      ·
        refine ⟨2478610659376296742833335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6609628425003457980888893 2478610659376296742833335)
        ·
          refine ⟨3717915989064445114250003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478610659376296742833335 3717915989064445114250003)
          ·
            refine ⟨5576873983596667671375005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717915989064445114250003 5576873983596667671375005)
            ·
              refine ⟨2091327743848750376765627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5576873983596667671375005 2091327743848750376765627)
              ·
                refine ⟨3136991615773125565148441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091327743848750376765627 3136991615773125565148441)
                ·
                  refine ⟨2352743711829844173861331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136991615773125565148441 2352743711829844173861331)
                  ·
                    refine ⟨3529115567744766260791997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352743711829844173861331 3529115567744766260791997)
                    ·
                      refine ⟨1323418337904287347796999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529115567744766260791997 1323418337904287347796999)
                      ·
                        rfl

theorem cell23_2577348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2577348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577348 prefixEnd_2577348 := by exact prefixLift 2577348
  have htrace : WordTrace (prefixWord ++ tailWord_2577348) baseStart_2577348 baseEnd_2577348 := by
    simpa [prefixWord, tailWord_2577348, baseEnd_2577348] using wordTrace_append hprefix tailTrace_2577348
  have hstable : (prefixWord ++ tailWord_2577348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577348).length < 2 ^ (prefixWord ++ tailWord_2577348).sum := by decide
  have hdescent : baseEnd_2577348 < baseStart_2577348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577394 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_2577394 : Nat := 118140960795 + 2577394 * 2 ^ 59
def prefixEnd_2577394 : Nat := 4983230072969 + 3 ^ 40 * 2577394 * 2
def baseEnd_2577394 : Nat := 147049106446043796424643

theorem tailTrace_2577394 : CollatzResearch.WordTrace tailWord_2577394 prefixEnd_2577394 147049106446043796424643 := by
  unfold tailWord_2577394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23501320506137299173870809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62670188016366131130322157 23501320506137299173870809)
  ·
    refine ⟨17625990379602974380403107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23501320506137299173870809 17625990379602974380403107)
    ·
      refine ⟨26438985569404461570604661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17625990379602974380403107 26438985569404461570604661)
      ·
        refine ⟨2478654897131668272244187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26438985569404461570604661 2478654897131668272244187)
        ·
          refine ⟨3717982345697502408366281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478654897131668272244187 3717982345697502408366281)
          ·
            refine ⟨2788486759273126806274711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3717982345697502408366281 2788486759273126806274711)
            ·
              refine ⟨4182730138909690209412067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788486759273126806274711 4182730138909690209412067)
              ·
                refine ⟨6274095208364535314118101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182730138909690209412067 6274095208364535314118101)
                ·
                  refine ⟨147049106446043796424643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6274095208364535314118101 147049106446043796424643)
                  ·
                    rfl

theorem cell23_2577394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_2577394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577394 prefixEnd_2577394 := by exact prefixLift 2577394
  have htrace : WordTrace (prefixWord ++ tailWord_2577394) baseStart_2577394 baseEnd_2577394 := by
    simpa [prefixWord, tailWord_2577394, baseEnd_2577394] using wordTrace_append hprefix tailTrace_2577394
  have hstable : (prefixWord ++ tailWord_2577394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577394).length < 2 ^ (prefixWord ++ tailWord_2577394).sum := by decide
  have hdescent : baseEnd_2577394 < baseStart_2577394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577423 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_2577423 : Nat := 118140960795 + 2577423 * 2 ^ 59
def prefixEnd_2577423 : Nat := 4983230072969 + 3 ^ 40 * 2577423 * 2
def baseEnd_2577423 : Nat := 1323456848953374554359153

theorem tailTrace_2577423 : CollatzResearch.WordTrace tailWord_2577423 prefixEnd_2577423 1323456848953374554359153 := by
  unfold tailWord_2577423
  simp only [CollatzResearch.WordTrace]
  refine ⟨94006339741444134648288923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62670893160962756432192615 94006339741444134648288923)
  ·
    refine ⟨141009509612166201972433385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94006339741444134648288923 141009509612166201972433385)
    ·
      refine ⟨105757132209124651479325039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141009509612166201972433385 105757132209124651479325039)
      ·
        refine ⟨158635698313686977218987559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105757132209124651479325039 158635698313686977218987559)
        ·
          refine ⟨237953547470530465828481339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158635698313686977218987559 237953547470530465828481339)
          ·
            refine ⟨356930321205795698742722009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237953547470530465828481339 356930321205795698742722009)
            ·
              refine ⟨267697740904346774057041507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356930321205795698742722009 267697740904346774057041507)
              ·
                refine ⟨401546611356520161085562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267697740904346774057041507 401546611356520161085562261)
                ·
                  refine ⟨18822497407336882550885731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401546611356520161085562261 18822497407336882550885731)
                  ·
                    refine ⟨28233746111005323826328597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18822497407336882550885731 28233746111005323826328597)
                    ·
                      refine ⟨1323456848953374554359153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28233746111005323826328597 1323456848953374554359153)
                      ·
                        rfl

theorem cell23_2577423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_2577423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577423 prefixEnd_2577423 := by exact prefixLift 2577423
  have htrace : WordTrace (prefixWord ++ tailWord_2577423) baseStart_2577423 baseEnd_2577423 := by
    simpa [prefixWord, tailWord_2577423, baseEnd_2577423] using wordTrace_append hprefix tailTrace_2577423
  have hstable : (prefixWord ++ tailWord_2577423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577423).length < 2 ^ (prefixWord ++ tailWord_2577423).sum := by decide
  have hdescent : baseEnd_2577423 < baseStart_2577423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577433 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 10]
def baseStart_2577433 : Nat := 118140960795 + 2577433 * 2 ^ 59
def prefixEnd_2577433 : Nat := 4983230072969 + 3 ^ 40 * 2577433 * 2
def baseEnd_2577433 : Nat := 147051331528879946137123

theorem tailTrace_2577433 : CollatzResearch.WordTrace tailWord_2577433 prefixEnd_2577433 147051331528879946137123 := by
  unfold tailWord_2577433
  simp only [CollatzResearch.WordTrace]
  refine ⟨94006704471407906356152953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62671136314271937570768635 94006704471407906356152953)
  ·
    refine ⟨70505028353555929767114715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94006704471407906356152953 70505028353555929767114715)
    ·
      refine ⟨105757542530333894650672073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70505028353555929767114715 105757542530333894650672073)
      ·
        refine ⟨79318156897750420988004055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105757542530333894650672073 79318156897750420988004055)
        ·
          refine ⟨118977235346625631482006083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79318156897750420988004055 118977235346625631482006083)
          ·
            refine ⟨178465853019938447223009125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118977235346625631482006083 178465853019938447223009125)
            ·
              refine ⟨33462347441238458854314211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178465853019938447223009125 33462347441238458854314211)
              ·
                refine ⟨50193521161857688281471317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33462347441238458854314211 50193521161857688281471317)
                ·
                  refine ⟨147051331528879946137123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50193521161857688281471317 147051331528879946137123)
                  ·
                    rfl

theorem cell23_2577433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_2577433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577433 prefixEnd_2577433 := by exact prefixLift 2577433
  have htrace : WordTrace (prefixWord ++ tailWord_2577433) baseStart_2577433 baseEnd_2577433 := by
    simpa [prefixWord, tailWord_2577433, baseEnd_2577433] using wordTrace_append hprefix tailTrace_2577433
  have hstable : (prefixWord ++ tailWord_2577433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577433).length < 2 ^ (prefixWord ++ tailWord_2577433).sum := by decide
  have hdescent : baseEnd_2577433 < baseStart_2577433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577477 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_2577477 : Nat := 118140960795 + 2577477 * 2 ^ 59
def prefixEnd_2577477 : Nat := 4983230072969 + 3 ^ 40 * 2577477 * 2
def baseEnd_2577477 : Nat := 1323484576908717343083905

theorem tailTrace_2577477 : CollatzResearch.WordTrace tailWord_2577477 prefixEnd_2577477 1323484576908717343083905 := by
  unfold tailWord_2577477
  simp only [CollatzResearch.WordTrace]
  refine ⟨94008309283248501870754685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62672206188832334580503123 94008309283248501870754685)
  ·
    refine ⟨35253115981218188201533007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94008309283248501870754685 35253115981218188201533007)
    ·
      refine ⟨52879673971827282302299511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35253115981218188201533007 52879673971827282302299511)
      ·
        refine ⟨79319510957740923453449267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52879673971827282302299511 79319510957740923453449267)
        ·
          refine ⟨118979266436611385180173901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79319510957740923453449267 118979266436611385180173901)
          ·
            refine ⟨44617224913729269442565213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118979266436611385180173901 44617224913729269442565213)
            ·
              refine ⟨16731459342648476040961955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44617224913729269442565213 16731459342648476040961955)
              ·
                refine ⟨25097189013972714061442933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16731459342648476040961955 25097189013972714061442933)
                ·
                  refine ⟨2352861470059941943260275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25097189013972714061442933 2352861470059941943260275)
                  ·
                    refine ⟨3529292205089912914890413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352861470059941943260275 3529292205089912914890413)
                    ·
                      refine ⟨1323484576908717343083905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529292205089912914890413 1323484576908717343083905)
                      ·
                        rfl

theorem cell23_2577477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_2577477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577477 prefixEnd_2577477 := by exact prefixLift 2577477
  have htrace : WordTrace (prefixWord ++ tailWord_2577477) baseStart_2577477 baseEnd_2577477 := by
    simpa [prefixWord, tailWord_2577477, baseEnd_2577477] using wordTrace_append hprefix tailTrace_2577477
  have hstable : (prefixWord ++ tailWord_2577477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577477).length < 2 ^ (prefixWord ++ tailWord_2577477).sum := by decide
  have hdescent : baseEnd_2577477 < baseStart_2577477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577480 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_2577480 : Nat := 118140960795 + 2577480 * 2 ^ 59
def prefixEnd_2577480 : Nat := 4983230072969 + 3 ^ 40 * 2577480 * 2
def baseEnd_2577480 : Nat := 441162039116893610448797

theorem tailTrace_2577480 : CollatzResearch.WordTrace tailWord_2577480 prefixEnd_2577480 441162039116893610448797 := by
  unfold tailWord_2577480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47004209351118816691556947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62672279134825088922075929 47004209351118816691556947)
  ·
    refine ⟨70506314026678225037335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47004209351118816691556947 70506314026678225037335421)
    ·
      refine ⟨26439867760004334389000783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70506314026678225037335421 26439867760004334389000783)
      ·
        refine ⟨39659801640006501583501175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26439867760004334389000783 39659801640006501583501175)
        ·
          refine ⟨59489702460009752375251763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39659801640006501583501175 59489702460009752375251763)
          ·
            refine ⟨89234553690014628562877645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59489702460009752375251763 89234553690014628562877645)
            ·
              refine ⟨33462957633755485711079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89234553690014628562877645 33462957633755485711079117)
              ·
                refine ⟨12548609112658307141654669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33462957633755485711079117 12548609112658307141654669)
                ·
                  refine ⟨4705728417246865178120501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12548609112658307141654669 4705728417246865178120501)
                  ·
                    refine ⟨441162039116893610448797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4705728417246865178120501 441162039116893610448797)
                    ·
                      rfl

theorem cell23_2577480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_2577480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577480 prefixEnd_2577480 := by exact prefixLift 2577480
  have htrace : WordTrace (prefixWord ++ tailWord_2577480) baseStart_2577480 baseEnd_2577480 := by
    simpa [prefixWord, tailWord_2577480, baseEnd_2577480] using wordTrace_append hprefix tailTrace_2577480
  have hstable : (prefixWord ++ tailWord_2577480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577480).length < 2 ^ (prefixWord ++ tailWord_2577480).sum := by decide
  have hdescent : baseEnd_2577480 < baseStart_2577480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577501 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 6]
def baseStart_2577501 : Nat := 118140960795 + 2577501 * 2 ^ 59
def prefixEnd_2577501 : Nat := 4983230072969 + 3 ^ 40 * 2577501 * 2
def baseEnd_2577501 : Nat := 147055211160491694353755

theorem tailTrace_2577501 : CollatzResearch.WordTrace tailWord_2577501 prefixEnd_2577501 147055211160491694353755 := by
  unfold tailWord_2577501
  simp only [CollatzResearch.WordTrace]
  refine ⟨94009184635161553969628357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62672789756774369313085571 94009184635161553969628357)
  ·
    refine ⟨17626722119092791369305317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94009184635161553969628357 17626722119092791369305317)
    ·
      refine ⟨3305010397329898381744747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17626722119092791369305317 3305010397329898381744747)
      ·
        refine ⟨4957515595994847572617121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305010397329898381744747 4957515595994847572617121)
        ·
          refine ⟨3718136696996135679462841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4957515595994847572617121 3718136696996135679462841)
          ·
            refine ⟨2788602522747101759597131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3718136696996135679462841 2788602522747101759597131)
            ·
              refine ⟨4182903784120652639395697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788602522747101759597131 4182903784120652639395697)
              ·
                refine ⟨3137177838090489479546773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182903784120652639395697 3137177838090489479546773)
                ·
                  refine ⟨147055211160491694353755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3137177838090489479546773 147055211160491694353755)
                  ·
                    rfl

theorem cell23_2577501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_2577501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577501 prefixEnd_2577501 := by exact prefixLift 2577501
  have htrace : WordTrace (prefixWord ++ tailWord_2577501) baseStart_2577501 baseEnd_2577501 := by
    simpa [prefixWord, tailWord_2577501, baseEnd_2577501] using wordTrace_append hprefix tailTrace_2577501
  have hstable : (prefixWord ++ tailWord_2577501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577501).length < 2 ^ (prefixWord ++ tailWord_2577501).sum := by decide
  have hdescent : baseEnd_2577501 < baseStart_2577501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577511 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_2577511 : Nat := 118140960795 + 2577511 * 2 ^ 59
def prefixEnd_2577511 : Nat := 4983230072969 + 3 ^ 40 * 2577511 * 2
def baseEnd_2577511 : Nat := 1323502035250970210058749

theorem tailTrace_2577511 : CollatzResearch.WordTrace tailWord_2577511 prefixEnd_2577511 1323502035250970210058749 := by
  unfold tailWord_2577511
  simp only [CollatzResearch.WordTrace]
  refine ⟨94009549365125325677492387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62673032910083550451661591 94009549365125325677492387)
  ·
    refine ⟨141014324047687988516238581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94009549365125325677492387 141014324047687988516238581)
    ·
      refine ⟨13220092879470748923397367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141014324047687988516238581 13220092879470748923397367)
      ·
        refine ⟨19830139319206123385096051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13220092879470748923397367 19830139319206123385096051)
        ·
          refine ⟨29745208978809185077644077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19830139319206123385096051 29745208978809185077644077)
          ·
            refine ⟨11154453367053444404116529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29745208978809185077644077 11154453367053444404116529)
            ·
              refine ⟨8365840025290083303087397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11154453367053444404116529 8365840025290083303087397)
              ·
                refine ⟨1568595004741890619328887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8365840025290083303087397 1568595004741890619328887)
                ·
                  refine ⟨2352892507112835928993331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568595004741890619328887 2352892507112835928993331)
                  ·
                    refine ⟨3529338760669253893489997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352892507112835928993331 3529338760669253893489997)
                    ·
                      refine ⟨1323502035250970210058749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529338760669253893489997 1323502035250970210058749)
                      ·
                        rfl

theorem cell23_2577511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_2577511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577511 prefixEnd_2577511 := by exact prefixLift 2577511
  have htrace : WordTrace (prefixWord ++ tailWord_2577511) baseStart_2577511 baseEnd_2577511 := by
    simpa [prefixWord, tailWord_2577511, baseEnd_2577511] using wordTrace_append hprefix tailTrace_2577511
  have hstable : (prefixWord ++ tailWord_2577511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577511).length < 2 ^ (prefixWord ++ tailWord_2577511).sum := by decide
  have hdescent : baseEnd_2577511 < baseStart_2577511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577554 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2577554 : Nat := 118140960795 + 2577554 * 2 ^ 59
def prefixEnd_2577554 : Nat := 4983230072969 + 3 ^ 40 * 2577554 * 2
def baseEnd_2577554 : Nat := 1323524114919113541821051

theorem tailTrace_2577554 : CollatzResearch.WordTrace tailWord_2577554 prefixEnd_2577554 1323524114919113541821051 := by
  unfold tailWord_2577554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23502779425992386005326929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62674078469313029347538477 23502779425992386005326929)
  ·
    refine ⟨17627084569494289503995197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23502779425992386005326929 17627084569494289503995197)
    ·
      refine ⟨6610156713560358563998199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17627084569494289503995197 6610156713560358563998199)
      ·
        refine ⟨9915235070340537845997299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6610156713560358563998199 9915235070340537845997299)
        ·
          refine ⟨14872852605510806768995949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9915235070340537845997299 14872852605510806768995949)
          ·
            refine ⟨5577319727066552538373481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14872852605510806768995949 5577319727066552538373481)
            ·
              refine ⟨4182989795299914403780111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577319727066552538373481 4182989795299914403780111)
              ·
                refine ⟨6274484692949871605670167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182989795299914403780111 6274484692949871605670167)
                ·
                  refine ⟨9411727039424807408505251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274484692949871605670167 9411727039424807408505251)
                  ·
                    refine ⟨14117590559137211112757877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9411727039424807408505251 14117590559137211112757877)
                    ·
                      refine ⟨1323524114919113541821051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14117590559137211112757877 1323524114919113541821051)
                      ·
                        rfl

theorem cell23_2577554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2577554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577554 prefixEnd_2577554 := by exact prefixLift 2577554
  have htrace : WordTrace (prefixWord ++ tailWord_2577554) baseStart_2577554 baseEnd_2577554 := by
    simpa [prefixWord, tailWord_2577554, baseEnd_2577554] using wordTrace_append hprefix tailTrace_2577554
  have hstable : (prefixWord ++ tailWord_2577554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577554).length < 2 ^ (prefixWord ++ tailWord_2577554).sum := by decide
  have hdescent : baseEnd_2577554 < baseStart_2577554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577578 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2577578 : Nat := 118140960795 + 2577578 * 2 ^ 59
def prefixEnd_2577578 : Nat := 4983230072969 + 3 ^ 40 * 2577578 * 2
def baseEnd_2577578 : Nat := 441178812818273815973647

theorem tailTrace_2577578 : CollatzResearch.WordTrace tailWord_2577578 prefixEnd_2577578 441178812818273815973647 := by
  unfold tailWord_2577578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23502998263970649030045347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62674662037255064080120925 23502998263970649030045347)
  ·
    refine ⟨35254497395955973545068021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23502998263970649030045347 35254497395955973545068021)
    ·
      refine ⟨3305109130870872519850127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35254497395955973545068021 3305109130870872519850127)
      ·
        refine ⟨4957663696306308779775191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305109130870872519850127 4957663696306308779775191)
        ·
          refine ⟨7436495544459463169662787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957663696306308779775191 7436495544459463169662787)
          ·
            refine ⟨11154743316689194754494181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436495544459463169662787 11154743316689194754494181)
            ·
              refine ⟨2091514371879224016467659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11154743316689194754494181 2091514371879224016467659)
              ·
                refine ⟨3137271557818836024701489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091514371879224016467659 3137271557818836024701489)
                ·
                  refine ⟨2352953668364127018526117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137271557818836024701489 2352953668364127018526117)
                  ·
                    refine ⟨441178812818273815973647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352953668364127018526117 441178812818273815973647)
                    ·
                      rfl

theorem cell23_2577578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2577578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577578 prefixEnd_2577578 := by exact prefixLift 2577578
  have htrace : WordTrace (prefixWord ++ tailWord_2577578) baseStart_2577578 baseEnd_2577578 := by
    simpa [prefixWord, tailWord_2577578, baseEnd_2577578] using wordTrace_append hprefix tailTrace_2577578
  have hstable : (prefixWord ++ tailWord_2577578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577578).length < 2 ^ (prefixWord ++ tailWord_2577578).sum := by decide
  have hdescent : baseEnd_2577578 < baseStart_2577578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577580 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2577580 : Nat := 118140960795 + 2577580 * 2 ^ 59
def prefixEnd_2577580 : Nat := 4983230072969 + 3 ^ 40 * 2577580 * 2
def baseEnd_2577580 : Nat := 1323537465416130440095931

theorem tailTrace_2577580 : CollatzResearch.WordTrace tailWord_2577580 prefixEnd_2577580 1323537465416130440095931 := by
  unfold tailWord_2577580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47006033000937675230877097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62674710667916900307836129 47006033000937675230877097)
  ·
    refine ⟨35254524750703256423157823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47006033000937675230877097 35254524750703256423157823)
    ·
      refine ⟨52881787126054884634736735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35254524750703256423157823 52881787126054884634736735)
      ·
        refine ⟨79322680689082326952105103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52881787126054884634736735 79322680689082326952105103)
        ·
          refine ⟨118984021033623490428157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79322680689082326952105103 118984021033623490428157655)
          ·
            refine ⟨178476031550435235642236483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118984021033623490428157655 178476031550435235642236483)
            ·
              refine ⟨267714047325652853463354725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178476031550435235642236483 267714047325652853463354725)
              ·
                refine ⟨50196383873559910024379011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267714047325652853463354725 50196383873559910024379011)
                ·
                  refine ⟨75294575810339865036568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50196383873559910024379011 75294575810339865036568517)
                  ·
                    refine ⟨14117732964438724694356597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75294575810339865036568517 14117732964438724694356597)
                    ·
                      refine ⟨1323537465416130440095931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14117732964438724694356597 1323537465416130440095931)
                      ·
                        rfl

theorem cell23_2577580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2577580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577580 prefixEnd_2577580 := by exact prefixLift 2577580
  have htrace : WordTrace (prefixWord ++ tailWord_2577580) baseStart_2577580 baseEnd_2577580 := by
    simpa [prefixWord, tailWord_2577580, baseEnd_2577580] using wordTrace_append hprefix tailTrace_2577580
  have hstable : (prefixWord ++ tailWord_2577580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577580).length < 2 ^ (prefixWord ++ tailWord_2577580).sum := by decide
  have hdescent : baseEnd_2577580 < baseStart_2577580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577584 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_2577584 : Nat := 118140960795 + 2577584 * 2 ^ 59
def prefixEnd_2577584 : Nat := 4983230072969 + 3 ^ 40 * 2577584 * 2
def baseEnd_2577584 : Nat := 1323539519338748424445913

theorem tailTrace_2577584 : CollatzResearch.WordTrace tailWord_2577584 prefixEnd_2577584 1323539519338748424445913 := by
  unfold tailWord_2577584
  simp only [CollatzResearch.WordTrace]
  refine ⟨47006105946930429572449903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62674807929240572763266537 47006105946930429572449903)
  ·
    refine ⟨70509158920395644358674855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47006105946930429572449903 70509158920395644358674855)
    ·
      refine ⟨105763738380593466538012283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70509158920395644358674855 105763738380593466538012283)
      ·
        refine ⟨158645607570890199807018425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105763738380593466538012283 158645607570890199807018425)
        ·
          refine ⟨118984205678167649855263819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158645607570890199807018425 118984205678167649855263819)
          ·
            refine ⟨178476308517251474782895729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118984205678167649855263819 178476308517251474782895729)
            ·
              refine ⟨133857231387938606087171797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178476308517251474782895729 133857231387938606087171797)
              ·
                refine ⟨3137278860654811080168089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133857231387938606087171797 3137278860654811080168089)
                ·
                  refine ⟨2352959145491108310126067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137278860654811080168089 2352959145491108310126067)
                  ·
                    refine ⟨3529438718236662465189101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352959145491108310126067 3529438718236662465189101)
                    ·
                      refine ⟨1323539519338748424445913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529438718236662465189101 1323539519338748424445913)
                      ·
                        rfl

theorem cell23_2577584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_2577584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577584 prefixEnd_2577584 := by exact prefixLift 2577584
  have htrace : WordTrace (prefixWord ++ tailWord_2577584) baseStart_2577584 baseEnd_2577584 := by
    simpa [prefixWord, tailWord_2577584, baseEnd_2577584] using wordTrace_append hprefix tailTrace_2577584
  have hstable : (prefixWord ++ tailWord_2577584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577584).length < 2 ^ (prefixWord ++ tailWord_2577584).sum := by decide
  have hdescent : baseEnd_2577584 < baseStart_2577584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577601 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2577601 : Nat := 118140960795 + 2577601 * 2 ^ 59
def prefixEnd_2577601 : Nat := 4983230072969 + 3 ^ 40 * 2577601 * 2
def baseEnd_2577601 : Nat := 1323548248509874857933335

theorem tailTrace_2577601 : CollatzResearch.WordTrace tailWord_2577601 prefixEnd_2577601 1323548248509874857933335 := by
  unfold tailWord_2577601
  simp only [CollatzResearch.WordTrace]
  refine ⟨94012831934799271048268657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62675221289866180698845771 94012831934799271048268657)
  ·
    refine ⟨70509623951099453286201493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94012831934799271048268657 70509623951099453286201493)
    ·
      refine ⟨3305138622707786872790695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70509623951099453286201493 3305138622707786872790695)
      ·
        refine ⟨4957707934061680309186043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305138622707786872790695 4957707934061680309186043)
        ·
          refine ⟨7436561901092520463779065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957707934061680309186043 7436561901092520463779065)
          ·
            refine ⟨5577421425819390347834299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7436561901092520463779065 5577421425819390347834299)
            ·
              refine ⟨8366132138729085521751449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577421425819390347834299 8366132138729085521751449)
              ·
                refine ⟨6274599104046814141313587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8366132138729085521751449 6274599104046814141313587)
                ·
                  refine ⟨9411898656070221211970381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274599104046814141313587 9411898656070221211970381)
                  ·
                    refine ⟨3529461996026332954488893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9411898656070221211970381 3529461996026332954488893)
                    ·
                      refine ⟨1323548248509874857933335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529461996026332954488893 1323548248509874857933335)
                      ·
                        rfl

theorem cell23_2577601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2577601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577601 prefixEnd_2577601 := by exact prefixLift 2577601
  have htrace : WordTrace (prefixWord ++ tailWord_2577601) baseStart_2577601 baseEnd_2577601 := by
    simpa [prefixWord, tailWord_2577601, baseEnd_2577601] using wordTrace_append hprefix tailTrace_2577601
  have hstable : (prefixWord ++ tailWord_2577601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577601).length < 2 ^ (prefixWord ++ tailWord_2577601).sum := by decide
  have hdescent : baseEnd_2577601 < baseStart_2577601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577657 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2577657 : Nat := 118140960795 + 2577657 * 2 ^ 59
def prefixEnd_2577657 : Nat := 4983230072969 + 3 ^ 40 * 2577657 * 2
def baseEnd_2577657 : Nat := 1323577003426526638833077

theorem tailTrace_2577657 : CollatzResearch.WordTrace tailWord_2577657 prefixEnd_2577657 1323577003426526638833077 := by
  unfold tailWord_2577657
  simp only [CollatzResearch.WordTrace]
  refine ⟨94014874422596392612307225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62676582948397595074871483 94014874422596392612307225)
  ·
    refine ⟨70511155816947294459230419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94014874422596392612307225 70511155816947294459230419)
    ·
      refine ⟨105766733725420941688845629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70511155816947294459230419 105766733725420941688845629)
      ·
        refine ⟨39662525147032853133317111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105766733725420941688845629 39662525147032853133317111)
        ·
          refine ⟨59493787720549279699975667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39662525147032853133317111 59493787720549279699975667)
          ·
            refine ⟨89240681580823919549963501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59493787720549279699975667 89240681580823919549963501)
            ·
              refine ⟨33465255592808969831236313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89240681580823919549963501 33465255592808969831236313)
              ·
                refine ⟨25098941694606727373427235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33465255592808969831236313 25098941694606727373427235)
                ·
                  refine ⟨37648412541910091060140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25098941694606727373427235 37648412541910091060140853)
                  ·
                    refine ⟨3529538675804071036888205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37648412541910091060140853 3529538675804071036888205)
                    ·
                      refine ⟨1323577003426526638833077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529538675804071036888205 1323577003426526638833077)
                      ·
                        rfl

theorem cell23_2577657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2577657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577657 prefixEnd_2577657 := by exact prefixLift 2577657
  have htrace : WordTrace (prefixWord ++ tailWord_2577657) baseStart_2577657 baseEnd_2577657 := by
    simpa [prefixWord, tailWord_2577657, baseEnd_2577657] using wordTrace_append hprefix tailTrace_2577657
  have hstable : (prefixWord ++ tailWord_2577657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577657).length < 2 ^ (prefixWord ++ tailWord_2577657).sum := by decide
  have hdescent : baseEnd_2577657 < baseStart_2577657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577687 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2577687 : Nat := 118140960795 + 2577687 * 2 ^ 59
def prefixEnd_2577687 : Nat := 4983230072969 + 3 ^ 40 * 2577687 * 2
def baseEnd_2577687 : Nat := 1323592407846161521457939

theorem tailTrace_2577687 : CollatzResearch.WordTrace tailWord_2577687 prefixEnd_2577687 1323592407846161521457939 := by
  unfold tailWord_2577687
  simp only [CollatzResearch.WordTrace]
  refine ⟨94015968612487707735899315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62677312408325138490599543 94015968612487707735899315)
  ·
    refine ⟨141023952918731561603848973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94015968612487707735899315 141023952918731561603848973)
    ·
      refine ⟨52883982344524335601443365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141023952918731561603848973 52883982344524335601443365)
      ·
        refine ⟨9915746689598312925270631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52883982344524335601443365 9915746689598312925270631)
        ·
          refine ⟨14873620034397469387905947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9915746689598312925270631 14873620034397469387905947)
          ·
            refine ⟨22310430051596204081858921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14873620034397469387905947 22310430051596204081858921)
            ·
              refine ⟨16732822538697153061394191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22310430051596204081858921 16732822538697153061394191)
              ·
                refine ⟨25099233808045729592091287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16732822538697153061394191 25099233808045729592091287)
                ·
                  refine ⟨37648850712068594388136931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25099233808045729592091287 37648850712068594388136931)
                  ·
                    refine ⟨56473276068102891582205397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37648850712068594388136931 56473276068102891582205397)
                    ·
                      refine ⟨1323592407846161521457939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56473276068102891582205397 1323592407846161521457939)
                      ·
                        rfl

theorem cell23_2577687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2577687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577687 prefixEnd_2577687 := by exact prefixLift 2577687
  have htrace : WordTrace (prefixWord ++ tailWord_2577687) baseStart_2577687 baseEnd_2577687 := by
    simpa [prefixWord, tailWord_2577687, baseEnd_2577687] using wordTrace_append hprefix tailTrace_2577687
  have hstable : (prefixWord ++ tailWord_2577687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577687).length < 2 ^ (prefixWord ++ tailWord_2577687).sum := by decide
  have hdescent : baseEnd_2577687 < baseStart_2577687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577714 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2577714 : Nat := 118140960795 + 2577714 * 2 ^ 59
def prefixEnd_2577714 : Nat := 4983230072969 + 3 ^ 40 * 2577714 * 2
def baseEnd_2577714 : Nat := 1323606271823832915820315

theorem tailTrace_2577714 : CollatzResearch.WordTrace tailWord_2577714 prefixEnd_2577714 1323606271823832915820315 := by
  unfold tailWord_2577714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23504238345847472836783049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62677968922259927564754797 23504238345847472836783049)
  ·
    refine ⟨17628178759385604627587287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23504238345847472836783049 17628178759385604627587287)
    ·
      refine ⟨26442268139078406941380931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628178759385604627587287 26442268139078406941380931)
      ·
        refine ⟨39663402208617610412071397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26442268139078406941380931 39663402208617610412071397)
        ·
          refine ⟨7436887914115801952263387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39663402208617610412071397 7436887914115801952263387)
          ·
            refine ⟨11155331871173702928395081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436887914115801952263387 11155331871173702928395081)
            ·
              refine ⟨8366498903380277196296311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155331871173702928395081 8366498903380277196296311)
              ·
                refine ⟨12549748355070415794444467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366498903380277196296311 12549748355070415794444467)
                ·
                  refine ⟨18824622532605623691666701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12549748355070415794444467 18824622532605623691666701)
                  ·
                    refine ⟨7059233449727108884375013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18824622532605623691666701 7059233449727108884375013)
                    ·
                      refine ⟨1323606271823832915820315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7059233449727108884375013 1323606271823832915820315)
                      ·
                        rfl

theorem cell23_2577714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2577714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577714 prefixEnd_2577714 := by exact prefixLift 2577714
  have htrace : WordTrace (prefixWord ++ tailWord_2577714) baseStart_2577714 baseEnd_2577714 := by
    simpa [prefixWord, tailWord_2577714, baseEnd_2577714] using wordTrace_append hprefix tailTrace_2577714
  have hstable : (prefixWord ++ tailWord_2577714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577714).length < 2 ^ (prefixWord ++ tailWord_2577714).sum := by decide
  have hdescent : baseEnd_2577714 < baseStart_2577714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577737 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 8]
def baseStart_2577737 : Nat := 118140960795 + 2577737 * 2 ^ 59
def prefixEnd_2577737 : Nat := 4983230072969 + 3 ^ 40 * 2577737 * 2
def baseEnd_2577737 : Nat := 147068675764320702870301

theorem tailTrace_2577737 : CollatzResearch.WordTrace tailWord_2577737 prefixEnd_2577737 147068675764320702870301 := by
  unfold tailWord_2577737
  simp only [CollatzResearch.WordTrace]
  refine ⟨94017792262306566275219465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62678528174871044183479643 94017792262306566275219465)
  ·
    refine ⟨70513344196729924706414599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94017792262306566275219465 70513344196729924706414599)
    ·
      refine ⟨105770016295094887059621899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70513344196729924706414599 105770016295094887059621899)
      ·
        refine ⟨158655024442642330589432849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105770016295094887059621899 158655024442642330589432849)
        ·
          refine ⟨118991268331981747942074637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158655024442642330589432849 118991268331981747942074637)
          ·
            refine ⟨44621725624493155478277989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118991268331981747942074637 44621725624493155478277989)
            ·
              refine ⟨8366573554592466652177123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44621725624493155478277989 8366573554592466652177123)
              ·
                refine ⟨12549860331888699978265685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366573554592466652177123 12549860331888699978265685)
                ·
                  refine ⟨147068675764320702870301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12549860331888699978265685 147068675764320702870301)
                  ·
                    rfl

theorem cell23_2577737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_2577737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577737 prefixEnd_2577737 := by exact prefixLift 2577737
  have htrace : WordTrace (prefixWord ++ tailWord_2577737) baseStart_2577737 baseEnd_2577737 := by
    simpa [prefixWord, tailWord_2577737, baseEnd_2577737] using wordTrace_append hprefix tailTrace_2577737
  have hstable : (prefixWord ++ tailWord_2577737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577737).length < 2 ^ (prefixWord ++ tailWord_2577737).sum := by decide
  have hdescent : baseEnd_2577737 < baseStart_2577737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577768 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2577768 : Nat := 118140960795 + 2577768 * 2 ^ 59
def prefixEnd_2577768 : Nat := 4983230072969 + 3 ^ 40 * 2577768 * 2
def baseEnd_2577768 : Nat := 1323633999779175704545067

theorem tailTrace_2577768 : CollatzResearch.WordTrace tailWord_2577768 prefixEnd_2577768 1323633999779175704545067 := by
  unfold tailWord_2577768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009461462597129284798979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62679281950129505713065305 47009461462597129284798979)
  ·
    refine ⟨70514192193895693927198469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47009461462597129284798979 70514192193895693927198469)
    ·
      refine ⟨13221411036355442611349713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70514192193895693927198469 13221411036355442611349713)
      ·
        refine ⟨9916058277266581958512285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13221411036355442611349713 9916058277266581958512285)
        ·
          refine ⟨3718521853974968234442107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9916058277266581958512285 3718521853974968234442107)
          ·
            refine ⟨5577782780962452351663161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718521853974968234442107 5577782780962452351663161)
            ·
              refine ⟨4183337085721839263747371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577782780962452351663161 4183337085721839263747371)
              ·
                refine ⟨6275005628582758895621057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183337085721839263747371 6275005628582758895621057)
                ·
                  refine ⟨4706254221437069171715793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6275005628582758895621057 4706254221437069171715793)
                  ·
                    refine ⟨3529690666077801878786845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706254221437069171715793 3529690666077801878786845)
                    ·
                      refine ⟨1323633999779175704545067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529690666077801878786845 1323633999779175704545067)
                      ·
                        rfl

theorem cell23_2577768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2577768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577768 prefixEnd_2577768 := by exact prefixLift 2577768
  have htrace : WordTrace (prefixWord ++ tailWord_2577768) baseStart_2577768 baseEnd_2577768 := by
    simpa [prefixWord, tailWord_2577768, baseEnd_2577768] using wordTrace_append hprefix tailTrace_2577768
  have hstable : (prefixWord ++ tailWord_2577768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577768).length < 2 ^ (prefixWord ++ tailWord_2577768).sum := by decide
  have hdescent : baseEnd_2577768 < baseStart_2577768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577804 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2577804 : Nat := 118140960795 + 2577804 * 2 ^ 59
def prefixEnd_2577804 : Nat := 4983230072969 + 3 ^ 40 * 2577804 * 2
def baseEnd_2577804 : Nat := 1323652485082737563694901

theorem tailTrace_2577804 : CollatzResearch.WordTrace tailWord_2577804 prefixEnd_2577804 1323652485082737563694901 := by
  unfold tailWord_2577804
  simp only [CollatzResearch.WordTrace]
  refine ⟨47010117976531918358954233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62680157302042557811938977 47010117976531918358954233)
  ·
    refine ⟨35257588482398938769215675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47010117976531918358954233 35257588482398938769215675)
    ·
      refine ⟨52886382723598408153823513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35257588482398938769215675 52886382723598408153823513)
      ·
        refine ⟨39664787042698806115367635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52886382723598408153823513 39664787042698806115367635)
        ·
          refine ⟨59497180564048209173051453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39664787042698806115367635 59497180564048209173051453)
          ·
            refine ⟨22311442711518078439894295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59497180564048209173051453 22311442711518078439894295)
            ·
              refine ⟨33467164067277117659841443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22311442711518078439894295 33467164067277117659841443)
              ·
                refine ⟨50200746100915676489762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33467164067277117659841443 50200746100915676489762165)
                ·
                  refine ⟨4706319946960844670915203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50200746100915676489762165 4706319946960844670915203)
                  ·
                    refine ⟨7059479920441267006372805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4706319946960844670915203 7059479920441267006372805)
                    ·
                      refine ⟨1323652485082737563694901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7059479920441267006372805 1323652485082737563694901)
                      ·
                        rfl

theorem cell23_2577804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2577804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577804 prefixEnd_2577804 := by exact prefixLift 2577804
  have htrace : WordTrace (prefixWord ++ tailWord_2577804) baseStart_2577804 baseEnd_2577804 := by
    simpa [prefixWord, tailWord_2577804, baseEnd_2577804] using wordTrace_append hprefix tailTrace_2577804
  have hstable : (prefixWord ++ tailWord_2577804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577804).length < 2 ^ (prefixWord ++ tailWord_2577804).sum := by decide
  have hdescent : baseEnd_2577804 < baseStart_2577804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577821 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2577821 : Nat := 118140960795 + 2577821 * 2 ^ 59
def prefixEnd_2577821 : Nat := 4983230072969 + 3 ^ 40 * 2577821 * 2
def baseEnd_2577821 : Nat := 1323661214253863997182323

theorem tailTrace_2577821 : CollatzResearch.WordTrace tailWord_2577821 prefixEnd_2577821 1323661214253863997182323 := by
  unfold tailWord_2577821
  simp only [CollatzResearch.WordTrace]
  refine ⟨94020855994002248621277317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62680570662668165747518211 94020855994002248621277317)
  ·
    refine ⟨17628910498875421616489497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94020855994002248621277317 17628910498875421616489497)
    ·
      refine ⟨13221682874156566212367123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17628910498875421616489497 13221682874156566212367123)
      ·
        refine ⟨19832524311234849318550685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13221682874156566212367123 19832524311234849318550685)
        ·
          refine ⟨7437196616713068494456507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19832524311234849318550685 7437196616713068494456507)
          ·
            refine ⟨11155794925069602741684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7437196616713068494456507 11155794925069602741684761)
            ·
              refine ⟨8366846193802202056263571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155794925069602741684761 8366846193802202056263571)
              ·
                refine ⟨12550269290703303084395357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366846193802202056263571 12550269290703303084395357)
                ·
                  refine ⟨4706350984013738656648259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12550269290703303084395357 4706350984013738656648259)
                  ·
                    refine ⟨7059526476020607984972389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4706350984013738656648259 7059526476020607984972389)
                    ·
                      refine ⟨1323661214253863997182323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7059526476020607984972389 1323661214253863997182323)
                      ·
                        rfl

theorem cell23_2577821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2577821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577821 prefixEnd_2577821 := by exact prefixLift 2577821
  have htrace : WordTrace (prefixWord ++ tailWord_2577821) baseStart_2577821 baseEnd_2577821 := by
    simpa [prefixWord, tailWord_2577821, baseEnd_2577821] using wordTrace_append hprefix tailTrace_2577821
  have hstable : (prefixWord ++ tailWord_2577821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577821).length < 2 ^ (prefixWord ++ tailWord_2577821).sum := by decide
  have hdescent : baseEnd_2577821 < baseStart_2577821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577831 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2577831 : Nat := 118140960795 + 2577831 * 2 ^ 59
def prefixEnd_2577831 : Nat := 4983230072969 + 3 ^ 40 * 2577831 * 2
def baseEnd_2577831 : Nat := 441222116353469652685759

theorem tailTrace_2577831 : CollatzResearch.WordTrace tailWord_2577831 prefixEnd_2577831 441222116353469652685759 := by
  unfold tailWord_2577831
  simp only [CollatzResearch.WordTrace]
  refine ⟨94021220723966020329141347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62680813815977346886094231 94021220723966020329141347)
  ·
    refine ⟨141031831085949030493712021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94021220723966020329141347 141031831085949030493712021)
    ·
      refine ⟨6610867082153860804392751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141031831085949030493712021 6610867082153860804392751)
      ·
        refine ⟨9916300623230791206589127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6610867082153860804392751 9916300623230791206589127)
        ·
          refine ⟨14874450934846186809883691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916300623230791206589127 14874450934846186809883691)
          ·
            refine ⟨22311676402269280214825537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14874450934846186809883691 22311676402269280214825537)
            ·
              refine ⟨16733757301701960161119153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22311676402269280214825537 16733757301701960161119153)
              ·
                refine ⟨12550317976276470120839365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16733757301701960161119153 12550317976276470120839365)
                ·
                  refine ⟨2353184620551838147657381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12550317976276470120839365 2353184620551838147657381)
                  ·
                    refine ⟨441222116353469652685759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353184620551838147657381 441222116353469652685759)
                    ·
                      rfl

theorem cell23_2577831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2577831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577831 prefixEnd_2577831 := by exact prefixLift 2577831
  have htrace : WordTrace (prefixWord ++ tailWord_2577831) baseStart_2577831 baseEnd_2577831 := by
    simpa [prefixWord, tailWord_2577831, baseEnd_2577831] using wordTrace_append hprefix tailTrace_2577831
  have hstable : (prefixWord ++ tailWord_2577831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577831).length < 2 ^ (prefixWord ++ tailWord_2577831).sum := by decide
  have hdescent : baseEnd_2577831 < baseStart_2577831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2577854 : Nat := 118140960795 + 2577854 * 2 ^ 59
def prefixEnd_2577854 : Nat := 4983230072969 + 3 ^ 40 * 2577854 * 2
def baseEnd_2577854 : Nat := 1323678159115462368069671

theorem tailTrace_2577854 : CollatzResearch.WordTrace tailWord_2577854 prefixEnd_2577854 1323678159115462368069671 := by
  unfold tailWord_2577854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752757450360336907153577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62681373068588463504819077 11752757450360336907153577)
  ·
    refine ⟨8814568087770252680365183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11752757450360336907153577 8814568087770252680365183)
    ·
      refine ⟨13221852131655379020547775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8814568087770252680365183 13221852131655379020547775)
      ·
        refine ⟨19832778197483068530821663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13221852131655379020547775 19832778197483068530821663)
        ·
          refine ⟨29749167296224602796232495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19832778197483068530821663 29749167296224602796232495)
          ·
            refine ⟨44623750944336904194348743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29749167296224602796232495 44623750944336904194348743)
            ·
              refine ⟨66935626416505356291523115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44623750944336904194348743 66935626416505356291523115)
              ·
                refine ⟨100403439624758034437284673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66935626416505356291523115 100403439624758034437284673)
                ·
                  refine ⟨75302579718568525827963505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100403439624758034437284673 75302579718568525827963505)
                  ·
                    refine ⟨56476934788926394370972629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75302579718568525827963505 56476934788926394370972629)
                    ·
                      refine ⟨1323678159115462368069671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56476934788926394370972629 1323678159115462368069671)
                      ·
                        rfl

theorem cell23_2577854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2577854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577854 prefixEnd_2577854 := by exact prefixLift 2577854
  have htrace : WordTrace (prefixWord ++ tailWord_2577854) baseStart_2577854 baseEnd_2577854 := by
    simpa [prefixWord, tailWord_2577854, baseEnd_2577854] using wordTrace_append hprefix tailTrace_2577854
  have hstable : (prefixWord ++ tailWord_2577854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577854).length < 2 ^ (prefixWord ++ tailWord_2577854).sum := by decide
  have hdescent : baseEnd_2577854 < baseStart_2577854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577868 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2577868 : Nat := 118140960795 + 2577868 * 2 ^ 59
def prefixEnd_2577868 : Nat := 4983230072969 + 3 ^ 40 * 2577868 * 2
def baseEnd_2577868 : Nat := 1323685347844625313294607

theorem tailTrace_2577868 : CollatzResearch.WordTrace tailWord_2577868 prefixEnd_2577868 1323685347844625313294607 := by
  unfold tailWord_2577868
  simp only [CollatzResearch.WordTrace]
  refine ⟨47011285112415987824119129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62681713483221317098825505 47011285112415987824119129)
  ·
    refine ⟨35258463834311990868089347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47011285112415987824119129 35258463834311990868089347)
    ·
      refine ⟨52887695751467986302134021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35258463834311990868089347 52887695751467986302134021)
      ·
        refine ⟨9916442953400247431650129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52887695751467986302134021 9916442953400247431650129)
        ·
          refine ⟨7437332215050185573737597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9916442953400247431650129 7437332215050185573737597)
          ·
            refine ⟨2788999580643819590151599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7437332215050185573737597 2788999580643819590151599)
            ·
              refine ⟨4183499370965729385227399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788999580643819590151599 4183499370965729385227399)
              ·
                refine ⟨6275249056448594077841099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183499370965729385227399 6275249056448594077841099)
                ·
                  refine ⟨9412873584672891116761649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275249056448594077841099 9412873584672891116761649)
                  ·
                    refine ⟨7059655188504668337571237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9412873584672891116761649 7059655188504668337571237)
                    ·
                      refine ⟨1323685347844625313294607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7059655188504668337571237 1323685347844625313294607)
                      ·
                        rfl

theorem cell23_2577868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2577868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577868 prefixEnd_2577868 := by exact prefixLift 2577868
  have htrace : WordTrace (prefixWord ++ tailWord_2577868) baseStart_2577868 baseEnd_2577868 := by
    simpa [prefixWord, tailWord_2577868, baseEnd_2577868] using wordTrace_append hprefix tailTrace_2577868
  have hstable : (prefixWord ++ tailWord_2577868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577868).length < 2 ^ (prefixWord ++ tailWord_2577868).sum := by decide
  have hdescent : baseEnd_2577868 < baseStart_2577868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577871 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_2577871 : Nat := 118140960795 + 2577871 * 2 ^ 59
def prefixEnd_2577871 : Nat := 4983230072969 + 3 ^ 40 * 2577871 * 2
def baseEnd_2577871 : Nat := 1323686888286588801557093

theorem tailTrace_2577871 : CollatzResearch.WordTrace tailWord_2577871 prefixEnd_2577871 1323686888286588801557093 := by
  unfold tailWord_2577871
  simp only [CollatzResearch.WordTrace]
  refine ⟨94022679643821107160597467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62681786429214071440398311 94022679643821107160597467)
  ·
    refine ⟨141034019465731660740896201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94022679643821107160597467 141034019465731660740896201)
    ·
      refine ⟨105775514599298745555672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141034019465731660740896201 105775514599298745555672151)
      ·
        refine ⟨158663271898948118333508227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105775514599298745555672151 158663271898948118333508227)
        ·
          refine ⟨237994907848422177500262341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158663271898948118333508227 237994907848422177500262341)
          ·
            refine ⟨44624045221579158281299189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237994907848422177500262341 44624045221579158281299189)
            ·
              refine ⟨4183504239523046088871799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44624045221579158281299189 4183504239523046088871799)
              ·
                refine ⟨6275256359284569133307699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183504239523046088871799 6275256359284569133307699)
                ·
                  refine ⟨9412884538926853699961549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275256359284569133307699 9412884538926853699961549)
                  ·
                    refine ⟨3529831702097570137485581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9412884538926853699961549 3529831702097570137485581)
                    ·
                      refine ⟨1323686888286588801557093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529831702097570137485581 1323686888286588801557093)
                      ·
                        rfl

theorem cell23_2577871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_2577871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577871 prefixEnd_2577871 := by exact prefixLift 2577871
  have htrace : WordTrace (prefixWord ++ tailWord_2577871) baseStart_2577871 baseEnd_2577871 := by
    simpa [prefixWord, tailWord_2577871, baseEnd_2577871] using wordTrace_append hprefix tailTrace_2577871
  have hstable : (prefixWord ++ tailWord_2577871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577871).length < 2 ^ (prefixWord ++ tailWord_2577871).sum := by decide
  have hdescent : baseEnd_2577871 < baseStart_2577871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577878 : List Nat := [5, 2, 1, 1, 1, 2, 4, 7]
def baseStart_2577878 : Nat := 118140960795 + 2577878 * 2 ^ 59
def prefixEnd_2577878 : Nat := 4983230072969 + 3 ^ 40 * 2577878 * 2
def baseEnd_2577878 : Nat := 49025573431524824969243

theorem tailTrace_2577878 : CollatzResearch.WordTrace tailWord_2577878 prefixEnd_2577878 49025573431524824969243 := by
  unfold tailWord_2577878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876433434674734209756393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62681956636530498237401525 5876433434674734209756393)
  ·
    refine ⟨4407325076006050657317295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5876433434674734209756393 4407325076006050657317295)
    ·
      refine ⟨6610987614009075985975943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407325076006050657317295 6610987614009075985975943)
      ·
        refine ⟨9916481421013613978963915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6610987614009075985975943 9916481421013613978963915)
        ·
          refine ⟨14874722131520420968445873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916481421013613978963915 14874722131520420968445873)
          ·
            refine ⟨11156041598640315726334405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14874722131520420968445873 11156041598640315726334405)
            ·
              refine ⟨2091757799745059198687701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11156041598640315726334405 2091757799745059198687701)
              ·
                refine ⟨49025573431524824969243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2091757799745059198687701 49025573431524824969243)
                ·
                  rfl

theorem cell23_2577878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_2577878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577878 prefixEnd_2577878 := by exact prefixLift 2577878
  have htrace : WordTrace (prefixWord ++ tailWord_2577878) baseStart_2577878 baseEnd_2577878 := by
    simpa [prefixWord, tailWord_2577878, baseEnd_2577878] using wordTrace_append hprefix tailTrace_2577878
  have hstable : (prefixWord ++ tailWord_2577878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577878).length < 2 ^ (prefixWord ++ tailWord_2577878).sum := by decide
  have hdescent : baseEnd_2577878 < baseStart_2577878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577911 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_2577911 : Nat := 118140960795 + 2577911 * 2 ^ 59
def prefixEnd_2577911 : Nat := 4983230072969 + 3 ^ 40 * 2577911 * 2
def baseEnd_2577911 : Nat := 1323707427512768645056909

theorem tailTrace_2577911 : CollatzResearch.WordTrace tailWord_2577911 prefixEnd_2577911 1323707427512768645056909 := by
  unfold tailWord_2577911
  simp only [CollatzResearch.WordTrace]
  refine ⟨94024138563676193992053587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62682759042450795994702391 94024138563676193992053587)
  ·
    refine ⟨141036207845514290988080381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94024138563676193992053587 141036207845514290988080381)
    ·
      refine ⟨52888577942067859120530143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141036207845514290988080381 52888577942067859120530143)
      ·
        refine ⟨79332866913101788680795215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52888577942067859120530143 79332866913101788680795215)
        ·
          refine ⟨118999300369652683021192823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79332866913101788680795215 118999300369652683021192823)
          ·
            refine ⟨178498950554479024531789235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118999300369652683021192823 178498950554479024531789235)
            ·
              refine ⟨267748425831718536797683853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178498950554479024531789235 267748425831718536797683853)
              ·
                refine ⟨100405659686894451299131445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267748425831718536797683853 100405659686894451299131445)
                ·
                  refine ⟨9413030595646354809293573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100405659686894451299131445 9413030595646354809293573)
                  ·
                    refine ⟨1764943236683691526742545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9413030595646354809293573 1764943236683691526742545)
                    ·
                      refine ⟨1323707427512768645056909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764943236683691526742545 1323707427512768645056909)
                      ·
                        rfl

theorem cell23_2577911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_2577911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577911 prefixEnd_2577911 := by exact prefixLift 2577911
  have htrace : WordTrace (prefixWord ++ tailWord_2577911) baseStart_2577911 baseEnd_2577911 := by
    simpa [prefixWord, tailWord_2577911, baseEnd_2577911] using wordTrace_append hprefix tailTrace_2577911
  have hstable : (prefixWord ++ tailWord_2577911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577911).length < 2 ^ (prefixWord ++ tailWord_2577911).sum := by decide
  have hdescent : baseEnd_2577911 < baseStart_2577911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577914 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2577914 : Nat := 118140960795 + 2577914 * 2 ^ 59
def prefixEnd_2577914 : Nat := 4983230072969 + 3 ^ 40 * 2577914 * 2
def baseEnd_2577914 : Nat := 1323708967954732133319395

theorem tailTrace_2577914 : CollatzResearch.WordTrace tailWord_2577914 prefixEnd_2577914 1323708967954732133319395 := by
  unfold tailWord_2577914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506061995666331376103199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62682831988443550336275197 23506061995666331376103199)
  ·
    refine ⟨35259092993499497064154799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23506061995666331376103199 35259092993499497064154799)
    ·
      refine ⟨52888639490249245596232199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35259092993499497064154799 52888639490249245596232199)
      ·
        refine ⟨79332959235373868394348299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52888639490249245596232199 79332959235373868394348299)
        ·
          refine ⟨118999438853060802591522449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79332959235373868394348299 118999438853060802591522449)
          ·
            refine ⟨89249579139795601943641837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118999438853060802591522449 89249579139795601943641837)
            ·
              refine ⟨33468592177423350728865689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89249579139795601943641837 33468592177423350728865689)
              ·
                refine ⟨25101444133067513046649267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33468592177423350728865689 25101444133067513046649267)
                ·
                  refine ⟨37652166199601269569973901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25101444133067513046649267 37652166199601269569973901)
                  ·
                    refine ⟨14119562324850476088740213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37652166199601269569973901 14119562324850476088740213)
                    ·
                      refine ⟨1323708967954732133319395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14119562324850476088740213 1323708967954732133319395)
                      ·
                        rfl

theorem cell23_2577914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2577914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577914 prefixEnd_2577914 := by exact prefixLift 2577914
  have htrace : WordTrace (prefixWord ++ tailWord_2577914) baseStart_2577914 baseEnd_2577914 := by
    simpa [prefixWord, tailWord_2577914, baseEnd_2577914] using wordTrace_append hprefix tailTrace_2577914
  have hstable : (prefixWord ++ tailWord_2577914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577914).length < 2 ^ (prefixWord ++ tailWord_2577914).sum := by decide
  have hdescent : baseEnd_2577914 < baseStart_2577914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577922 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2577922 : Nat := 118140960795 + 2577922 * 2 ^ 59
def prefixEnd_2577922 : Nat := 4983230072969 + 3 ^ 40 * 2577922 * 2
def baseEnd_2577922 : Nat := 1323713075799968102019359

theorem tailTrace_2577922 : CollatzResearch.WordTrace tailWord_2577922 prefixEnd_2577922 1323713075799968102019359 := by
  unfold tailWord_2577922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506134941659085717676005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62683026511090895247136013 23506134941659085717676005)
  ·
    refine ⟨4407400301561078572064251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23506134941659085717676005 4407400301561078572064251)
    ·
      refine ⟨6611100452341617858096377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407400301561078572064251 6611100452341617858096377)
      ·
        refine ⟨4958325339256213393572283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6611100452341617858096377 4958325339256213393572283)
        ·
          refine ⟨7437488008884320090358425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958325339256213393572283 7437488008884320090358425)
          ·
            refine ⟨5578116006663240067768819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7437488008884320090358425 5578116006663240067768819)
            ·
              refine ⟨8367174009994860101653229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578116006663240067768819 8367174009994860101653229)
              ·
                refine ⟨3137690253748072538119961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8367174009994860101653229 3137690253748072538119961)
                ·
                  refine ⟨2353267690311054403589971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137690253748072538119961 2353267690311054403589971)
                  ·
                    refine ⟨3529901535466581605384957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353267690311054403589971 3529901535466581605384957)
                    ·
                      refine ⟨1323713075799968102019359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529901535466581605384957 1323713075799968102019359)
                      ·
                        rfl

theorem cell23_2577922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2577922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577922 prefixEnd_2577922 := by exact prefixLift 2577922
  have htrace : WordTrace (prefixWord ++ tailWord_2577922) baseStart_2577922 baseEnd_2577922 := by
    simpa [prefixWord, tailWord_2577922, baseEnd_2577922] using wordTrace_append hprefix tailTrace_2577922
  have hstable : (prefixWord ++ tailWord_2577922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577922).length < 2 ^ (prefixWord ++ tailWord_2577922).sum := by decide
  have hdescent : baseEnd_2577922 < baseStart_2577922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577926 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2577926 : Nat := 118140960795 + 2577926 * 2 ^ 59
def prefixEnd_2577926 : Nat := 4983230072969 + 3 ^ 40 * 2577926 * 2
def baseEnd_2577926 : Nat := 1323715129722586086369341

theorem tailTrace_2577926 : CollatzResearch.WordTrace tailWord_2577926 prefixEnd_2577926 1323715129722586086369341 := by
  unfold tailWord_2577926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938271426831932861057801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62683123772414567702566421 2938271426831932861057801)
  ·
    refine ⟨2203703570123949645793351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2938271426831932861057801 2203703570123949645793351)
    ·
      refine ⟨3305555355185924468690027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203703570123949645793351 3305555355185924468690027)
      ·
        refine ⟨4958333032778886703035041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305555355185924468690027 4958333032778886703035041)
        ·
          refine ⟨3718749774584165027276281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4958333032778886703035041 3718749774584165027276281)
          ·
            refine ⟨2789062330938123770457211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3718749774584165027276281 2789062330938123770457211)
            ·
              refine ⟨4183593496407185655685817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789062330938123770457211 4183593496407185655685817)
              ·
                refine ⟨3137695122305389241764363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183593496407185655685817 3137695122305389241764363)
                ·
                  refine ⟨4706542683458083862646545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137695122305389241764363 4706542683458083862646545)
                  ·
                    refine ⟨3529907012593562896984909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706542683458083862646545 3529907012593562896984909)
                    ·
                      refine ⟨1323715129722586086369341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3529907012593562896984909 1323715129722586086369341)
                      ·
                        rfl

theorem cell23_2577926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2577926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577926 prefixEnd_2577926 := by exact prefixLift 2577926
  have htrace : WordTrace (prefixWord ++ tailWord_2577926) baseStart_2577926 baseEnd_2577926 := by
    simpa [prefixWord, tailWord_2577926, baseEnd_2577926] using wordTrace_append hprefix tailTrace_2577926
  have hstable : (prefixWord ++ tailWord_2577926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577926).length < 2 ^ (prefixWord ++ tailWord_2577926).sum := by decide
  have hdescent : baseEnd_2577926 < baseStart_2577926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577932 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_2577932 : Nat := 118140960795 + 2577932 * 2 ^ 59
def prefixEnd_2577932 : Nat := 4983230072969 + 3 ^ 40 * 2577932 * 2
def baseEnd_2577932 : Nat := 1323718210606513062894313

theorem tailTrace_2577932 : CollatzResearch.WordTrace tailWord_2577932 prefixEnd_2577932 1323718210606513062894313 := by
  unfold tailWord_2577932
  simp only [CollatzResearch.WordTrace]
  refine ⟨47012452248300057289284025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62683269664400076385712033 47012452248300057289284025)
  ·
    refine ⟨35259339186225042966963019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47012452248300057289284025 35259339186225042966963019)
    ·
      refine ⟨52889008779337564450444529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35259339186225042966963019 52889008779337564450444529)
      ·
        refine ⟨39666756584503173337833397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52889008779337564450444529 39666756584503173337833397)
        ·
          refine ⟨3718758429797172500421881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39666756584503173337833397 3718758429797172500421881)
          ·
            refine ⟨2789068822347879375316411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3718758429797172500421881 2789068822347879375316411)
            ·
              refine ⟨4183603233521819062974617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789068822347879375316411 4183603233521819062974617)
              ·
                refine ⟨3137702425141364297230963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183603233521819062974617 3137702425141364297230963)
                ·
                  refine ⟨4706553637712046445846445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137702425141364297230963 4706553637712046445846445)
                  ·
                    refine ⟨1764957614142017417192417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4706553637712046445846445 1764957614142017417192417)
                    ·
                      refine ⟨1323718210606513062894313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764957614142017417192417 1323718210606513062894313)
                      ·
                        rfl

theorem cell23_2577932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_2577932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577932 prefixEnd_2577932 := by exact prefixLift 2577932
  have htrace : WordTrace (prefixWord ++ tailWord_2577932) baseStart_2577932 baseEnd_2577932 := by
    simpa [prefixWord, tailWord_2577932, baseEnd_2577932] using wordTrace_append hprefix tailTrace_2577932
  have hstable : (prefixWord ++ tailWord_2577932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577932).length < 2 ^ (prefixWord ++ tailWord_2577932).sum := by decide
  have hdescent : baseEnd_2577932 < baseStart_2577932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577962 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2577962 : Nat := 118140960795 + 2577962 * 2 ^ 59
def prefixEnd_2577962 : Nat := 4983230072969 + 3 ^ 40 * 2577962 * 2
def baseEnd_2577962 : Nat := 1323733615026147945519175

theorem tailTrace_2577962 : CollatzResearch.WordTrace tailWord_2577962 prefixEnd_2577962 1323733615026147945519175 := by
  unfold tailWord_2577962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506499671622857425540035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62683999124327619801440093 23506499671622857425540035)
  ·
    refine ⟨35259749507434286138310053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23506499671622857425540035 35259749507434286138310053)
    ·
      refine ⟨6611203032643928650933135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35259749507434286138310053 6611203032643928650933135)
      ·
        refine ⟨9916804548965892976399703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611203032643928650933135 9916804548965892976399703)
        ·
          refine ⟨14875206823448839464599555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916804548965892976399703 14875206823448839464599555)
          ·
            refine ⟨22312810235173259196899333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14875206823448839464599555 22312810235173259196899333)
            ·
              refine ⟨4183651919094986099418625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22312810235173259196899333 4183651919094986099418625)
              ·
                refine ⟨3137738939321239574563969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183651919094986099418625 3137738939321239574563969)
                ·
                  refine ⟨2353304204490929680922977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137738939321239574563969 2353304204490929680922977)
                  ·
                    refine ⟨1764978153368197260692233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2353304204490929680922977 1764978153368197260692233)
                    ·
                      refine ⟨1323733615026147945519175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1764978153368197260692233 1323733615026147945519175)
                      ·
                        rfl

theorem cell23_2577962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2577962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2577962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2577962 prefixEnd_2577962 := by exact prefixLift 2577962
  have htrace : WordTrace (prefixWord ++ tailWord_2577962) baseStart_2577962 baseEnd_2577962 := by
    simpa [prefixWord, tailWord_2577962, baseEnd_2577962] using wordTrace_append hprefix tailTrace_2577962
  have hstable : (prefixWord ++ tailWord_2577962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577962).length < 2 ^ (prefixWord ++ tailWord_2577962).sum := by decide
  have hdescent : baseEnd_2577962 < baseStart_2577962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
