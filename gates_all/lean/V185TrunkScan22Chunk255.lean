import V185TrunkScan22Chunk254

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2273328 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_2273328 : Nat := 118140960795 + 2273328 * 2 ^ 59
def prefixEnd_2273328 : Nat := 4983230072969 + 3 ^ 40 * 2273328 * 2
def baseEnd_2273328 : Nat := 259402210960974850543369

theorem tailTrace_2273328 : CollatzResearch.WordTrace tailWord_2273328 prefixEnd_2273328 259402210960974850543369 := by
  unfold tailWord_2273328
  simp only [CollatzResearch.WordTrace]
  refine ⟨41457541954064192178534319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55276722605418922904712425 41457541954064192178534319)
  ·
    refine ⟨62186312931096288267801479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41457541954064192178534319 62186312931096288267801479)
    ·
      refine ⟨93279469396644432401702219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62186312931096288267801479 93279469396644432401702219)
      ·
        refine ⟨139919204094966648602553329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93279469396644432401702219 139919204094966648602553329)
        ·
          refine ⟨104939403071224986451914997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139919204094966648602553329 104939403071224986451914997)
          ·
            refine ⟨9838069037927342479867031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104939403071224986451914997 9838069037927342479867031)
            ·
              refine ⟨14757103556891013719800547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838069037927342479867031 14757103556891013719800547)
              ·
                refine ⟨22135655335336520579700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14757103556891013719800547 22135655335336520579700821)
                ·
                  refine ⟨259402210960974850543369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22135655335336520579700821 259402210960974850543369)
                  ·
                    rfl

theorem cell22_2273328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_2273328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273328 prefixEnd_2273328 := by exact prefixLift 2273328
  have htrace : WordTrace (prefixWord ++ tailWord_2273328) baseStart_2273328 baseEnd_2273328 := by
    simpa [prefixWord, tailWord_2273328, baseEnd_2273328] using wordTrace_append hprefix tailTrace_2273328
  have hstable : (prefixWord ++ tailWord_2273328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273328).length < 2 ^ (prefixWord ++ tailWord_2273328).sum := by decide
  have hdescent : baseEnd_2273328 < baseStart_2273328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273330 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2273330 : Nat := 118140960795 + 2273330 * 2 ^ 59
def prefixEnd_2273330 : Nat := 4983230072969 + 3 ^ 40 * 2273330 * 2
def baseEnd_2273330 : Nat := 778207317523797213080101

theorem tailTrace_2273330 : CollatzResearch.WordTrace tailWord_2273330 prefixEnd_2273330 778207317523797213080101 := by
  unfold tailWord_2273330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20728789213530284674660361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55276771236080759132427629 20728789213530284674660361)
  ·
    refine ⟨15546591910147713505995271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20728789213530284674660361 15546591910147713505995271)
    ·
      refine ⟨23319887865221570258992907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546591910147713505995271 23319887865221570258992907)
      ·
        refine ⟨34979831797832355388489361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23319887865221570258992907 34979831797832355388489361)
        ·
          refine ⟨26234873848374266541367021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34979831797832355388489361 26234873848374266541367021)
          ·
            refine ⟨9838077693140349953012633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26234873848374266541367021 9838077693140349953012633)
            ·
              refine ⟨7378558269855262464759475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9838077693140349953012633 7378558269855262464759475)
              ·
                refine ⟨11067837404782893697139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378558269855262464759475 11067837404782893697139213)
                ·
                  refine ⟨4150439026793585136427205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11067837404782893697139213 4150439026793585136427205)
                  ·
                    refine ⟨778207317523797213080101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150439026793585136427205 778207317523797213080101)
                    ·
                      rfl

theorem cell22_2273330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2273330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273330 prefixEnd_2273330 := by exact prefixLift 2273330
  have htrace : WordTrace (prefixWord ++ tailWord_2273330) baseStart_2273330 baseEnd_2273330 := by
    simpa [prefixWord, tailWord_2273330, baseEnd_2273330] using wordTrace_append hprefix tailTrace_2273330
  have hstable : (prefixWord ++ tailWord_2273330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273330).length < 2 ^ (prefixWord ++ tailWord_2273330).sum := by decide
  have hdescent : baseEnd_2273330 < baseStart_2273330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273362 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_2273362 : Nat := 118140960795 + 2273362 * 2 ^ 59
def prefixEnd_2273362 : Nat := 4983230072969 + 3 ^ 40 * 2273362 * 2
def baseEnd_2273362 : Nat := 259406090592586598760001

theorem tailTrace_2273362 : CollatzResearch.WordTrace tailWord_2273362 prefixEnd_2273362 259406090592586598760001 := by
  unfold tailWord_2273362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20729080997501302040951585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55277549326670138775870893 20729080997501302040951585)
  ·
    refine ⟨15546810748125976530713689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20729080997501302040951585 15546810748125976530713689)
    ·
      refine ⟨11660108061094482398035267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15546810748125976530713689 11660108061094482398035267)
      ·
        refine ⟨17490162091641723597052901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660108061094482398035267 17490162091641723597052901)
        ·
          refine ⟨3279405392182823174447419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17490162091641723597052901 3279405392182823174447419)
          ·
            refine ⟨4919108088274234761671129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279405392182823174447419 4919108088274234761671129)
            ·
              refine ⟨3689331066205676071253347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4919108088274234761671129 3689331066205676071253347)
              ·
                refine ⟨5533996599308514106880021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3689331066205676071253347 5533996599308514106880021)
                ·
                  refine ⟨259406090592586598760001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5533996599308514106880021 259406090592586598760001)
                  ·
                    rfl

theorem cell22_2273362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_2273362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273362 prefixEnd_2273362 := by exact prefixLift 2273362
  have htrace : WordTrace (prefixWord ++ tailWord_2273362) baseStart_2273362 baseEnd_2273362 := by
    simpa [prefixWord, tailWord_2273362, baseEnd_2273362] using wordTrace_append hprefix tailTrace_2273362
  have hstable : (prefixWord ++ tailWord_2273362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273362).length < 2 ^ (prefixWord ++ tailWord_2273362).sum := by decide
  have hdescent : baseEnd_2273362 < baseStart_2273362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273390 : List Nat := [4, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2273390 : Nat := 118140960795 + 2273390 * 2 ^ 59
def prefixEnd_2273390 : Nat := 4983230072969 + 3 ^ 40 * 2273390 * 2
def baseEnd_2273390 : Nat := 86469761861108561842213

theorem tailTrace_2273390 : CollatzResearch.WordTrace tailWord_2273390 prefixEnd_2273390 86469761861108561842213 := by
  unfold tailWord_2273390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364668154237971118228203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55278230155935845963883749 10364668154237971118228203)
  ·
    refine ⟨15547002231356956677342305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10364668154237971118228203 15547002231356956677342305)
    ·
      refine ⟨11660251673517717508006729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15547002231356956677342305 11660251673517717508006729)
      ·
        refine ⟨8745188755138288131005047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11660251673517717508006729 8745188755138288131005047)
        ·
          refine ⟨13117783132707432196507571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745188755138288131005047 13117783132707432196507571)
          ·
            refine ⟨19676674699061148294761357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13117783132707432196507571 19676674699061148294761357)
            ·
              refine ⟨7378753012147930610535509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19676674699061148294761357 7378753012147930610535509)
              ·
                refine ⟨86469761861108561842213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7378753012147930610535509 86469761861108561842213)
                ·
                  rfl

theorem cell22_2273390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2273390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273390 prefixEnd_2273390 := by exact prefixLift 2273390
  have htrace : WordTrace (prefixWord ++ tailWord_2273390) baseStart_2273390 baseEnd_2273390 := by
    simpa [prefixWord, tailWord_2273390, baseEnd_2273390] using wordTrace_append hprefix tailTrace_2273390
  have hstable : (prefixWord ++ tailWord_2273390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273390).length < 2 ^ (prefixWord ++ tailWord_2273390).sum := by decide
  have hdescent : baseEnd_2273390 < baseStart_2273390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273403 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_2273403 : Nat := 118140960795 + 2273403 * 2 ^ 59
def prefixEnd_2273403 : Nat := 4983230072969 + 3 ^ 40 * 2273403 * 2
def baseEnd_2273403 : Nat := 778232306915649356004877

theorem tailTrace_2273403 : CollatzResearch.WordTrace tailWord_2273403 prefixEnd_2273403 778232306915649356004877 := by
  unfold tailWord_2273403
  simp only [CollatzResearch.WordTrace]
  refine ⟨82917819382856672166048863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55278546255237781444032575 82917819382856672166048863)
  ·
    refine ⟨124376729074285008249073295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82917819382856672166048863 124376729074285008249073295)
    ·
      refine ⟨186565093611427512373609943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124376729074285008249073295 186565093611427512373609943)
      ·
        refine ⟨279847640417141268560414915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186565093611427512373609943 279847640417141268560414915)
        ·
          refine ⟨419771460625711902840622373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279847640417141268560414915 419771460625711902840622373)
          ·
            refine ⟨78707148867320981782616695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 419771460625711902840622373 78707148867320981782616695)
            ·
              refine ⟨118060723300981472673925043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78707148867320981782616695 118060723300981472673925043)
              ·
                refine ⟨177091084951472209010887565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118060723300981472673925043 177091084951472209010887565)
                ·
                  refine ⟨66409156856802078379082837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177091084951472209010887565 66409156856802078379082837)
                  ·
                    refine ⟨778232306915649356004877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66409156856802078379082837 778232306915649356004877)
                    ·
                      rfl

theorem cell22_2273403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_2273403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273403 prefixEnd_2273403 := by exact prefixLift 2273403
  have htrace : WordTrace (prefixWord ++ tailWord_2273403) baseStart_2273403 baseEnd_2273403 := by
    simpa [prefixWord, tailWord_2273403, baseEnd_2273403] using wordTrace_append hprefix tailTrace_2273403
  have hstable : (prefixWord ++ tailWord_2273403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273403).length < 2 ^ (prefixWord ++ tailWord_2273403).sum := by decide
  have hdescent : baseEnd_2273403 < baseStart_2273403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273473 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2273473 : Nat := 118140960795 + 2273473 * 2 ^ 59
def prefixEnd_2273473 : Nat := 4983230072969 + 3 ^ 40 * 2273473 * 2
def baseEnd_2273473 : Nat := 778256269346192506754663

theorem tailTrace_2273473 : CollatzResearch.WordTrace tailWord_2273473 prefixEnd_2273473 778256269346192506754663 := by
  unfold tailWord_2273473
  simp only [CollatzResearch.WordTrace]
  refine ⟨82920372492603074121097073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55280248328402049414064715 82920372492603074121097073)
  ·
    refine ⟨62190279369452305590822805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82920372492603074121097073 62190279369452305590822805)
    ·
      refine ⟨2915169345443076824569819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62190279369452305590822805 2915169345443076824569819)
      ·
        refine ⟨4372754018164615236854729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915169345443076824569819 4372754018164615236854729)
        ·
          refine ⟨3279565513623461427641047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372754018164615236854729 3279565513623461427641047)
          ·
            refine ⟨4919348270435192141461571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279565513623461427641047 4919348270435192141461571)
            ·
              refine ⟨7379022405652788212192357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919348270435192141461571 7379022405652788212192357)
              ·
                refine ⟨1383566701059897789786067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7379022405652788212192357 1383566701059897789786067)
                ·
                  refine ⟨2075350051589846684679101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383566701059897789786067 2075350051589846684679101)
                  ·
                    refine ⟨778256269346192506754663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075350051589846684679101 778256269346192506754663)
                    ·
                      rfl

theorem cell22_2273473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2273473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273473 prefixEnd_2273473 := by exact prefixLift 2273473
  have htrace : WordTrace (prefixWord ++ tailWord_2273473) baseStart_2273473 baseEnd_2273473 := by
    simpa [prefixWord, tailWord_2273473, baseEnd_2273473] using wordTrace_append hprefix tailTrace_2273473
  have hstable : (prefixWord ++ tailWord_2273473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273473).length < 2 ^ (prefixWord ++ tailWord_2273473).sum := by decide
  have hdescent : baseEnd_2273473 < baseStart_2273473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273480 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_2273480 : Nat := 118140960795 + 2273480 * 2 ^ 59
def prefixEnd_2273480 : Nat := 4983230072969 + 3 ^ 40 * 2273480 * 2
def baseEnd_2273480 : Nat := 259419555196415607276547

theorem tailTrace_2273480 : CollatzResearch.WordTrace tailWord_2273480 prefixEnd_2273480 259419555196415607276547 := by
  unfold tailWord_2273480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41460313901788857158300947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55280418535718476211067929 41460313901788857158300947)
  ·
    refine ⟨62190470852683285737451421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41460313901788857158300947 62190470852683285737451421)
    ·
      refine ⟨23321426569756232151544283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62190470852683285737451421 23321426569756232151544283)
      ·
        refine ⟨34982139854634348227316425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23321426569756232151544283 34982139854634348227316425)
        ·
          refine ⟨26236604890975761170487319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34982139854634348227316425 26236604890975761170487319)
          ·
            refine ⟨39354907336463641755730979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26236604890975761170487319 39354907336463641755730979)
            ·
              refine ⟨59032361004695462633596469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39354907336463641755730979 59032361004695462633596469)
              ·
                refine ⟨5534283844190199621899669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59032361004695462633596469 5534283844190199621899669)
                ·
                  refine ⟨259419555196415607276547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5534283844190199621899669 259419555196415607276547)
                  ·
                    rfl

theorem cell22_2273480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_2273480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273480 prefixEnd_2273480 := by exact prefixLift 2273480
  have htrace : WordTrace (prefixWord ++ tailWord_2273480) baseStart_2273480 baseEnd_2273480 := by
    simpa [prefixWord, tailWord_2273480, baseEnd_2273480] using wordTrace_append hprefix tailTrace_2273480
  have hstable : (prefixWord ++ tailWord_2273480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273480).length < 2 ^ (prefixWord ++ tailWord_2273480).sum := by decide
  have hdescent : baseEnd_2273480 < baseStart_2273480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273484 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_2273484 : Nat := 118140960795 + 2273484 * 2 ^ 59
def prefixEnd_2273484 : Nat := 4983230072969 + 3 ^ 40 * 2273484 * 2
def baseEnd_2273484 : Nat := 778260034870992144729629

theorem tailTrace_2273484 : CollatzResearch.WordTrace tailWord_2273484 prefixEnd_2273484 778260034870992144729629 := by
  unfold tailWord_2273484
  simp only [CollatzResearch.WordTrace]
  refine ⟨41460386847781611499873753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55280515797042148666498337 41460386847781611499873753)
  ·
    refine ⟨31095290135836208624905315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41460386847781611499873753 31095290135836208624905315)
    ·
      refine ⟨46642935203754312937357973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31095290135836208624905315 46642935203754312937357973)
      ·
        refine ⟨2186387587675983418938655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46642935203754312937357973 2186387587675983418938655)
        ·
          refine ⟨3279581381513975128407983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186387587675983418938655 3279581381513975128407983)
          ·
            refine ⟨4919372072270962692611975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279581381513975128407983 4919372072270962692611975)
            ·
              refine ⟨7379058108406444038917963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919372072270962692611975 7379058108406444038917963)
              ·
                refine ⟨11068587162609666058376945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379058108406444038917963 11068587162609666058376945)
                ·
                  refine ⟨8301440371957249543782709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068587162609666058376945 8301440371957249543782709)
                  ·
                    refine ⟨778260034870992144729629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8301440371957249543782709 778260034870992144729629)
                    ·
                      rfl

theorem cell22_2273484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_2273484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273484 prefixEnd_2273484 := by exact prefixLift 2273484
  have htrace : WordTrace (prefixWord ++ tailWord_2273484) baseStart_2273484 baseEnd_2273484 := by
    simpa [prefixWord, tailWord_2273484, baseEnd_2273484] using wordTrace_append hprefix tailTrace_2273484
  have hstable : (prefixWord ++ tailWord_2273484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273484).length < 2 ^ (prefixWord ++ tailWord_2273484).sum := by decide
  have hdescent : baseEnd_2273484 < baseStart_2273484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273512 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2273512 : Nat := 118140960795 + 2273512 * 2 ^ 59
def prefixEnd_2273512 : Nat := 4983230072969 + 3 ^ 40 * 2273512 * 2
def baseEnd_2273512 : Nat := 778269619843209405029543

theorem tailTrace_2273512 : CollatzResearch.WordTrace tailWord_2273512 prefixEnd_2273512 778269619843209405029543 := by
  unfold tailWord_2273512
  simp only [CollatzResearch.WordTrace]
  refine ⟨41460897469730891890883395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55281196626307855854511193 41460897469730891890883395)
  ·
    refine ⟨62191346204596337836325093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41460897469730891890883395 62191346204596337836325093)
    ·
      refine ⟨11660877413361813344310955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62191346204596337836325093 11660877413361813344310955)
      ·
        refine ⟨17491316120042720016466433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660877413361813344310955 17491316120042720016466433)
        ·
          refine ⟨13118487090032040012349825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17491316120042720016466433 13118487090032040012349825)
          ·
            refine ⟨9838865317524030009262369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13118487090032040012349825 9838865317524030009262369)
            ·
              refine ⟨7379148988143022506946777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9838865317524030009262369 7379148988143022506946777)
              ·
                refine ⟨5534361741107266880210083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7379148988143022506946777 5534361741107266880210083)
                ·
                  refine ⟨8301542611660900320315125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5534361741107266880210083 8301542611660900320315125)
                  ·
                    refine ⟨778269619843209405029543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8301542611660900320315125 778269619843209405029543)
                    ·
                      rfl

theorem cell22_2273512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2273512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273512 prefixEnd_2273512 := by exact prefixLift 2273512
  have htrace : WordTrace (prefixWord ++ tailWord_2273512) baseStart_2273512 baseEnd_2273512 := by
    simpa [prefixWord, tailWord_2273512, baseEnd_2273512] using wordTrace_append hprefix tailTrace_2273512
  have hstable : (prefixWord ++ tailWord_2273512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273512).length < 2 ^ (prefixWord ++ tailWord_2273512).sum := by decide
  have hdescent : baseEnd_2273512 < baseStart_2273512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273514 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_2273514 : Nat := 118140960795 + 2273514 * 2 ^ 59
def prefixEnd_2273514 : Nat := 4983230072969 + 3 ^ 40 * 2273514 * 2
def baseEnd_2273514 : Nat := 259423434828027355493179

theorem tailTrace_2273514 : CollatzResearch.WordTrace tailWord_2273514 prefixEnd_2273514 259423434828027355493179 := by
  unfold tailWord_2273514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730466971363634530834899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55281245256969692082226397 20730466971363634530834899)
  ·
    refine ⟨31095700457045451796252349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20730466971363634530834899 31095700457045451796252349)
    ·
      refine ⟨11660887671392044423594631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31095700457045451796252349 11660887671392044423594631)
      ·
        refine ⟨17491331507088066635391947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660887671392044423594631 17491331507088066635391947)
        ·
          refine ⟨26236997260632099953087921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17491331507088066635391947 26236997260632099953087921)
          ·
            refine ⟨19677747945474074964815941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26236997260632099953087921 19677747945474074964815941)
            ·
              refine ⟨3689577739776389055902989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19677747945474074964815941 3689577739776389055902989)
              ·
                refine ⟨1383591652416145895963621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689577739776389055902989 1383591652416145895963621)
                ·
                  refine ⟨259423434828027355493179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383591652416145895963621 259423434828027355493179)
                  ·
                    rfl

theorem cell22_2273514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_2273514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273514 prefixEnd_2273514 := by exact prefixLift 2273514
  have htrace : WordTrace (prefixWord ++ tailWord_2273514) baseStart_2273514 baseEnd_2273514 := by
    simpa [prefixWord, tailWord_2273514, baseEnd_2273514] using wordTrace_append hprefix tailTrace_2273514
  have hstable : (prefixWord ++ tailWord_2273514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273514).length < 2 ^ (prefixWord ++ tailWord_2273514).sum := by decide
  have hdescent : baseEnd_2273514 < baseStart_2273514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273555 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_2273555 : Nat := 118140960795 + 2273555 * 2 ^ 59
def prefixEnd_2273555 : Nat := 4983230072969 + 3 ^ 40 * 2273555 * 2
def baseEnd_2273555 : Nat := 778284339621971626204411

theorem tailTrace_2273555 : CollatzResearch.WordTrace tailWord_2273555 prefixEnd_2273555 778284339621971626204411 := by
  unfold tailWord_2273555
  simp only [CollatzResearch.WordTrace]
  refine ⟨82923363278306002125582119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55282242185537334750388079 82923363278306002125582119)
  ·
    refine ⟨124385044917459003188373179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82923363278306002125582119 124385044917459003188373179)
    ·
      refine ⟨186577567376188504782559769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124385044917459003188373179 186577567376188504782559769)
      ·
        refine ⟨139933175532141378586919827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186577567376188504782559769 139933175532141378586919827)
        ·
          refine ⟨209899763298212067880379741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139933175532141378586919827 209899763298212067880379741)
          ·
            refine ⟨78712411236829525455142403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209899763298212067880379741 78712411236829525455142403)
            ·
              refine ⟨118068616855244288182713605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78712411236829525455142403 118068616855244288182713605)
              ·
                refine ⟨22137865660358304034258801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118068616855244288182713605 22137865660358304034258801)
                ·
                  refine ⟨16603399245268728025694101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22137865660358304034258801 16603399245268728025694101)
                  ·
                    refine ⟨778284339621971626204411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16603399245268728025694101 778284339621971626204411)
                    ·
                      rfl

theorem cell22_2273555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_2273555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273555 prefixEnd_2273555 := by exact prefixLift 2273555
  have htrace : WordTrace (prefixWord ++ tailWord_2273555) baseStart_2273555 baseEnd_2273555 := by
    simpa [prefixWord, tailWord_2273555, baseEnd_2273555] using wordTrace_append hprefix tailTrace_2273555
  have hstable : (prefixWord ++ tailWord_2273555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273555).length < 2 ^ (prefixWord ++ tailWord_2273555).sum := by decide
  have hdescent : baseEnd_2273555 < baseStart_2273555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273559 : List Nat := [1, 1, 3, 4, 1, 4, 2, 6]
def baseStart_2273559 : Nat := 118140960795 + 2273559 * 2 ^ 59
def prefixEnd_2273559 : Nat := 4983230072969 + 3 ^ 40 * 2273559 * 2
def baseEnd_2273559 : Nat := 86476189878190772122711

theorem tailTrace_2273559 : CollatzResearch.WordTrace tailWord_2273559 prefixEnd_2273559 86476189878190772122711 := by
  unfold tailWord_2273559
  simp only [CollatzResearch.WordTrace]
  refine ⟨82923509170291510808727731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55282339446861007205818487 82923509170291510808727731)
  ·
    refine ⟨124385263755437266213091597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82923509170291510808727731 124385263755437266213091597)
    ·
      refine ⟨46644473908288974829909349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124385263755437266213091597 46644473908288974829909349)
      ·
        refine ⟨8745838857804182780608003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46644473908288974829909349 8745838857804182780608003)
        ·
          refine ⟨13118758286706274170912005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745838857804182780608003 13118758286706274170912005)
          ·
            refine ⟨2459767178757426407046001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13118758286706274170912005 2459767178757426407046001)
            ·
              refine ⟨1844825384068069805284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459767178757426407046001 1844825384068069805284501)
              ·
                refine ⟨86476189878190772122711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1844825384068069805284501 86476189878190772122711)
                ·
                  rfl

theorem cell22_2273559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 6].length) (baseStart_2273559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273559 prefixEnd_2273559 := by exact prefixLift 2273559
  have htrace : WordTrace (prefixWord ++ tailWord_2273559) baseStart_2273559 baseEnd_2273559 := by
    simpa [prefixWord, tailWord_2273559, baseEnd_2273559] using wordTrace_append hprefix tailTrace_2273559
  have hstable : (prefixWord ++ tailWord_2273559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273559).length < 2 ^ (prefixWord ++ tailWord_2273559).sum := by decide
  have hdescent : baseEnd_2273559 < baseStart_2273559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273587 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 5]
def baseStart_2273587 : Nat := 118140960795 + 2273587 * 2 ^ 59
def prefixEnd_2273587 : Nat := 4983230072969 + 3 ^ 40 * 2273587 * 2
def baseEnd_2273587 : Nat := 259431764625311403134771

theorem tailTrace_2273587 : CollatzResearch.WordTrace tailWord_2273587 prefixEnd_2273587 259431764625311403134771 := by
  unfold tailWord_2273587
  simp only [CollatzResearch.WordTrace]
  refine ⟨82924530414190071590747015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55283020276126714393831343 82924530414190071590747015)
  ·
    refine ⟨124386795621285107386120523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82924530414190071590747015 124386795621285107386120523)
    ·
      refine ⟨186580193431927661079180785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124386795621285107386120523 186580193431927661079180785)
      ·
        refine ⟨139935145073945745809385589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186580193431927661079180785 139935145073945745809385589)
        ·
          refine ⟨13118919850682413669629899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139935145073945745809385589 13118919850682413669629899)
          ·
            refine ⟨19678379776023620504444849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13118919850682413669629899 19678379776023620504444849)
            ·
              refine ⟨14758784832017715378333637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19678379776023620504444849 14758784832017715378333637)
              ·
                refine ⟨2767272156003321633437557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14758784832017715378333637 2767272156003321633437557)
                ·
                  refine ⟨259431764625311403134771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767272156003321633437557 259431764625311403134771)
                  ·
                    rfl

theorem cell22_2273587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].length) (baseStart_2273587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273587 prefixEnd_2273587 := by exact prefixLift 2273587
  have htrace : WordTrace (prefixWord ++ tailWord_2273587) baseStart_2273587 baseEnd_2273587 := by
    simpa [prefixWord, tailWord_2273587, baseEnd_2273587] using wordTrace_append hprefix tailTrace_2273587
  have hstable : (prefixWord ++ tailWord_2273587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273587).length < 2 ^ (prefixWord ++ tailWord_2273587).sum := by decide
  have hdescent : baseEnd_2273587 < baseStart_2273587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273726 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2273726 : Nat := 118140960795 + 2273726 * 2 ^ 59
def prefixEnd_2273726 : Nat := 4983230072969 + 3 ^ 40 * 2273726 * 2
def baseEnd_2273726 : Nat := 778342876416584180178887

theorem tailTrace_2273726 : CollatzResearch.WordTrace tailWord_2273726 prefixEnd_2273726 778342876416584180178887 := by
  unfold tailWord_2273726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366200020085812291257129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55286400107124332220038021 10366200020085812291257129)
  ·
    refine ⟨7774650015064359218442847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366200020085812291257129 7774650015064359218442847)
    ·
      refine ⟨11661975022596538827664271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774650015064359218442847 11661975022596538827664271)
      ·
        refine ⟨17492962533894808241496407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661975022596538827664271 17492962533894808241496407)
        ·
          refine ⟨26239443800842212362244611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17492962533894808241496407 26239443800842212362244611)
          ·
            refine ⟨39359165701263318543366917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26239443800842212362244611 39359165701263318543366917)
            ·
              refine ⟨7379843568986872226881297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39359165701263318543366917 7379843568986872226881297)
              ·
                refine ⟨5534882676740154170160973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7379843568986872226881297 5534882676740154170160973)
                ·
                  refine ⟨2075581003777557813810365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5534882676740154170160973 2075581003777557813810365)
                  ·
                    refine ⟨778342876416584180178887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075581003777557813810365 778342876416584180178887)
                    ·
                      rfl

theorem cell22_2273726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2273726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273726 prefixEnd_2273726 := by exact prefixLift 2273726
  have htrace : WordTrace (prefixWord ++ tailWord_2273726) baseStart_2273726 baseEnd_2273726 := by
    simpa [prefixWord, tailWord_2273726, baseEnd_2273726] using wordTrace_append hprefix tailTrace_2273726
  have hstable : (prefixWord ++ tailWord_2273726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273726).length < 2 ^ (prefixWord ++ tailWord_2273726).sum := by decide
  have hdescent : baseEnd_2273726 < baseStart_2273726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273737 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_2273737 : Nat := 118140960795 + 2273737 * 2 ^ 59
def prefixEnd_2273737 : Nat := 4983230072969 + 3 ^ 40 * 2273737 * 2
def baseEnd_2273737 : Nat := 778346641941383818153853

theorem tailTrace_2273737 : CollatzResearch.WordTrace tailWord_2273737 prefixEnd_2273737 778346641941383818153853 := by
  unfold tailWord_2273737
  simp only [CollatzResearch.WordTrace]
  refine ⟨82930001363646647208707465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55286667575764431472471643 82930001363646647208707465)
  ·
    refine ⟨62197501022734985406530599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82930001363646647208707465 62197501022734985406530599)
    ·
      refine ⟨93296251534102478109795899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62197501022734985406530599 93296251534102478109795899)
      ·
        refine ⟨139944377301153717164693849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93296251534102478109795899 139944377301153717164693849)
        ·
          refine ⟨104958282975865287873520387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139944377301153717164693849 104958282975865287873520387)
          ·
            refine ⟨157437424463797931810280581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104958282975865287873520387 157437424463797931810280581)
            ·
              refine ⟨29519517086962112214427609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157437424463797931810280581 29519517086962112214427609)
              ·
                refine ⟨22139637815221584160820707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29519517086962112214427609 22139637815221584160820707)
                ·
                  refine ⟨33209456722832376241231061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22139637815221584160820707 33209456722832376241231061)
                  ·
                    refine ⟨778346641941383818153853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33209456722832376241231061 778346641941383818153853)
                    ·
                      rfl

theorem cell22_2273737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_2273737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273737 prefixEnd_2273737 := by exact prefixLift 2273737
  have htrace : WordTrace (prefixWord ++ tailWord_2273737) baseStart_2273737 baseEnd_2273737 := by
    simpa [prefixWord, tailWord_2273737, baseEnd_2273737] using wordTrace_append hprefix tailTrace_2273737
  have hstable : (prefixWord ++ tailWord_2273737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273737).length < 2 ^ (prefixWord ++ tailWord_2273737).sum := by decide
  have hdescent : baseEnd_2273737 < baseStart_2273737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273773 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2273773 : Nat := 118140960795 + 2273773 * 2 ^ 59
def prefixEnd_2273773 : Nat := 4983230072969 + 3 ^ 40 * 2273773 * 2
def baseEnd_2273773 : Nat := 259452988492363908084581

theorem tailTrace_2273773 : CollatzResearch.WordTrace tailWord_2273773 prefixEnd_2273773 259452988492363908084581 := by
  unfold tailWord_2273773
  simp only [CollatzResearch.WordTrace]
  refine ⟨82931314391516225357017973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55287542927677483571345315 82931314391516225357017973)
  ·
    refine ⟨7774810724204646127220435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82931314391516225357017973 7774810724204646127220435)
    ·
      refine ⟨11662216086306969190830653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774810724204646127220435 11662216086306969190830653)
      ·
        refine ⟨4373331032365113446561495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11662216086306969190830653 4373331032365113446561495)
        ·
          refine ⟨6559996548547670169842243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373331032365113446561495 6559996548547670169842243)
          ·
            refine ⟨9839994822821505254763365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559996548547670169842243 9839994822821505254763365)
            ·
              refine ⟨1844999029279032235268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9839994822821505254763365 1844999029279032235268131)
              ·
                refine ⟨2767498543918548352902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844999029279032235268131 2767498543918548352902197)
                ·
                  refine ⟨259452988492363908084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767498543918548352902197 259452988492363908084581)
                  ·
                    rfl

theorem cell22_2273773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2273773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273773 prefixEnd_2273773 := by exact prefixLift 2273773
  have htrace : WordTrace (prefixWord ++ tailWord_2273773) baseStart_2273773 baseEnd_2273773 := by
    simpa [prefixWord, tailWord_2273773, baseEnd_2273773] using wordTrace_append hprefix tailTrace_2273773
  have hstable : (prefixWord ++ tailWord_2273773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273773).length < 2 ^ (prefixWord ++ tailWord_2273773).sum := by decide
  have hdescent : baseEnd_2273773 < baseStart_2273773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273803 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 1, 4]
def baseStart_2273803 : Nat := 118140960795 + 2273803 * 2 ^ 59
def prefixEnd_2273803 : Nat := 4983230072969 + 3 ^ 40 * 2273803 * 2
def baseEnd_2273803 : Nat := 778369235090181646003651

theorem tailTrace_2273803 : CollatzResearch.WordTrace tailWord_2273803 prefixEnd_2273803 778369235090181646003651 := by
  unfold tailWord_2273803
  simp only [CollatzResearch.WordTrace]
  refine ⟨82932408581407540480610063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55288272387605026987073375 82932408581407540480610063)
  ·
    refine ⟨124398612872111310720915095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82932408581407540480610063 124398612872111310720915095)
    ·
      refine ⟨186597919308166966081372643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124398612872111310720915095 186597919308166966081372643)
      ·
        refine ⟨279896878962250449122058965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186597919308166966081372643 279896878962250449122058965)
        ·
          refine ⟨6560083100677744901298257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 279896878962250449122058965 6560083100677744901298257)
          ·
            refine ⟨4920062325508308675973693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6560083100677744901298257 4920062325508308675973693)
            ·
              refine ⟨1845023372065615753490135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4920062325508308675973693 1845023372065615753490135)
              ·
                refine ⟨2767535058098423630235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845023372065615753490135 2767535058098423630235203)
                ·
                  refine ⟨4151302587147635445352805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767535058098423630235203 4151302587147635445352805)
                  ·
                    refine ⟨778369235090181646003651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151302587147635445352805 778369235090181646003651)
                    ·
                      rfl

theorem cell22_2273803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 4].length) (baseStart_2273803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273803 prefixEnd_2273803 := by exact prefixLift 2273803
  have htrace : WordTrace (prefixWord ++ tailWord_2273803) baseStart_2273803 baseEnd_2273803 := by
    simpa [prefixWord, tailWord_2273803, baseEnd_2273803] using wordTrace_append hprefix tailTrace_2273803
  have hstable : (prefixWord ++ tailWord_2273803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273803).length < 2 ^ (prefixWord ++ tailWord_2273803).sum := by decide
  have hdescent : baseEnd_2273803 < baseStart_2273803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273818 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_2273818 : Nat := 118140960795 + 2273818 * 2 ^ 59
def prefixEnd_2273818 : Nat := 4983230072969 + 3 ^ 40 * 2273818 * 2
def baseEnd_2273818 : Nat := 259458123298908868959535

theorem tailTrace_2273818 : CollatzResearch.WordTrace tailWord_2273818 prefixEnd_2273818 259458123298908868959535 := by
  unfold tailWord_2273818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20733238919088299510601527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55288637117568798694937405 20733238919088299510601527)
  ·
    refine ⟨31099858378632449265902291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20733238919088299510601527 31099858378632449265902291)
    ·
      refine ⟨46649787567948673898853437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31099858378632449265902291 46649787567948673898853437)
      ·
        refine ⟨17493670337980752712070039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46649787567948673898853437 17493670337980752712070039)
        ·
          refine ⟨26240505506971129068105059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17493670337980752712070039 26240505506971129068105059)
          ·
            refine ⟨39360758260456693602157589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240505506971129068105059 39360758260456693602157589)
            ·
              refine ⟨1845035543458907512601137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39360758260456693602157589 1845035543458907512601137)
              ·
                refine ⟨1383776657594180634450853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1845035543458907512601137 1383776657594180634450853)
                ·
                  refine ⟨259458123298908868959535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383776657594180634450853 259458123298908868959535)
                  ·
                    rfl

theorem cell22_2273818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_2273818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273818 prefixEnd_2273818 := by exact prefixLift 2273818
  have htrace : WordTrace (prefixWord ++ tailWord_2273818) baseStart_2273818 baseEnd_2273818 := by
    simpa [prefixWord, tailWord_2273818, baseEnd_2273818] using wordTrace_append hprefix tailTrace_2273818
  have hstable : (prefixWord ++ tailWord_2273818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273818).length < 2 ^ (prefixWord ++ tailWord_2273818).sum := by decide
  have hdescent : baseEnd_2273818 < baseStart_2273818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273829 : List Nat := [1, 3, 1, 2, 2, 1, 5, 7]
def baseStart_2273829 : Nat := 118140960795 + 2273829 * 2 ^ 59
def prefixEnd_2273829 : Nat := 4983230072969 + 3 ^ 40 * 2273829 * 2
def baseEnd_2273829 : Nat := 86486459491280693872619

theorem tailTrace_2273829 : CollatzResearch.WordTrace tailWord_2273829 prefixEnd_2273829 86486459491280693872619 := by
  unfold tailWord_2273829
  simp only [CollatzResearch.WordTrace]
  refine ⟨82933356879313346921056541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55288904586208897947371027 82933356879313346921056541)
  ·
    refine ⟨31100008829742505095396203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82933356879313346921056541 31100008829742505095396203)
    ·
      refine ⟨46650013244613757643094305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31100008829742505095396203 46650013244613757643094305)
      ·
        refine ⟨34987509933460318232320729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46650013244613757643094305 34987509933460318232320729)
        ·
          refine ⟨26240632450095238674240547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34987509933460318232320729 26240632450095238674240547)
          ·
            refine ⟨39360948675142858011360821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240632450095238674240547 39360948675142858011360821)
            ·
              refine ⟨3690088938294642938565077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39360948675142858011360821 3690088938294642938565077)
              ·
                refine ⟨86486459491280693872619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3690088938294642938565077 86486459491280693872619)
                ·
                  rfl

theorem cell22_2273829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 7].length) (baseStart_2273829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273829 prefixEnd_2273829 := by exact prefixLift 2273829
  have htrace : WordTrace (prefixWord ++ tailWord_2273829) baseStart_2273829 baseEnd_2273829 := by
    simpa [prefixWord, tailWord_2273829, baseEnd_2273829] using wordTrace_append hprefix tailTrace_2273829
  have hstable : (prefixWord ++ tailWord_2273829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273829).length < 2 ^ (prefixWord ++ tailWord_2273829).sum := by decide
  have hdescent : baseEnd_2273829 < baseStart_2273829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273854 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2273854 : Nat := 118140960795 + 2273854 * 2 ^ 59
def prefixEnd_2273854 : Nat := 4983230072969 + 3 ^ 40 * 2273854 * 2
def baseEnd_2273854 : Nat := 778386693432434512978495

theorem tailTrace_2273854 : CollatzResearch.WordTrace tailWord_2273854 prefixEnd_2273854 778386693432434512978495 := by
  unfold tailWord_2273854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366783588027847023839577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55289512469481850793811077 10366783588027847023839577)
  ·
    refine ⟨7775087691020885267879683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366783588027847023839577 7775087691020885267879683)
    ·
      refine ⟨11662631536531327901819525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775087691020885267879683 11662631536531327901819525)
      ·
        refine ⟨2186743413099623981591161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11662631536531327901819525 2186743413099623981591161)
        ·
          refine ⟨1640057559824717986193371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186743413099623981591161 1640057559824717986193371)
          ·
            refine ⟨2460086339737076979290057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640057559824717986193371 2460086339737076979290057)
            ·
              refine ⟨1845064754802807734467543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460086339737076979290057 1845064754802807734467543)
              ·
                refine ⟨2767597132204211601701315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845064754802807734467543 2767597132204211601701315)
                ·
                  refine ⟨4151395698306317402551973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767597132204211601701315 4151395698306317402551973)
                  ·
                    refine ⟨778386693432434512978495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151395698306317402551973 778386693432434512978495)
                    ·
                      rfl

theorem cell22_2273854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2273854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273854 prefixEnd_2273854 := by exact prefixLift 2273854
  have htrace : WordTrace (prefixWord ++ tailWord_2273854) baseStart_2273854 baseEnd_2273854 := by
    simpa [prefixWord, tailWord_2273854, baseEnd_2273854] using wordTrace_append hprefix tailTrace_2273854
  have hstable : (prefixWord ++ tailWord_2273854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273854).length < 2 ^ (prefixWord ++ tailWord_2273854).sum := by decide
  have hdescent : baseEnd_2273854 < baseStart_2273854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273998 : List Nat := [4, 1, 1, 1, 3, 4, 1, 7]
def baseStart_2273998 : Nat := 118140960795 + 2273998 * 2 ^ 59
def prefixEnd_2273998 : Nat := 4983230072969 + 3 ^ 40 * 2273998 * 2
def baseEnd_2273998 : Nat := 86492887508362904153117

theorem tailTrace_2273998 : CollatzResearch.WordTrace tailWord_2273998 prefixEnd_2273998 86492887508362904153117 := by
  unfold tailWord_2273998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367440101962636097994831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55293013877134059189305765 10367440101962636097994831)
  ·
    refine ⟨15551160152943954146992247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10367440101962636097994831 15551160152943954146992247)
    ·
      refine ⟨23326740229415931220488371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15551160152943954146992247 23326740229415931220488371)
      ·
        refine ⟨34990110344123896830732557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23326740229415931220488371 34990110344123896830732557)
        ·
          refine ⟨13121291379046461311524709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34990110344123896830732557 13121291379046461311524709)
          ·
            refine ⟨2460242133571211495910883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13121291379046461311524709 2460242133571211495910883)
            ·
              refine ⟨3690363200356817243866325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460242133571211495910883 3690363200356817243866325)
              ·
                refine ⟨86492887508362904153117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3690363200356817243866325 86492887508362904153117)
                ·
                  rfl

theorem cell22_2273998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_2273998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273998 prefixEnd_2273998 := by exact prefixLift 2273998
  have htrace : WordTrace (prefixWord ++ tailWord_2273998) baseStart_2273998 baseEnd_2273998 := by
    simpa [prefixWord, tailWord_2273998, baseEnd_2273998] using wordTrace_append hprefix tailTrace_2273998
  have hstable : (prefixWord ++ tailWord_2273998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273998).length < 2 ^ (prefixWord ++ tailWord_2273998).sum := by decide
  have hdescent : baseEnd_2273998 < baseStart_2273998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274026 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_2274026 : Nat := 118140960795 + 2274026 * 2 ^ 59
def prefixEnd_2274026 : Nat := 4983230072969 + 3 ^ 40 * 2274026 * 2
def baseEnd_2274026 : Nat := 259481857515827799225989

theorem tailTrace_2274026 : CollatzResearch.WordTrace tailWord_2274026 prefixEnd_2274026 259481857515827799225989 := by
  unfold tailWord_2274026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735135514899912391494483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55293694706399766377318621 20735135514899912391494483)
  ·
    refine ⟨31102703272349868587241725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20735135514899912391494483 31102703272349868587241725)
    ·
      refine ⟨11663513727131200720215647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31102703272349868587241725 11663513727131200720215647)
      ·
        refine ⟨17495270590696801080323471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663513727131200720215647 17495270590696801080323471)
        ·
          refine ⟨26242905886045201620485207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17495270590696801080323471 26242905886045201620485207)
          ·
            refine ⟨39364358829067802430727811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26242905886045201620485207 39364358829067802430727811)
            ·
              refine ⟨59046538243601703646091717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39364358829067802430727811 59046538243601703646091717)
              ·
                refine ⟨11071225920675319433642197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59046538243601703646091717 11071225920675319433642197)
                ·
                  refine ⟨259481857515827799225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11071225920675319433642197 259481857515827799225989)
                  ·
                    rfl

theorem cell22_2274026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_2274026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274026 prefixEnd_2274026 := by exact prefixLift 2274026
  have htrace : WordTrace (prefixWord ++ tailWord_2274026) baseStart_2274026 baseEnd_2274026 := by
    simpa [prefixWord, tailWord_2274026, baseEnd_2274026] using wordTrace_append hprefix tailTrace_2274026
  have hstable : (prefixWord ++ tailWord_2274026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274026).length < 2 ^ (prefixWord ++ tailWord_2274026).sum := by decide
  have hdescent : baseEnd_2274026 < baseStart_2274026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274036 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2274036 : Nat := 118140960795 + 2274036 * 2 ^ 59
def prefixEnd_2274036 : Nat := 4983230072969 + 3 ^ 40 * 2274036 * 2
def baseEnd_2274036 : Nat := 778448995751846704927937

theorem tailTrace_2274036 : CollatzResearch.WordTrace tailWord_2274036 prefixEnd_2274036 778448995751846704927937 := by
  unfold tailWord_2274036
  simp only [CollatzResearch.WordTrace]
  refine ⟨41470453394781710636920981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55293937859708947515894641 41470453394781710636920981)
  ·
    refine ⟨1943927502880392686105671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41470453394781710636920981 1943927502880392686105671)
    ·
      refine ⟨2915891254320589029158507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943927502880392686105671 2915891254320589029158507)
      ·
        refine ⟨4373836881480883543737761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915891254320589029158507 4373836881480883543737761)
        ·
          refine ⟨3280377661110662657803321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4373836881480883543737761 3280377661110662657803321)
          ·
            refine ⟨2460283245832996993352491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3280377661110662657803321 2460283245832996993352491)
            ·
              refine ⟨3690424868749495490028737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460283245832996993352491 3690424868749495490028737)
              ·
                refine ⟨2767818651562121617521553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690424868749495490028737 2767818651562121617521553)
                ·
                  refine ⟨2075863988671591213141165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767818651562121617521553 2075863988671591213141165)
                  ·
                    refine ⟨778448995751846704927937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075863988671591213141165 778448995751846704927937)
                    ·
                      rfl

theorem cell22_2274036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2274036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274036 prefixEnd_2274036 := by exact prefixLift 2274036
  have htrace : WordTrace (prefixWord ++ tailWord_2274036) baseStart_2274036 baseEnd_2274036 := by
    simpa [prefixWord, tailWord_2274036, baseEnd_2274036] using wordTrace_append hprefix tailTrace_2274036
  have hstable : (prefixWord ++ tailWord_2274036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274036).length < 2 ^ (prefixWord ++ tailWord_2274036).sum := by decide
  have hdescent : baseEnd_2274036 < baseStart_2274036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274103 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2274103 : Nat := 118140960795 + 2274103 * 2 ^ 59
def prefixEnd_2274103 : Nat := 4983230072969 + 3 ^ 40 * 2274103 * 2
def baseEnd_2274103 : Nat := 778471931221080863502731

theorem tailTrace_2274103 : CollatzResearch.WordTrace tailWord_2274103 prefixEnd_2274103 778471931221080863502731 := by
  unfold tailWord_2274103
  simp only [CollatzResearch.WordTrace]
  refine ⟨82943350480320691716530963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55295566986880461144353975 82943350480320691716530963)
  ·
    refine ⟨124415025720481037574796445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82943350480320691716530963 124415025720481037574796445)
    ·
      refine ⟨46655634645180389090548667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124415025720481037574796445 46655634645180389090548667)
      ·
        refine ⟨69983451967770583635823001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46655634645180389090548667 69983451967770583635823001)
        ·
          refine ⟨52487588975827937726867251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69983451967770583635823001 52487588975827937726867251)
          ·
            refine ⟨78731383463741906590300877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52487588975827937726867251 78731383463741906590300877)
            ·
              refine ⟨29524268798903214971362829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78731383463741906590300877 29524268798903214971362829)
              ·
                refine ⟨11071600799588705614261061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29524268798903214971362829 11071600799588705614261061)
                ·
                  refine ⟨2075925149922882302673949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11071600799588705614261061 2075925149922882302673949)
                  ·
                    refine ⟨778471931221080863502731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075925149922882302673949 778471931221080863502731)
                    ·
                      rfl

theorem cell22_2274103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2274103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274103 prefixEnd_2274103 := by exact prefixLift 2274103
  have htrace : WordTrace (prefixWord ++ tailWord_2274103) baseStart_2274103 baseEnd_2274103 := by
    simpa [prefixWord, tailWord_2274103, baseEnd_2274103] using wordTrace_append hprefix tailTrace_2274103
  have hstable : (prefixWord ++ tailWord_2274103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274103).length < 2 ^ (prefixWord ++ tailWord_2274103).sum := by decide
  have hdescent : baseEnd_2274103 < baseStart_2274103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274120 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2274120 : Nat := 118140960795 + 2274120 * 2 ^ 59
def prefixEnd_2274120 : Nat := 4983230072969 + 3 ^ 40 * 2274120 * 2
def baseEnd_2274120 : Nat := 778477750668498485827679

theorem tailTrace_2274120 : CollatzResearch.WordTrace tailWord_2274120 prefixEnd_2274120 778477750668498485827679 := by
  unfold tailWord_2274120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471985260629551809949907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55295980347506069079933209 41471985260629551809949907)
  ·
    refine ⟨62207977890944327714924861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41471985260629551809949907 62207977890944327714924861)
    ·
      refine ⟨23327991709104122893096823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62207977890944327714924861 23327991709104122893096823)
      ·
        refine ⟨34991987563656184339645235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23327991709104122893096823 34991987563656184339645235)
        ·
          refine ⟨52487981345484276509467853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34991987563656184339645235 52487981345484276509467853)
          ·
            refine ⟨19682993004556603691050445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52487981345484276509467853 19682993004556603691050445)
            ·
              refine ⟨7381122376708726384143917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19682993004556603691050445 7381122376708726384143917)
              ·
                refine ⟨2767920891265772394053969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7381122376708726384143917 2767920891265772394053969)
                ·
                  refine ⟨2075940668449329295540477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767920891265772394053969 2075940668449329295540477)
                  ·
                    refine ⟨778477750668498485827679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075940668449329295540477 778477750668498485827679)
                    ·
                      rfl

theorem cell22_2274120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2274120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274120 prefixEnd_2274120 := by exact prefixLift 2274120
  have htrace : WordTrace (prefixWord ++ tailWord_2274120) baseStart_2274120 baseEnd_2274120 := by
    simpa [prefixWord, tailWord_2274120, baseEnd_2274120] using wordTrace_append hprefix tailTrace_2274120
  have hstable : (prefixWord ++ tailWord_2274120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274120).length < 2 ^ (prefixWord ++ tailWord_2274120).sum := by decide
  have hdescent : baseEnd_2274120 < baseStart_2274120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_2274131 : Nat := 118140960795 + 2274131 * 2 ^ 59
def prefixEnd_2274131 : Nat := 4983230072969 + 3 ^ 40 * 2274131 * 2
def baseEnd_2274131 : Nat := 778481516193298123802645

theorem tailTrace_2274131 : CollatzResearch.WordTrace tailWord_2274131 prefixEnd_2274131 778481516193298123802645 := by
  unfold tailWord_2274131
  simp only [CollatzResearch.WordTrace]
  refine ⟨82944371724219252498550247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55296247816146168332366831 82944371724219252498550247)
  ·
    refine ⟨124416557586328878747825371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82944371724219252498550247 124416557586328878747825371)
    ·
      refine ⟨186624836379493318121738057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124416557586328878747825371 186624836379493318121738057)
      ·
        refine ⟨139968627284619988591303543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186624836379493318121738057 139968627284619988591303543)
        ·
          refine ⟨209952940926929982886955315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139968627284619988591303543 209952940926929982886955315)
          ·
            refine ⟨314929411390394974330432973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209952940926929982886955315 314929411390394974330432973)
            ·
              refine ⟨118098529271398115373912365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314929411390394974330432973 118098529271398115373912365)
              ·
                refine ⟨44286948476774293265217137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118098529271398115373912365 44286948476774293265217137)
                ·
                  refine ⟨33215211357580719948912853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44286948476774293265217137 33215211357580719948912853)
                  ·
                    refine ⟨778481516193298123802645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33215211357580719948912853 778481516193298123802645)
                    ·
                      rfl

theorem cell22_2274131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_2274131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274131 prefixEnd_2274131 := by exact prefixLift 2274131
  have htrace : WordTrace (prefixWord ++ tailWord_2274131) baseStart_2274131 baseEnd_2274131 := by
    simpa [prefixWord, tailWord_2274131, baseEnd_2274131] using wordTrace_append hprefix tailTrace_2274131
  have hstable : (prefixWord ++ tailWord_2274131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274131).length < 2 ^ (prefixWord ++ tailWord_2274131).sum := by decide
  have hdescent : baseEnd_2274131 < baseStart_2274131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274135 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2274135 : Nat := 118140960795 + 2274135 * 2 ^ 59
def prefixEnd_2274135 : Nat := 4983230072969 + 3 ^ 40 * 2274135 * 2
def baseEnd_2274135 : Nat := 778482885475043446702633

theorem tailTrace_2274135 : CollatzResearch.WordTrace tailWord_2274135 prefixEnd_2274135 778482885475043446702633 := by
  unfold tailWord_2274135
  simp only [CollatzResearch.WordTrace]
  refine ⟨82944517616204761181695859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55296345077469840787797239 82944517616204761181695859)
  ·
    refine ⟨124416776424307141772543789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82944517616204761181695859 124416776424307141772543789)
    ·
      refine ⟨46656291159115178164703921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124416776424307141772543789 46656291159115178164703921)
      ·
        refine ⟨34992218369336383623527941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46656291159115178164703921 34992218369336383623527941)
        ·
          refine ⟨6561040944250571929411489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34992218369336383623527941 6561040944250571929411489)
          ·
            refine ⟨4920780708187928947058617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561040944250571929411489 4920780708187928947058617)
            ·
              refine ⟨3690585531140946710293963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920780708187928947058617 3690585531140946710293963)
              ·
                refine ⟨5535878296711420065440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690585531140946710293963 5535878296711420065440945)
                ·
                  refine ⟨4151908722533565049080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535878296711420065440945 4151908722533565049080709)
                  ·
                    refine ⟨778482885475043446702633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151908722533565049080709 778482885475043446702633)
                    ·
                      rfl

theorem cell22_2274135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2274135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274135 prefixEnd_2274135 := by exact prefixLift 2274135
  have htrace : WordTrace (prefixWord ++ tailWord_2274135) baseStart_2274135 baseEnd_2274135 := by
    simpa [prefixWord, tailWord_2274135, baseEnd_2274135] using wordTrace_append hprefix tailTrace_2274135
  have hstable : (prefixWord ++ tailWord_2274135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274135).length < 2 ^ (prefixWord ++ tailWord_2274135).sum := by decide
  have hdescent : baseEnd_2274135 < baseStart_2274135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274210 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2274210 : Nat := 118140960795 + 2274210 * 2 ^ 59
def prefixEnd_2274210 : Nat := 4983230072969 + 3 ^ 40 * 2274210 * 2
def baseEnd_2274210 : Nat := 778508559507768251077403

theorem tailTrace_2274210 : CollatzResearch.WordTrace tailWord_2274210 prefixEnd_2274210 778508559507768251077403 := by
  unfold tailWord_2274210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736813272733262247669021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55298168727288699327117389 20736813272733262247669021)
  ·
    refine ⟨7776304977274973342875883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20736813272733262247669021 7776304977274973342875883)
    ·
      refine ⟨11664457465912460014313825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776304977274973342875883 11664457465912460014313825)
      ·
        refine ⟨8748343099434345010735369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11664457465912460014313825 8748343099434345010735369)
        ·
          refine ⟨6561257324575758758051527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8748343099434345010735369 6561257324575758758051527)
          ·
            refine ⟨9841885986863638137077291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561257324575758758051527 9841885986863638137077291)
            ·
              refine ⟨14762828980295457205615937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841885986863638137077291 14762828980295457205615937)
              ·
                refine ⟨11072121735221592904211953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14762828980295457205615937 11072121735221592904211953)
                ·
                  refine ⟨8304091301416194678158965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11072121735221592904211953 8304091301416194678158965)
                  ·
                    refine ⟨778508559507768251077403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8304091301416194678158965 778508559507768251077403)
                    ·
                      rfl

theorem cell22_2274210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2274210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274210 prefixEnd_2274210 := by exact prefixLift 2274210
  have htrace : WordTrace (prefixWord ++ tailWord_2274210) baseStart_2274210 baseEnd_2274210 := by
    simpa [prefixWord, tailWord_2274210, baseEnd_2274210] using wordTrace_append hprefix tailTrace_2274210
  have hstable : (prefixWord ++ tailWord_2274210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274210).length < 2 ^ (prefixWord ++ tailWord_2274210).sum := by decide
  have hdescent : baseEnd_2274210 < baseStart_2274210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274255 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 4, 3]
def baseStart_2274255 : Nat := 118140960795 + 2274255 * 2 ^ 59
def prefixEnd_2274255 : Nat := 4983230072969 + 3 ^ 40 * 2274255 * 2
def baseEnd_2274255 : Nat := 778523963927403133702265

theorem tailTrace_2274255 : CollatzResearch.WordTrace tailWord_2274255 prefixEnd_2274255 778523963927403133702265 := by
  unfold tailWord_2274255
  simp only [CollatzResearch.WordTrace]
  refine ⟨82948894375770021676064219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55299262917180014450709479 82948894375770021676064219)
  ·
    refine ⟨124423341563655032514096329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82948894375770021676064219 124423341563655032514096329)
    ·
      refine ⟨93317506172741274385572247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124423341563655032514096329 93317506172741274385572247)
      ·
        refine ⟨139976259259111911578358371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93317506172741274385572247 139976259259111911578358371)
        ·
          refine ⟨209964388888667867367537557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139976259259111911578358371 209964388888667867367537557)
          ·
            refine ⟨9842080729156306282853323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 209964388888667867367537557 9842080729156306282853323)
            ·
              refine ⟨14763121093734459424279985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9842080729156306282853323 14763121093734459424279985)
              ·
                refine ⟨11072340820300844568209989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14763121093734459424279985 11072340820300844568209989)
                ·
                  refine ⟨2076063903806408356539373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11072340820300844568209989 2076063903806408356539373)
                  ·
                    refine ⟨778523963927403133702265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076063903806408356539373 778523963927403133702265)
                    ·
                      rfl

theorem cell22_2274255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_2274255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274255 prefixEnd_2274255 := by exact prefixLift 2274255
  have htrace : WordTrace (prefixWord ++ tailWord_2274255) baseStart_2274255 baseEnd_2274255 := by
    simpa [prefixWord, tailWord_2274255, baseEnd_2274255] using wordTrace_append hprefix tailTrace_2274255
  have hstable : (prefixWord ++ tailWord_2274255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274255).length < 2 ^ (prefixWord ++ tailWord_2274255).sum := by decide
  have hdescent : baseEnd_2274255 < baseStart_2274255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274274 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2274274 : Nat := 118140960795 + 2274274 * 2 ^ 59
def prefixEnd_2274274 : Nat := 4983230072969 + 3 ^ 40 * 2274274 * 2
def baseEnd_2274274 : Nat := 259510156005231139159069

theorem tailTrace_2274274 : CollatzResearch.WordTrace tailWord_2274274 prefixEnd_2274274 259510156005231139159069 := by
  unfold tailWord_2274274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20737396840675296980251469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55299724908467458614003917 20737396840675296980251469)
  ·
    refine ⟨7776523815253236367594301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20737396840675296980251469 7776523815253236367594301)
    ·
      refine ⟨2916196430719963637847863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7776523815253236367594301 2916196430719963637847863)
      ·
        refine ⟨4374294646079945456771795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916196430719963637847863 4374294646079945456771795)
        ·
          refine ⟨6561441969119918185157693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374294646079945456771795 6561441969119918185157693)
          ·
            refine ⟨2460540738419969319434135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6561441969119918185157693 2460540738419969319434135)
            ·
              refine ⟨3690811107629953979151203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460540738419969319434135 3690811107629953979151203)
              ·
                refine ⟨5536216661444930968726805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690811107629953979151203 5536216661444930968726805)
                ·
                  refine ⟨259510156005231139159069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5536216661444930968726805 259510156005231139159069)
                  ·
                    rfl

theorem cell22_2274274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2274274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274274 prefixEnd_2274274 := by exact prefixLift 2274274
  have htrace : WordTrace (prefixWord ++ tailWord_2274274) baseStart_2274274 baseEnd_2274274 := by
    simpa [prefixWord, tailWord_2274274, baseEnd_2274274] using wordTrace_append hprefix tailTrace_2274274
  have hstable : (prefixWord ++ tailWord_2274274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274274).length < 2 ^ (prefixWord ++ tailWord_2274274).sum := by decide
  have hdescent : baseEnd_2274274 < baseStart_2274274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274289 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_2274289 : Nat := 118140960795 + 2274289 * 2 ^ 59
def prefixEnd_2274289 : Nat := 4983230072969 + 3 ^ 40 * 2274289 * 2
def baseEnd_2274289 : Nat := 778535602822238378352161

theorem tailTrace_2274289 : CollatzResearch.WordTrace tailWord_2274289 prefixEnd_2274289 778535602822238378352161 := by
  unfold tailWord_2274289
  simp only [CollatzResearch.WordTrace]
  refine ⟨82950134457646845482801921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55300089638431230321867947 82950134457646845482801921)
  ·
    refine ⟨62212600843235134112101441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82950134457646845482801921 62212600843235134112101441)
    ·
      refine ⟨46659450632426350584076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62212600843235134112101441 46659450632426350584076081)
      ·
        refine ⟨34994587974319762938057061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46659450632426350584076081 34994587974319762938057061)
        ·
          refine ⟨6561485245184955550885699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34994587974319762938057061 6561485245184955550885699)
          ·
            refine ⟨9842227867777433326328549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561485245184955550885699 9842227867777433326328549)
            ·
              refine ⟨1845417725208268748686603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9842227867777433326328549 1845417725208268748686603)
              ·
                refine ⟨2768126587812403123029905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845417725208268748686603 2768126587812403123029905)
                ·
                  refine ⟨2076094940859302342272429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768126587812403123029905 2076094940859302342272429)
                  ·
                    refine ⟨778535602822238378352161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076094940859302342272429 778535602822238378352161)
                    ·
                      rfl

theorem cell22_2274289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_2274289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274289 prefixEnd_2274289 := by exact prefixLift 2274289
  have htrace : WordTrace (prefixWord ++ tailWord_2274289) baseStart_2274289 baseEnd_2274289 := by
    simpa [prefixWord, tailWord_2274289, baseEnd_2274289] using wordTrace_append hprefix tailTrace_2274289
  have hstable : (prefixWord ++ tailWord_2274289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274289).length < 2 ^ (prefixWord ++ tailWord_2274289).sum := by decide
  have hdescent : baseEnd_2274289 < baseStart_2274289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274293 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2274293 : Nat := 118140960795 + 2274293 * 2 ^ 59
def prefixEnd_2274293 : Nat := 4983230072969 + 3 ^ 40 * 2274293 * 2
def baseEnd_2274293 : Nat := 778536972103983701252149

theorem tailTrace_2274293 : CollatzResearch.WordTrace tailWord_2274293 prefixEnd_2274293 778536972103983701252149 := by
  unfold tailWord_2274293
  simp only [CollatzResearch.WordTrace]
  refine ⟨82950280349632354165947533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55300186899754902777298355 82950280349632354165947533)
  ·
    refine ⟨31106355131112132812230325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82950280349632354165947533 31106355131112132812230325)
    ·
      refine ⟨2916220793541762451146593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31106355131112132812230325 2916220793541762451146593)
      ·
        refine ⟨2187165595156321838359945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2916220793541762451146593 2187165595156321838359945)
        ·
          refine ⟨1640374196367241378769959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2187165595156321838359945 1640374196367241378769959)
          ·
            refine ⟨2460561294550862068154939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640374196367241378769959 2460561294550862068154939)
            ·
              refine ⟨3690841941826293102232409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460561294550862068154939 3690841941826293102232409)
              ·
                refine ⟨2768131456369719826674307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690841941826293102232409 2768131456369719826674307)
                ·
                  refine ⟨4152197184554579740011461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768131456369719826674307 4152197184554579740011461)
                  ·
                    refine ⟨778536972103983701252149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4152197184554579740011461 778536972103983701252149)
                    ·
                      rfl

theorem cell22_2274293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2274293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274293 prefixEnd_2274293 := by exact prefixLift 2274293
  have htrace : WordTrace (prefixWord ++ tailWord_2274293) baseStart_2274293 baseEnd_2274293 := by
    simpa [prefixWord, tailWord_2274293, baseEnd_2274293] using wordTrace_append hprefix tailTrace_2274293
  have hstable : (prefixWord ++ tailWord_2274293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274293).length < 2 ^ (prefixWord ++ tailWord_2274293).sum := by decide
  have hdescent : baseEnd_2274293 < baseStart_2274293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274313 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 9]
def baseStart_2274313 : Nat := 118140960795 + 2274313 * 2 ^ 59
def prefixEnd_2274313 : Nat := 4983230072969 + 3 ^ 40 * 2274313 * 2
def baseEnd_2274313 : Nat := 259514606170903438584029

theorem tailTrace_2274313 : CollatzResearch.WordTrace tailWord_2274313 prefixEnd_2274313 259514606170903438584029 := by
  unfold tailWord_2274313
  simp only [CollatzResearch.WordTrace]
  refine ⟨82951009809559897581675593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55300673206373265054450395 82951009809559897581675593)
  ·
    refine ⟨62213257357169923186256695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82951009809559897581675593 62213257357169923186256695)
    ·
      refine ⟨93319886035754884779385043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62213257357169923186256695 93319886035754884779385043)
      ·
        refine ⟨139979829053632327169077565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93319886035754884779385043 139979829053632327169077565)
        ·
          refine ⟨52492435895112122688404087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139979829053632327169077565 52492435895112122688404087)
          ·
            refine ⟨78738653842668184032606131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52492435895112122688404087 78738653842668184032606131)
            ·
              refine ⟨118107980764002276048909197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78738653842668184032606131 118107980764002276048909197)
              ·
                refine ⟨44290492786500853518340949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118107980764002276048909197 44290492786500853518340949)
                ·
                  refine ⟨259514606170903438584029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44290492786500853518340949 259514606170903438584029)
                  ·
                    rfl

theorem cell22_2274313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_2274313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274313 prefixEnd_2274313 := by exact prefixLift 2274313
  have htrace : WordTrace (prefixWord ++ tailWord_2274313) baseStart_2274313 baseEnd_2274313 := by
    simpa [prefixWord, tailWord_2274313, baseEnd_2274313] using wordTrace_append hprefix tailTrace_2274313
  have hstable : (prefixWord ++ tailWord_2274313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274313).length < 2 ^ (prefixWord ++ tailWord_2274313).sum := by decide
  have hdescent : baseEnd_2274313 < baseStart_2274313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274392 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_2274392 : Nat := 118140960795 + 2274392 * 2 ^ 59
def prefixEnd_2274392 : Nat := 4983230072969 + 3 ^ 40 * 2274392 * 2
def baseEnd_2274392 : Nat := 259523620609060147675615

theorem tailTrace_2274392 : CollatzResearch.WordTrace tailWord_2274392 prefixEnd_2274392 259523620609060147675615 := by
  unfold tailWord_2274392
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476945588136847036900715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55302594117515796049200953 41476945588136847036900715)
  ·
    refine ⟨62215418382205270555351073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41476945588136847036900715 62215418382205270555351073)
    ·
      refine ⟨46661563786653952916513305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62215418382205270555351073 46661563786653952916513305)
      ·
        refine ⟨34996172839990464687384979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46661563786653952916513305 34996172839990464687384979)
        ·
          refine ⟨52494259259985697031077469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34996172839990464687384979 52494259259985697031077469)
          ·
            refine ⟨19685347222494636386654051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52494259259985697031077469 19685347222494636386654051)
            ·
              refine ⟨29528020833741954579981077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685347222494636386654051 29528020833741954579981077)
              ·
                refine ⟨1384125976581654120936613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29528020833741954579981077 1384125976581654120936613)
                ·
                  refine ⟨259523620609060147675615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384125976581654120936613 259523620609060147675615)
                  ·
                    rfl

theorem cell22_2274392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_2274392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274392 prefixEnd_2274392 := by exact prefixLift 2274392
  have htrace : WordTrace (prefixWord ++ tailWord_2274392) baseStart_2274392 baseEnd_2274392 := by
    simpa [prefixWord, tailWord_2274392, baseEnd_2274392] using wordTrace_append hprefix tailTrace_2274392
  have hstable : (prefixWord ++ tailWord_2274392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274392).length < 2 ^ (prefixWord ++ tailWord_2274392).sum := by decide
  have hdescent : baseEnd_2274392 < baseStart_2274392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274398 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2274398 : Nat := 118140960795 + 2274398 * 2 ^ 59
def prefixEnd_2274398 : Nat := 4983230072969 + 3 ^ 40 * 2274398 * 2
def baseEnd_2274398 : Nat := 259524305249932809125609

theorem tailTrace_2274398 : CollatzResearch.WordTrace tailWord_2274398 prefixEnd_2274398 259524305249932809125609 := by
  unfold tailWord_2274398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369263751781494637314981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55302740009501304732346565 10369263751781494637314981)
  ·
    refine ⟨1944236953459030244496559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10369263751781494637314981 1944236953459030244496559)
    ·
      refine ⟨2916355430188545366744839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944236953459030244496559 2916355430188545366744839)
      ·
        refine ⟨4374533145282818050117259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916355430188545366744839 4374533145282818050117259)
        ·
          refine ⟨6561799717924227075175889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374533145282818050117259 6561799717924227075175889)
          ·
            refine ⟨4921349788443170306381917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561799717924227075175889 4921349788443170306381917)
            ·
              refine ⟨1845506170666188864893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4921349788443170306381917 1845506170666188864893219)
              ·
                refine ⟨2768259255999283297339829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845506170666188864893219 2768259255999283297339829)
                ·
                  refine ⟨259524305249932809125609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768259255999283297339829 259524305249932809125609)
                  ·
                    rfl

theorem cell22_2274398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2274398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274398 prefixEnd_2274398 := by exact prefixLift 2274398
  have htrace : WordTrace (prefixWord ++ tailWord_2274398) baseStart_2274398 baseEnd_2274398 := by
    simpa [prefixWord, tailWord_2274398, baseEnd_2274398] using wordTrace_append hprefix tailTrace_2274398
  have hstable : (prefixWord ++ tailWord_2274398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274398).length < 2 ^ (prefixWord ++ tailWord_2274398).sum := by decide
  have hdescent : baseEnd_2274398 < baseStart_2274398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274405 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2274405 : Nat := 118140960795 + 2274405 * 2 ^ 59
def prefixEnd_2274405 : Nat := 4983230072969 + 3 ^ 40 * 2274405 * 2
def baseEnd_2274405 : Nat := 778575311992852742451805

theorem tailTrace_2274405 : CollatzResearch.WordTrace tailWord_2274405 prefixEnd_2274405 778575311992852742451805 := by
  unfold tailWord_2274405
  simp only [CollatzResearch.WordTrace]
  refine ⟨82954365325226597294024669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55302910216817731529349779 82954365325226597294024669)
  ·
    refine ⟨31107886996959973985259251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82954365325226597294024669 31107886996959973985259251)
    ·
      refine ⟨46661830495439960977888877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31107886996959973985259251 46661830495439960977888877)
      ·
        refine ⟨17498186435789985366708329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46661830495439960977888877 17498186435789985366708329)
        ·
          refine ⟨13123639826842489025031247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17498186435789985366708329 13123639826842489025031247)
          ·
            refine ⟨19685459740263733537546871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123639826842489025031247 19685459740263733537546871)
            ·
              refine ⟨29528189610395600306320307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685459740263733537546871 29528189610395600306320307)
              ·
                refine ⟨44292284415593400459480461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29528189610395600306320307 44292284415593400459480461)
                ·
                  refine ⟨16609606655847525172305173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44292284415593400459480461 16609606655847525172305173)
                  ·
                    refine ⟨778575311992852742451805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16609606655847525172305173 778575311992852742451805)
                    ·
                      rfl

theorem cell22_2274405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2274405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274405 prefixEnd_2274405 := by exact prefixLift 2274405
  have htrace : WordTrace (prefixWord ++ tailWord_2274405) baseStart_2274405 baseEnd_2274405 := by
    simpa [prefixWord, tailWord_2274405, baseEnd_2274405] using wordTrace_append hprefix tailTrace_2274405
  have hstable : (prefixWord ++ tailWord_2274405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274405).length < 2 ^ (prefixWord ++ tailWord_2274405).sum := by decide
  have hdescent : baseEnd_2274405 < baseStart_2274405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274407 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2274407 : Nat := 118140960795 + 2274407 * 2 ^ 59
def prefixEnd_2274407 : Nat := 4983230072969 + 3 ^ 40 * 2274407 * 2
def baseEnd_2274407 : Nat := 778575996633725403901799

theorem tailTrace_2274407 : CollatzResearch.WordTrace tailWord_2274407 prefixEnd_2274407 778575996633725403901799 := by
  unfold tailWord_2274407
  simp only [CollatzResearch.WordTrace]
  refine ⟨82954438271219351635597475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55302958847479567757064983 82954438271219351635597475)
  ·
    refine ⟨124431657406829027453396213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82954438271219351635597475 124431657406829027453396213)
    ·
      refine ⟨11665467881890221323755895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124431657406829027453396213 11665467881890221323755895)
      ·
        refine ⟨17498201822835331985633843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665467881890221323755895 17498201822835331985633843)
        ·
          refine ⟨26247302734252997978450765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498201822835331985633843 26247302734252997978450765)
          ·
            refine ⟨9842738525344874241919037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26247302734252997978450765 9842738525344874241919037)
            ·
              refine ⟨3691026947004327840719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9842738525344874241919037 3691026947004327840719639)
              ·
                refine ⟨5536540420506491761079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691026947004327840719639 5536540420506491761079459)
                ·
                  refine ⟨8304810630759737641619189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536540420506491761079459 8304810630759737641619189)
                  ·
                    refine ⟨778575996633725403901799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8304810630759737641619189 778575996633725403901799)
                    ·
                      rfl

theorem cell22_2274407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2274407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274407 prefixEnd_2274407 := by exact prefixLift 2274407
  have htrace : WordTrace (prefixWord ++ tailWord_2274407) baseStart_2274407 baseEnd_2274407 := by
    simpa [prefixWord, tailWord_2274407, baseEnd_2274407] using wordTrace_append hprefix tailTrace_2274407
  have hstable : (prefixWord ++ tailWord_2274407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274407).length < 2 ^ (prefixWord ++ tailWord_2274407).sum := by decide
  have hdescent : baseEnd_2274407 < baseStart_2274407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274422 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2274422 : Nat := 118140960795 + 2274422 * 2 ^ 59
def prefixEnd_2274422 : Nat := 4983230072969 + 3 ^ 40 * 2274422 * 2
def baseEnd_2274422 : Nat := 778581131440270364776753

theorem tailTrace_2274422 : CollatzResearch.WordTrace tailWord_2274422 prefixEnd_2274422 778581131440270364776753 := by
  unfold tailWord_2274422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184686585385313074837095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55303323577443339464929013 5184686585385313074837095)
  ·
    refine ⟨7777029878077969612255643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5184686585385313074837095 7777029878077969612255643)
    ·
      refine ⟨11665544817116954418383465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777029878077969612255643 11665544817116954418383465)
      ·
        refine ⟨8749158612837715813787599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11665544817116954418383465 8749158612837715813787599)
        ·
          refine ⟨13123737919256573720681399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8749158612837715813787599 13123737919256573720681399)
          ·
            refine ⟨19685606878884860581022099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123737919256573720681399 19685606878884860581022099)
            ·
              refine ⟨29528410318327290871533149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685606878884860581022099 29528410318327290871533149)
              ·
                refine ⟨11073153869372734076824931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29528410318327290871533149 11073153869372734076824931)
                ·
                  refine ⟨16609730804059101115237397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11073153869372734076824931 16609730804059101115237397)
                  ·
                    refine ⟨778581131440270364776753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16609730804059101115237397 778581131440270364776753)
                    ·
                      rfl

theorem cell22_2274422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2274422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274422 prefixEnd_2274422 := by exact prefixLift 2274422
  have htrace : WordTrace (prefixWord ++ tailWord_2274422) baseStart_2274422 baseEnd_2274422 := by
    simpa [prefixWord, tailWord_2274422, baseEnd_2274422] using wordTrace_append hprefix tailTrace_2274422
  have hstable : (prefixWord ++ tailWord_2274422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274422).length < 2 ^ (prefixWord ++ tailWord_2274422).sum := by decide
  have hdescent : baseEnd_2274422 < baseStart_2274422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274437 : List Nat := [1, 3, 1, 1, 6, 2, 8]
def baseStart_2274437 : Nat := 118140960795 + 2274437 * 2 ^ 59
def prefixEnd_2274437 : Nat := 4983230072969 + 3 ^ 40 * 2274437 * 2
def baseEnd_2274437 : Nat := 28836528379511678727841

theorem tailTrace_2274437 : CollatzResearch.WordTrace tailWord_2274437 prefixEnd_2274437 28836528379511678727841 := by
  unfold tailWord_2274437
  simp only [CollatzResearch.WordTrace]
  refine ⟨82955532461110666759189565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55303688307407111172793043 82955532461110666759189565)
  ·
    refine ⟨31108324672916500034696087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82955532461110666759189565 31108324672916500034696087)
    ·
      refine ⟨46662487009374750052044131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31108324672916500034696087 46662487009374750052044131)
      ·
        refine ⟨69993730514062125078066197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46662487009374750052044131 69993730514062125078066197)
        ·
          refine ⟨3280956117846662113034353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69993730514062125078066197 3280956117846662113034353)
          ·
            refine ⟨2460717088384996584775765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3280956117846662113034353 2460717088384996584775765)
            ·
              refine ⟨28836528379511678727841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2460717088384996584775765 28836528379511678727841)
              ·
                rfl

theorem cell22_2274437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 8].length) (baseStart_2274437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274437 prefixEnd_2274437 := by exact prefixLift 2274437
  have htrace : WordTrace (prefixWord ++ tailWord_2274437) baseStart_2274437 baseEnd_2274437 := by
    simpa [prefixWord, tailWord_2274437, baseEnd_2274437] using wordTrace_append hprefix tailTrace_2274437
  have hstable : (prefixWord ++ tailWord_2274437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274437).length < 2 ^ (prefixWord ++ tailWord_2274437).sum := by decide
  have hdescent : baseEnd_2274437 < baseStart_2274437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274458 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_2274458 : Nat := 118140960795 + 2274458 * 2 ^ 59
def prefixEnd_2274458 : Nat := 4983230072969 + 3 ^ 40 * 2274458 * 2
def baseEnd_2274458 : Nat := 778593454975978270876643

theorem tailTrace_2274458 : CollatzResearch.WordTrace tailWord_2274458 prefixEnd_2274458 778593454975978270876643 := by
  unfold tailWord_2274458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739074598508646836426007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55304198929356391563802685 20739074598508646836426007)
  ·
    refine ⟨31108611897762970254639011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20739074598508646836426007 31108611897762970254639011)
    ·
      refine ⟨46662917846644455381958517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31108611897762970254639011 46662917846644455381958517)
      ·
        refine ⟨4374648548122917692058611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46662917846644455381958517 4374648548122917692058611)
        ·
          refine ⟨6561972822184376538087917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374648548122917692058611 6561972822184376538087917)
          ·
            refine ⟨2460739808319141201782969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6561972822184376538087917 2460739808319141201782969)
            ·
              refine ⟨1845554856239355901337227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460739808319141201782969 1845554856239355901337227)
              ·
                refine ⟨2768332284359033852005841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845554856239355901337227 2768332284359033852005841)
                ·
                  refine ⟨2076249213269275389004381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768332284359033852005841 2076249213269275389004381)
                  ·
                    refine ⟨778593454975978270876643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076249213269275389004381 778593454975978270876643)
                    ·
                      rfl

theorem cell22_2274458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_2274458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274458 prefixEnd_2274458 := by exact prefixLift 2274458
  have htrace : WordTrace (prefixWord ++ tailWord_2274458) baseStart_2274458 baseEnd_2274458 := by
    simpa [prefixWord, tailWord_2274458, baseEnd_2274458] using wordTrace_append hprefix tailTrace_2274458
  have hstable : (prefixWord ++ tailWord_2274458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274458).length < 2 ^ (prefixWord ++ tailWord_2274458).sum := by decide
  have hdescent : baseEnd_2274458 < baseStart_2274458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274480 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_2274480 : Nat := 118140960795 + 2274480 * 2 ^ 59
def prefixEnd_2274480 : Nat := 4983230072969 + 3 ^ 40 * 2274480 * 2
def baseEnd_2274480 : Nat := 778600986025577546826575

theorem tailTrace_2274480 : CollatzResearch.WordTrace tailWord_2274480 prefixEnd_2274480 778600986025577546826575 := by
  unfold tailWord_2274480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41478550399977442551502447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55304733866636590068669929 41478550399977442551502447)
  ·
    refine ⟨62217825599966163827253671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41478550399977442551502447 62217825599966163827253671)
    ·
      refine ⟨93326738399949245740880507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62217825599966163827253671 93326738399949245740880507)
      ·
        refine ⟨139990107599923868611320761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93326738399949245740880507 139990107599923868611320761)
        ·
          refine ⟨104992580699942901458490571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139990107599923868611320761 104992580699942901458490571)
          ·
            refine ⟨157488871049914352187735857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104992580699942901458490571 157488871049914352187735857)
            ·
              refine ⟨118116653287435764140801893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157488871049914352187735857 118116653287435764140801893)
              ·
                refine ⟨22146872491394205776400355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118116653287435764140801893 22146872491394205776400355)
                ·
                  refine ⟨33220308737091308664600533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22146872491394205776400355 33220308737091308664600533)
                  ·
                    refine ⟨778600986025577546826575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33220308737091308664600533 778600986025577546826575)
                    ·
                      rfl

theorem cell22_2274480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_2274480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274480 prefixEnd_2274480 := by exact prefixLift 2274480
  have htrace : WordTrace (prefixWord ++ tailWord_2274480) baseStart_2274480 baseEnd_2274480 := by
    simpa [prefixWord, tailWord_2274480, baseEnd_2274480] using wordTrace_append hprefix tailTrace_2274480
  have hstable : (prefixWord ++ tailWord_2274480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274480).length < 2 ^ (prefixWord ++ tailWord_2274480).sum := by decide
  have hdescent : baseEnd_2274480 < baseStart_2274480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274546 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2274546 : Nat := 118140960795 + 2274546 * 2 ^ 59
def prefixEnd_2274546 : Nat := 4983230072969 + 3 ^ 40 * 2274546 * 2
def baseEnd_2274546 : Nat := 778623579174375374676373

theorem tailTrace_2274546 : CollatzResearch.WordTrace tailWord_2274546 prefixEnd_2274546 778623579174375374676373 := by
  unfold tailWord_2274546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739877004428944593726873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55306338678477185583271661 20739877004428944593726873)
  ·
    refine ⟨15554907753321708445295155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20739877004428944593726873 15554907753321708445295155)
    ·
      refine ⟨23332361629982562667942733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15554907753321708445295155 23332361629982562667942733)
      ·
        refine ⟨8749635611243461000478525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23332361629982562667942733 8749635611243461000478525)
        ·
          refine ⟨3281113354216297875179447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8749635611243461000478525 3281113354216297875179447)
          ·
            refine ⟨4921670031324446812769171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281113354216297875179447 4921670031324446812769171)
            ·
              refine ⟨7382505046986670219153757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921670031324446812769171 7382505046986670219153757)
              ·
                refine ⟨2768439392620001332182659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7382505046986670219153757 2768439392620001332182659)
                ·
                  refine ⟨4152659088930001998273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768439392620001332182659 4152659088930001998273989)
                  ·
                    refine ⟨778623579174375374676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4152659088930001998273989 778623579174375374676373)
                    ·
                      rfl

theorem cell22_2274546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2274546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274546 prefixEnd_2274546 := by exact prefixLift 2274546
  have htrace : WordTrace (prefixWord ++ tailWord_2274546) baseStart_2274546 baseEnd_2274546 := by
    simpa [prefixWord, tailWord_2274546, baseEnd_2274546] using wordTrace_append hprefix tailTrace_2274546
  have hstable : (prefixWord ++ tailWord_2274546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274546).length < 2 ^ (prefixWord ++ tailWord_2274546).sum := by decide
  have hdescent : baseEnd_2274546 < baseStart_2274546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274559 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 4, 3]
def baseStart_2274559 : Nat := 118140960795 + 2274559 * 2 ^ 59
def prefixEnd_2274559 : Nat := 4983230072969 + 3 ^ 40 * 2274559 * 2
def baseEnd_2274559 : Nat := 778628029340047674101333

theorem tailTrace_2274559 : CollatzResearch.WordTrace tailWord_2274559 prefixEnd_2274559 778628029340047674101333 := by
  unfold tailWord_2274559
  simp only [CollatzResearch.WordTrace]
  refine ⟨82959982166668681595130731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55306654777779121063420487 82959982166668681595130731)
  ·
    refine ⟨124439973250003022392696097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82959982166668681595130731 124439973250003022392696097)
    ·
      refine ⟨93329979937502266794522073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124439973250003022392696097 93329979937502266794522073)
      ·
        refine ⟨69997484953126700095891555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93329979937502266794522073 69997484953126700095891555)
        ·
          refine ⟨104996227429690050143837333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69997484953126700095891555 104996227429690050143837333)
          ·
            refine ⟨4921698160766721100492375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104996227429690050143837333 4921698160766721100492375)
            ·
              refine ⟨7382547241150081650738563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921698160766721100492375 7382547241150081650738563)
              ·
                refine ⟨11073820861725122476107845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382547241150081650738563 11073820861725122476107845)
                ·
                  refine ⟨2076341411573460464270221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11073820861725122476107845 2076341411573460464270221)
                  ·
                    refine ⟨778628029340047674101333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076341411573460464270221 778628029340047674101333)
                    ·
                      rfl

theorem cell22_2274559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_2274559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274559 prefixEnd_2274559 := by exact prefixLift 2274559
  have htrace : WordTrace (prefixWord ++ tailWord_2274559) baseStart_2274559 baseEnd_2274559 := by
    simpa [prefixWord, tailWord_2274559, baseEnd_2274559] using wordTrace_append hprefix tailTrace_2274559
  have hstable : (prefixWord ++ tailWord_2274559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274559).length < 2 ^ (prefixWord ++ tailWord_2274559).sum := by decide
  have hdescent : baseEnd_2274559 < baseStart_2274559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274589 : List Nat := [1, 4, 2, 3, 1, 2, 1, 8]
def baseStart_2274589 : Nat := 118140960795 + 2274589 * 2 ^ 59
def prefixEnd_2274589 : Nat := 4983230072969 + 3 ^ 40 * 2274589 * 2
def baseEnd_2274589 : Nat := 86515366550348621761249

theorem tailTrace_2274589 : CollatzResearch.WordTrace tailWord_2274589 prefixEnd_2274589 86515366550348621761249 := by
  unfold tailWord_2274589
  simp only [CollatzResearch.WordTrace]
  refine ⟨82961076356559996718722821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55307384237706664479148547 82961076356559996718722821)
  ·
    refine ⟨15555201816854999384760529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82961076356559996718722821 15555201816854999384760529)
    ·
      refine ⟨11666401362641249538570397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15555201816854999384760529 11666401362641249538570397)
      ·
        refine ⟨4374900510990468576963899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11666401362641249538570397 4374900510990468576963899)
        ·
          refine ⟨6562350766485702865445849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374900510990468576963899 6562350766485702865445849)
          ·
            refine ⟨4921763074864277149084387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562350766485702865445849 4921763074864277149084387)
            ·
              refine ⟨7382644612296415723626581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921763074864277149084387 7382644612296415723626581)
              ·
                refine ⟨86515366550348621761249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7382644612296415723626581 86515366550348621761249)
                ·
                  rfl

theorem cell22_2274589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 8].length) (baseStart_2274589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274589 prefixEnd_2274589 := by exact prefixLift 2274589
  have htrace : WordTrace (prefixWord ++ tailWord_2274589) baseStart_2274589 baseEnd_2274589 := by
    simpa [prefixWord, tailWord_2274589, baseEnd_2274589] using wordTrace_append hprefix tailTrace_2274589
  have hstable : (prefixWord ++ tailWord_2274589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274589).length < 2 ^ (prefixWord ++ tailWord_2274589).sum := by decide
  have hdescent : baseEnd_2274589 < baseStart_2274589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274632 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2274632 : Nat := 118140960795 + 2274632 * 2 ^ 59
def prefixEnd_2274632 : Nat := 4983230072969 + 3 ^ 40 * 2274632 * 2
def baseEnd_2274632 : Nat := 778653018731899817026109

theorem tailTrace_2274632 : CollatzResearch.WordTrace tailWord_2274632 prefixEnd_2274632 778653018731899817026109 := by
  unfold tailWord_2274632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41481322347702107531269075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55308429796936143375025433 41481322347702107531269075)
  ·
    refine ⟨62221983521553161296903613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41481322347702107531269075 62221983521553161296903613)
    ·
      refine ⟨23333243820582435486338855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62221983521553161296903613 23333243820582435486338855)
      ·
        refine ⟨34999865730873653229508283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23333243820582435486338855 34999865730873653229508283)
        ·
          refine ⟨52499798596310479844262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34999865730873653229508283 52499798596310479844262425)
          ·
            refine ⟨39374848947232859883196819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52499798596310479844262425 39374848947232859883196819)
            ·
              refine ⟨59062273420849289824795229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39374848947232859883196819 59062273420849289824795229)
              ·
                refine ⟨22148352532818483684298211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59062273420849289824795229 22148352532818483684298211)
                ·
                  refine ⟨33222528799227725526447317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22148352532818483684298211 33222528799227725526447317)
                  ·
                    refine ⟨778653018731899817026109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33222528799227725526447317 778653018731899817026109)
                    ·
                      rfl

theorem cell22_2274632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2274632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274632 prefixEnd_2274632 := by exact prefixLift 2274632
  have htrace : WordTrace (prefixWord ++ tailWord_2274632) baseStart_2274632 baseEnd_2274632 := by
    simpa [prefixWord, tailWord_2274632, baseEnd_2274632] using wordTrace_append hprefix tailTrace_2274632
  have hstable : (prefixWord ++ tailWord_2274632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274632).length < 2 ^ (prefixWord ++ tailWord_2274632).sum := by decide
  have hdescent : baseEnd_2274632 < baseStart_2274632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274745 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_2274745 : Nat := 118140960795 + 2274745 * 2 ^ 59
def prefixEnd_2274745 : Nat := 4983230072969 + 3 ^ 40 * 2274745 * 2
def baseEnd_2274745 : Nat := 778691700941205188950763

theorem tailTrace_2274745 : CollatzResearch.WordTrace tailWord_2274745 prefixEnd_2274745 778691700941205188950763 := by
  unfold tailWord_2274745
  simp only [CollatzResearch.WordTrace]
  refine ⟨82966766143994835361401689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55311177429329890240934459 82966766143994835361401689)
  ·
    refine ⟨62225074607996126521051267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82966766143994835361401689 62225074607996126521051267)
    ·
      refine ⟨93337611911994189781576901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62225074607996126521051267 93337611911994189781576901)
      ·
        refine ⟨17500802233498910584045669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93337611911994189781576901 17500802233498910584045669)
        ·
          refine ⟨3281400418781045734508563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17500802233498910584045669 3281400418781045734508563)
          ·
            refine ⟨4922100628171568601762845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281400418781045734508563 4922100628171568601762845)
            ·
              refine ⟨1845787735564338225661067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4922100628171568601762845 1845787735564338225661067)
              ·
                refine ⟨2768681603346507338491601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845787735564338225661067 2768681603346507338491601)
                ·
                  refine ⟨2076511202509880503868701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768681603346507338491601 2076511202509880503868701)
                  ·
                    refine ⟨778691700941205188950763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076511202509880503868701 778691700941205188950763)
                    ·
                      rfl

theorem cell22_2274745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_2274745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274745 prefixEnd_2274745 := by exact prefixLift 2274745
  have htrace : WordTrace (prefixWord ++ tailWord_2274745) baseStart_2274745 baseEnd_2274745 := by
    simpa [prefixWord, tailWord_2274745, baseEnd_2274745] using wordTrace_append hprefix tailTrace_2274745
  have hstable : (prefixWord ++ tailWord_2274745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274745).length < 2 ^ (prefixWord ++ tailWord_2274745).sum := by decide
  have hdescent : baseEnd_2274745 < baseStart_2274745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274784 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_2274784 : Nat := 118140960795 + 2274784 * 2 ^ 59
def prefixEnd_2274784 : Nat := 4983230072969 + 3 ^ 40 * 2274784 * 2
def baseEnd_2274784 : Nat := 778705051438222087225643

theorem tailTrace_2274784 : CollatzResearch.WordTrace tailWord_2274784 prefixEnd_2274784 778705051438222087225643 := by
  unfold tailWord_2274784
  simp only [CollatzResearch.WordTrace]
  refine ⟨41484094295426772511035703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55312125727235696681380937 41484094295426772511035703)
  ·
    refine ⟨62226141443140158766553555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41484094295426772511035703 62226141443140158766553555)
    ·
      refine ⟨93339212164710238149830333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62226141443140158766553555 93339212164710238149830333)
      ·
        refine ⟨35002204561766339306186375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93339212164710238149830333 35002204561766339306186375)
        ·
          refine ⟨52503306842649508959279563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35002204561766339306186375 52503306842649508959279563)
          ·
            refine ⟨78754960263974263438919345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52503306842649508959279563 78754960263974263438919345)
            ·
              refine ⟨59066220197980697579189509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78754960263974263438919345 59066220197980697579189509)
              ·
                refine ⟨11074916287121380796098033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59066220197980697579189509 11074916287121380796098033)
                ·
                  refine ⟨8306187215341035597073525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11074916287121380796098033 8306187215341035597073525)
                  ·
                    refine ⟨778705051438222087225643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8306187215341035597073525 778705051438222087225643)
                    ·
                      rfl

theorem cell22_2274784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_2274784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274784 prefixEnd_2274784 := by exact prefixLift 2274784
  have htrace : WordTrace (prefixWord ++ tailWord_2274784) baseStart_2274784 baseEnd_2274784 := by
    simpa [prefixWord, tailWord_2274784, baseEnd_2274784] using wordTrace_append hprefix tailTrace_2274784
  have hstable : (prefixWord ++ tailWord_2274784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274784).length < 2 ^ (prefixWord ++ tailWord_2274784).sum := by decide
  have hdescent : baseEnd_2274784 < baseStart_2274784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274833 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_2274833 : Nat := 118140960795 + 2274833 * 2 ^ 59
def prefixEnd_2274833 : Nat := 4983230072969 + 3 ^ 40 * 2274833 * 2
def baseEnd_2274833 : Nat := 778721825139602292750493

theorem tailTrace_2274833 : CollatzResearch.WordTrace tailWord_2274833 prefixEnd_2274833 778721825139602292750493 := by
  unfold tailWord_2274833
  simp only [CollatzResearch.WordTrace]
  refine ⟨82969975767676026390605153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55313317178450684260403435 82969975767676026390605153)
  ·
    refine ⟨62227481825757019792953865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82969975767676026390605153 62227481825757019792953865)
    ·
      refine ⟨46670611369317764844715399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62227481825757019792953865 46670611369317764844715399)
      ·
        refine ⟨70005917053976647267073099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46670611369317764844715399 70005917053976647267073099)
        ·
          refine ⟨105008875580964970900609649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70005917053976647267073099 105008875580964970900609649)
          ·
            refine ⟨78756656685723728175457237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105008875580964970900609649 78756656685723728175457237)
            ·
              refine ⟨1845859141071649879112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78756656685723728175457237 1845859141071649879112279)
              ·
                refine ⟨2768788711607474818668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845859141071649879112279 2768788711607474818668419)
                ·
                  refine ⟨4153183067411212228002629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768788711607474818668419 4153183067411212228002629)
                  ·
                    refine ⟨778721825139602292750493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153183067411212228002629 778721825139602292750493)
                    ·
                      rfl

theorem cell22_2274833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_2274833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274833 prefixEnd_2274833 := by exact prefixLift 2274833
  have htrace : WordTrace (prefixWord ++ tailWord_2274833) baseStart_2274833 baseEnd_2274833 := by
    simpa [prefixWord, tailWord_2274833, baseEnd_2274833] using wordTrace_append hprefix tailTrace_2274833
  have hstable : (prefixWord ++ tailWord_2274833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274833).length < 2 ^ (prefixWord ++ tailWord_2274833).sum := by decide
  have hdescent : baseEnd_2274833 < baseStart_2274833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274891 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 7, 3]
def baseStart_2274891 : Nat := 118140960795 + 2274891 * 2 ^ 59
def prefixEnd_2274891 : Nat := 4983230072969 + 3 ^ 40 * 2274891 * 2
def baseEnd_2274891 : Nat := 778741679724909474800315

theorem tailTrace_2274891 : CollatzResearch.WordTrace tailWord_2274891 prefixEnd_2274891 778741679724909474800315 := by
  unfold tailWord_2274891
  simp only [CollatzResearch.WordTrace]
  refine ⟨82972091201465902296216527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55314727467643934864144351 82972091201465902296216527)
  ·
    refine ⟨124458136802198853444324791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82972091201465902296216527 124458136802198853444324791)
    ·
      refine ⟨186687205203298280166487187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124458136802198853444324791 186687205203298280166487187)
      ·
        refine ⟨280030807804947420249730781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186687205203298280166487187 280030807804947420249730781)
        ·
          refine ⟨105011552926855282593649043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280030807804947420249730781 105011552926855282593649043)
          ·
            refine ⟨157517329390282923890473565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105011552926855282593649043 157517329390282923890473565)
            ·
              refine ⟨59068998521356096458927587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157517329390282923890473565 59068998521356096458927587)
              ·
                refine ⟨88603497782034144688391381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59068998521356096458927587 88603497782034144688391381)
                ·
                  refine ⟨2076644479266425266134173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88603497782034144688391381 2076644479266425266134173)
                  ·
                    refine ⟨778741679724909474800315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076644479266425266134173 778741679724909474800315)
                    ·
                      rfl

theorem cell22_2274891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].length) (baseStart_2274891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274891 prefixEnd_2274891 := by exact prefixLift 2274891
  have htrace : WordTrace (prefixWord ++ tailWord_2274891) baseStart_2274891 baseEnd_2274891 := by
    simpa [prefixWord, tailWord_2274891, baseEnd_2274891] using wordTrace_append hprefix tailTrace_2274891
  have hstable : (prefixWord ++ tailWord_2274891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274891).length < 2 ^ (prefixWord ++ tailWord_2274891).sum := by decide
  have hdescent : baseEnd_2274891 < baseStart_2274891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274893 : List Nat := [1, 6, 1, 1, 3, 1, 9]
def baseStart_2274893 : Nat := 118140960795 + 2274893 * 2 ^ 59
def prefixEnd_2274893 : Nat := 4983230072969 + 3 ^ 40 * 2274893 * 2
def baseEnd_2274893 : Nat := 28842309791325264305567

theorem tailTrace_2274893 : CollatzResearch.WordTrace tailWord_2274893 prefixEnd_2274893 28842309791325264305567 := by
  unfold tailWord_2274893
  simp only [CollatzResearch.WordTrace]
  refine ⟨82972164147458656637789333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55314776098305771091859555 82972164147458656637789333)
  ·
    refine ⟨3889320194412124529896375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82972164147458656637789333 3889320194412124529896375)
    ·
      refine ⟨5833980291618186794844563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889320194412124529896375 5833980291618186794844563)
      ·
        refine ⟨8750970437427280192266845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833980291618186794844563 8750970437427280192266845)
        ·
          refine ⟨3281613914035230072100067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8750970437427280192266845 3281613914035230072100067)
          ·
            refine ⟨4922420871052845108150101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281613914035230072100067 4922420871052845108150101)
            ·
              refine ⟨28842309791325264305567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4922420871052845108150101 28842309791325264305567)
              ·
                rfl

theorem cell22_2274893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 9].length) (baseStart_2274893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274893 prefixEnd_2274893 := by exact prefixLift 2274893
  have htrace : WordTrace (prefixWord ++ tailWord_2274893) baseStart_2274893 baseEnd_2274893 := by
    simpa [prefixWord, tailWord_2274893, baseEnd_2274893] using wordTrace_append hprefix tailTrace_2274893
  have hstable : (prefixWord ++ tailWord_2274893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274893).length < 2 ^ (prefixWord ++ tailWord_2274893).sum := by decide
  have hdescent : baseEnd_2274893 < baseStart_2274893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274921 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 5]
def baseStart_2274921 : Nat := 118140960795 + 2274921 * 2 ^ 59
def prefixEnd_2274921 : Nat := 4983230072969 + 3 ^ 40 * 2274921 * 2
def baseEnd_2274921 : Nat := 259583983112666465516741

theorem tailTrace_2274921 : CollatzResearch.WordTrace tailWord_2274921 prefixEnd_2274921 259583983112666465516741 := by
  unfold tailWord_2274921
  simp only [CollatzResearch.WordTrace]
  refine ⟨82973185391357217419808617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55315456927571478279872411 82973185391357217419808617)
  ·
    refine ⟨62229889043517913064856463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82973185391357217419808617 62229889043517913064856463)
    ·
      refine ⟨93344833565276869597284695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62229889043517913064856463 93344833565276869597284695)
      ·
        refine ⟨140017250347915304395927043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93344833565276869597284695 140017250347915304395927043)
        ·
          refine ⟨210025875521872956593890565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140017250347915304395927043 210025875521872956593890565)
          ·
            refine ⟨39379851660351179361354481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210025875521872956593890565 39379851660351179361354481)
            ·
              refine ⟨29534888745263384521015861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39379851660351179361354481 29534888745263384521015861)
              ·
                refine ⟨2768895819868442298845237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29534888745263384521015861 2768895819868442298845237)
                ·
                  refine ⟨259583983112666465516741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768895819868442298845237 259583983112666465516741)
                  ·
                    rfl

theorem cell22_2274921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_2274921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274921 prefixEnd_2274921 := by exact prefixLift 2274921
  have htrace : WordTrace (prefixWord ++ tailWord_2274921) baseStart_2274921 baseEnd_2274921 := by
    simpa [prefixWord, tailWord_2274921, baseEnd_2274921] using wordTrace_append hprefix tailTrace_2274921
  have hstable : (prefixWord ++ tailWord_2274921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274921).length < 2 ^ (prefixWord ++ tailWord_2274921).sum := by decide
  have hdescent : baseEnd_2274921 < baseStart_2274921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274972 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_2274972 : Nat := 118140960795 + 2274972 * 2 ^ 59
def prefixEnd_2274972 : Nat := 4983230072969 + 3 ^ 40 * 2274972 * 2
def baseEnd_2274972 : Nat := 259589802560084087841689

theorem tailTrace_2274972 : CollatzResearch.WordTrace tailWord_2274972 prefixEnd_2274972 259589802560084087841689 := by
  unfold tailWord_2274972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41487522757086226564957585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55316697009448302086610113 41487522757086226564957585)
  ·
    refine ⟨31115642067814669923718189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41487522757086226564957585 31115642067814669923718189)
    ·
      refine ⟨11668365775430501221394321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31115642067814669923718189 11668365775430501221394321)
      ·
        refine ⟨8751274331572875916045741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11668365775430501221394321 8751274331572875916045741)
        ·
          refine ⟨3281727874339828468517153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8751274331572875916045741 3281727874339828468517153)
          ·
            refine ⟨2461295905754871351387865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3281727874339828468517153 2461295905754871351387865)
            ·
              refine ⟨1845971929316153513540899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461295905754871351387865 1845971929316153513540899)
              ·
                refine ⟨2768957893974230270311349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845971929316153513540899 2768957893974230270311349)
                ·
                  refine ⟨259589802560084087841689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768957893974230270311349 259589802560084087841689)
                  ·
                    rfl

theorem cell22_2274972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_2274972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2274972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2274972 prefixEnd_2274972 := by exact prefixLift 2274972
  have htrace : WordTrace (prefixWord ++ tailWord_2274972) baseStart_2274972 baseEnd_2274972 := by
    simpa [prefixWord, tailWord_2274972, baseEnd_2274972] using wordTrace_append hprefix tailTrace_2274972
  have hstable : (prefixWord ++ tailWord_2274972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274972).length < 2 ^ (prefixWord ++ tailWord_2274972).sum := by decide
  have hdescent : baseEnd_2274972 < baseStart_2274972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275010 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2275010 : Nat := 118140960795 + 2275010 * 2 ^ 59
def prefixEnd_2275010 : Nat := 4983230072969 + 3 ^ 40 * 2275010 * 2
def baseEnd_2275010 : Nat := 778782415856832831074951

theorem tailTrace_2275010 : CollatzResearch.WordTrace tailWord_2275010 prefixEnd_2275010 778782415856832831074951 := by
  unfold tailWord_2275010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744107872008696404949621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55317620992023190413198989 20744107872008696404949621)
  ·
    refine ⟨1944760113000815287964027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20744107872008696404949621 1944760113000815287964027)
    ·
      refine ⟨2917140169501222931946041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944760113000815287964027 2917140169501222931946041)
      ·
        refine ⟨2187855127125917198959531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2917140169501222931946041 2187855127125917198959531)
        ·
          refine ⟨3281782690688875798439297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187855127125917198959531 3281782690688875798439297)
          ·
            refine ⟨2461337018016656848829473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3281782690688875798439297 2461337018016656848829473)
            ·
              refine ⟨1846002763512492636622105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461337018016656848829473 1846002763512492636622105)
              ·
                refine ⟨1384502072634369477466579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846002763512492636622105 1384502072634369477466579)
                ·
                  refine ⟨2076753108951554216199869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384502072634369477466579 2076753108951554216199869)
                  ·
                    refine ⟨778782415856832831074951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076753108951554216199869 778782415856832831074951)
                    ·
                      rfl

theorem cell22_2275010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2275010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275010 prefixEnd_2275010 := by exact prefixLift 2275010
  have htrace : WordTrace (prefixWord ++ tailWord_2275010) baseStart_2275010 baseEnd_2275010 := by
    simpa [prefixWord, tailWord_2275010, baseEnd_2275010] using wordTrace_append hprefix tailTrace_2275010
  have hstable : (prefixWord ++ tailWord_2275010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275010).length < 2 ^ (prefixWord ++ tailWord_2275010).sum := by decide
  have hdescent : baseEnd_2275010 < baseStart_2275010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275015 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2275015 : Nat := 118140960795 + 2275015 * 2 ^ 59
def prefixEnd_2275015 : Nat := 4983230072969 + 3 ^ 40 * 2275015 * 2
def baseEnd_2275015 : Nat := 778784127459014484699935

theorem tailTrace_2275015 : CollatzResearch.WordTrace tailWord_2275015 prefixEnd_2275015 778784127459014484699935 := by
  unfold tailWord_2275015
  simp only [CollatzResearch.WordTrace]
  refine ⟨82976613853016671473730499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55317742568677780982486999 82976613853016671473730499)
  ·
    refine ⟨124464920779525007210595749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82976613853016671473730499 124464920779525007210595749)
    ·
      refine ⟨23337172646160938851986703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124464920779525007210595749 23337172646160938851986703)
      ·
        refine ⟨35005758969241408277980055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23337172646160938851986703 35005758969241408277980055)
        ·
          refine ⟨52508638453862112416970083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35005758969241408277980055 52508638453862112416970083)
          ·
            refine ⟨78762957680793168625455125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52508638453862112416970083 78762957680793168625455125)
            ·
              refine ⟨3692013641287179779318209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78762957680793168625455125 3692013641287179779318209)
              ·
                refine ⟨2769010230965384834488657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692013641287179779318209 2769010230965384834488657)
                ·
                  refine ⟨2076757673224038625866493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2769010230965384834488657 2076757673224038625866493)
                  ·
                    refine ⟨778784127459014484699935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076757673224038625866493 778784127459014484699935)
                    ·
                      rfl

theorem cell22_2275015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2275015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275015 prefixEnd_2275015 := by exact prefixLift 2275015
  have htrace : WordTrace (prefixWord ++ tailWord_2275015) baseStart_2275015 baseEnd_2275015 := by
    simpa [prefixWord, tailWord_2275015, baseEnd_2275015] using wordTrace_append hprefix tailTrace_2275015
  have hstable : (prefixWord ++ tailWord_2275015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275015).length < 2 ^ (prefixWord ++ tailWord_2275015).sum := by decide
  have hdescent : baseEnd_2275015 < baseStart_2275015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275182 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2275182 : Nat := 118140960795 + 2275182 * 2 ^ 59
def prefixEnd_2275182 : Nat := 4983230072969 + 3 ^ 40 * 2275182 * 2
def baseEnd_2275182 : Nat := 778841294971881715774423

theorem tailTrace_2275182 : CollatzResearch.WordTrace tailWord_2275182 prefixEnd_2275182 778841294971881715774423 := by
  unfold tailWord_2275182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372838105426457374382475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55321803228941105996706533 10372838105426457374382475)
  ·
    refine ⟨15559257158139686061573713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10372838105426457374382475 15559257158139686061573713)
    ·
      refine ⟨11669442868604764546180285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15559257158139686061573713 11669442868604764546180285)
      ·
        refine ⟨4376041075726786704817607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11669442868604764546180285 4376041075726786704817607)
        ·
          refine ⟨6564061613590180057226411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376041075726786704817607 6564061613590180057226411)
          ·
            refine ⟨9846092420385270085839617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564061613590180057226411 9846092420385270085839617)
            ·
              refine ⟨7384569315288952564379713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9846092420385270085839617 7384569315288952564379713)
              ·
                refine ⟨5538426986466714423284785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384569315288952564379713 5538426986466714423284785)
                ·
                  refine ⟨4153820239850035817463589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538426986466714423284785 4153820239850035817463589)
                  ·
                    refine ⟨778841294971881715774423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153820239850035817463589 778841294971881715774423)
                    ·
                      rfl

theorem cell22_2275182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2275182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275182 prefixEnd_2275182 := by exact prefixLift 2275182
  have htrace : WordTrace (prefixWord ++ tailWord_2275182) baseStart_2275182 baseEnd_2275182 := by
    simpa [prefixWord, tailWord_2275182, baseEnd_2275182] using wordTrace_append hprefix tailTrace_2275182
  have hstable : (prefixWord ++ tailWord_2275182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275182).length < 2 ^ (prefixWord ++ tailWord_2275182).sum := by decide
  have hdescent : baseEnd_2275182 < baseStart_2275182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275193 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_2275193 : Nat := 118140960795 + 2275193 * 2 ^ 59
def prefixEnd_2275193 : Nat := 4983230072969 + 3 ^ 40 * 2275193 * 2
def baseEnd_2275193 : Nat := 778845060496681353749389

theorem tailTrace_2275193 : CollatzResearch.WordTrace tailWord_2275193 prefixEnd_2275193 778845060496681353749389 := by
  unfold tailWord_2275193
  simp only [CollatzResearch.WordTrace]
  refine ⟨82983106046371807873710233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55322070697581205249140155 82983106046371807873710233)
  ·
    refine ⟨62237329534778855905282675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82983106046371807873710233 62237329534778855905282675)
    ·
      refine ⟨93355994302168283857924013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62237329534778855905282675 93355994302168283857924013)
      ·
        refine ⟨35008497863313106446721505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93355994302168283857924013 35008497863313106446721505)
        ·
          refine ⟨26256373397484829835041129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35008497863313106446721505 26256373397484829835041129)
          ·
            refine ⟨19692280048113622376280847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26256373397484829835041129 19692280048113622376280847)
            ·
              refine ⟨29538420072170433564421271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19692280048113622376280847 29538420072170433564421271)
              ·
                refine ⟨44307630108255650346631907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29538420072170433564421271 44307630108255650346631907)
                ·
                  refine ⟨66461445162383475519947861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44307630108255650346631907 66461445162383475519947861)
                  ·
                    refine ⟨778845060496681353749389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66461445162383475519947861 778845060496681353749389)
                    ·
                      rfl

theorem cell22_2275193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_2275193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275193 prefixEnd_2275193 := by exact prefixLift 2275193
  have htrace : WordTrace (prefixWord ++ tailWord_2275193) baseStart_2275193 baseEnd_2275193 := by
    simpa [prefixWord, tailWord_2275193, baseEnd_2275193] using wordTrace_append hprefix tailTrace_2275193
  have hstable : (prefixWord ++ tailWord_2275193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275193).length < 2 ^ (prefixWord ++ tailWord_2275193).sum := by decide
  have hdescent : baseEnd_2275193 < baseStart_2275193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275195 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 3, 3]
def baseStart_2275195 : Nat := 118140960795 + 2275195 * 2 ^ 59
def prefixEnd_2275195 : Nat := 4983230072969 + 3 ^ 40 * 2275195 * 2
def baseEnd_2275195 : Nat := 778845745137554015199383

theorem tailTrace_2275195 : CollatzResearch.WordTrace tailWord_2275195 prefixEnd_2275195 778845745137554015199383 := by
  unfold tailWord_2275195
  simp only [CollatzResearch.WordTrace]
  refine ⟨82983178992364562215283039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55322119328243041476855359 82983178992364562215283039)
  ·
    refine ⟨124474768488546843322924559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82983178992364562215283039 124474768488546843322924559)
    ·
      refine ⟨186712152732820264984386839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124474768488546843322924559 186712152732820264984386839)
      ·
        refine ⟨280068229099230397476580259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186712152732820264984386839 280068229099230397476580259)
        ·
          refine ⟨420102343648845596214870389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280068229099230397476580259 420102343648845596214870389)
          ·
            refine ⟨39384594717079274645144099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 420102343648845596214870389 39384594717079274645144099)
            ·
              refine ⟨59076892075618911967716149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39384594717079274645144099 59076892075618911967716149)
              ·
                refine ⟨5538458632089272996973389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59076892075618911967716149 5538458632089272996973389)
                ·
                  refine ⟨2076921987033477373865021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5538458632089272996973389 2076921987033477373865021)
                  ·
                    refine ⟨778845745137554015199383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076921987033477373865021 778845745137554015199383)
                    ·
                      rfl

theorem cell22_2275195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].length) (baseStart_2275195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275195 prefixEnd_2275195 := by exact prefixLift 2275195
  have htrace : WordTrace (prefixWord ++ tailWord_2275195) baseStart_2275195 baseEnd_2275195 := by
    simpa [prefixWord, tailWord_2275195, baseEnd_2275195] using wordTrace_append hprefix tailTrace_2275195
  have hstable : (prefixWord ++ tailWord_2275195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275195).length < 2 ^ (prefixWord ++ tailWord_2275195).sum := by decide
  have hdescent : baseEnd_2275195 < baseStart_2275195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275214 : List Nat := [4, 1, 1, 5, 1, 1, 3, 6]
def baseStart_2275214 : Nat := 118140960795 + 2275214 * 2 ^ 59
def prefixEnd_2275214 : Nat := 4983230072969 + 3 ^ 40 * 2275214 * 2
def baseEnd_2275214 : Nat := 86539138802871588774925

theorem tailTrace_2275214 : CollatzResearch.WordTrace tailWord_2275214 prefixEnd_2275214 86539138802871588774925 := by
  unfold tailWord_2275214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372983997411966057528087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55322581319530485640149797 10372983997411966057528087)
  ·
    refine ⟨15559475996117949086292131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10372983997411966057528087 15559475996117949086292131)
    ·
      refine ⟨23339213994176923629438197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559475996117949086292131 23339213994176923629438197)
      ·
        refine ⟨2188051311954086590259831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23339213994176923629438197 2188051311954086590259831)
        ·
          refine ⟨3282076967931129885389747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188051311954086590259831 3282076967931129885389747)
          ·
            refine ⟨4923115451896694828084621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282076967931129885389747 4923115451896694828084621)
            ·
              refine ⟨1846168294461260560531733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4923115451896694828084621 1846168294461260560531733)
              ·
                refine ⟨86539138802871588774925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1846168294461260560531733 86539138802871588774925)
                ·
                  rfl

theorem cell22_2275214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_2275214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275214 prefixEnd_2275214 := by exact prefixLift 2275214
  have htrace : WordTrace (prefixWord ++ tailWord_2275214) baseStart_2275214 baseEnd_2275214 := by
    simpa [prefixWord, tailWord_2275214, baseEnd_2275214] using wordTrace_append hprefix tailTrace_2275214
  have hstable : (prefixWord ++ tailWord_2275214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275214).length < 2 ^ (prefixWord ++ tailWord_2275214).sum := by decide
  have hdescent : baseEnd_2275214 < baseStart_2275214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275229 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2275229 : Nat := 118140960795 + 2275229 * 2 ^ 59
def prefixEnd_2275229 : Nat := 4983230072969 + 3 ^ 40 * 2275229 * 2
def baseEnd_2275229 : Nat := 778857384032389259849279

theorem tailTrace_2275229 : CollatzResearch.WordTrace tailWord_2275229 prefixEnd_2275229 778857384032389259849279 := by
  unfold tailWord_2275229
  simp only [CollatzResearch.WordTrace]
  refine ⟨82984419074241386022020741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55322946049494257348013827 82984419074241386022020741)
  ·
    refine ⟨15559578576420259879128889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82984419074241386022020741 15559578576420259879128889)
    ·
      refine ⟨11669683932315194909346667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15559578576420259879128889 11669683932315194909346667)
      ·
        refine ⟨17504525898472792364020001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11669683932315194909346667 17504525898472792364020001)
        ·
          refine ⟨13128394423854594273015001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17504525898472792364020001 13128394423854594273015001)
          ·
            refine ⟨9846295817890945704761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13128394423854594273015001 9846295817890945704761251)
            ·
              refine ⟨14769443726836418557141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9846295817890945704761251 14769443726836418557141877)
              ·
                refine ⟨1384635349390914239732051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14769443726836418557141877 1384635349390914239732051)
                ·
                  refine ⟨2076953024086371359598077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384635349390914239732051 2076953024086371359598077)
                  ·
                    refine ⟨778857384032389259849279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076953024086371359598077 778857384032389259849279)
                    ·
                      rfl

theorem cell22_2275229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2275229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275229 prefixEnd_2275229 := by exact prefixLift 2275229
  have htrace : WordTrace (prefixWord ++ tailWord_2275229) baseStart_2275229 baseEnd_2275229 := by
    simpa [prefixWord, tailWord_2275229, baseEnd_2275229] using wordTrace_append hprefix tailTrace_2275229
  have hstable : (prefixWord ++ tailWord_2275229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275229).length < 2 ^ (prefixWord ++ tailWord_2275229).sum := by decide
  have hdescent : baseEnd_2275229 < baseStart_2275229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275272 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2275272 : Nat := 118140960795 + 2275272 * 2 ^ 59
def prefixEnd_2275272 : Nat := 4983230072969 + 3 ^ 40 * 2275272 * 2
def baseEnd_2275272 : Nat := 778872103811151481024147

theorem tailTrace_2275272 : CollatzResearch.WordTrace tailWord_2275272 prefixEnd_2275272 778872103811151481024147 := by
  unfold tailWord_2275272
  simp only [CollatzResearch.WordTrace]
  refine ⟨41492993706542802182918035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55323991608723736243890713 41492993706542802182918035)
  ·
    refine ⟨62239490559814203274377053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41492993706542802182918035 62239490559814203274377053)
    ·
      refine ⟨23339808959930326227891395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62239490559814203274377053 23339808959930326227891395)
      ·
        refine ⟨35009713439895489341837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23339808959930326227891395 35009713439895489341837093)
        ·
          refine ⟨6564321269980404251594455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35009713439895489341837093 6564321269980404251594455)
          ·
            refine ⟨9846481904970606377391683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564321269980404251594455 9846481904970606377391683)
            ·
              refine ⟨14769722857455909566087525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9846481904970606377391683 14769722857455909566087525)
              ·
                refine ⟨2769323035772983043641411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14769722857455909566087525 2769323035772983043641411)
                ·
                  refine ⟨4153984553659474565462117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769323035772983043641411 4153984553659474565462117)
                  ·
                    refine ⟨778872103811151481024147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153984553659474565462117 778872103811151481024147)
                    ·
                      rfl

theorem cell22_2275272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2275272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275272 prefixEnd_2275272 := by exact prefixLift 2275272
  have htrace : WordTrace (prefixWord ++ tailWord_2275272) baseStart_2275272 baseEnd_2275272 := by
    simpa [prefixWord, tailWord_2275272, baseEnd_2275272] using wordTrace_append hprefix tailTrace_2275272
  have hstable : (prefixWord ++ tailWord_2275272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275272).length < 2 ^ (prefixWord ++ tailWord_2275272).sum := by decide
  have hdescent : baseEnd_2275272 < baseStart_2275272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275377 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 5]
def baseStart_2275377 : Nat := 118140960795 + 2275377 * 2 ^ 59
def prefixEnd_2275377 : Nat := 4983230072969 + 3 ^ 40 * 2275377 * 2
def baseEnd_2275377 : Nat := 259636015818988735716275

theorem tailTrace_2275377 : CollatzResearch.WordTrace tailWord_2275377 prefixEnd_2275377 259636015818988735716275 := by
  unfold tailWord_2275377
  simp only [CollatzResearch.WordTrace]
  refine ⟨82989817077705207298408385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55326544718470138198938923 82989817077705207298408385)
  ·
    refine ⟨62242362808278905473806289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82989817077705207298408385 62242362808278905473806289)
    ·
      refine ⟨46681772106209179105354717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62242362808278905473806289 46681772106209179105354717)
      ·
        refine ⟨17505664539828442164508019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46681772106209179105354717 17505664539828442164508019)
        ·
          refine ⟨26258496809742663246762029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505664539828442164508019 26258496809742663246762029)
          ·
            refine ⟨9846936303653498717535761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26258496809742663246762029 9846936303653498717535761)
            ·
              refine ⟨7385202227740124038151821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9846936303653498717535761 7385202227740124038151821)
              ·
                refine ⟨2769450835402546514306933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7385202227740124038151821 2769450835402546514306933)
                ·
                  refine ⟨259636015818988735716275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2769450835402546514306933 259636015818988735716275)
                  ·
                    rfl

theorem cell22_2275377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_2275377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275377 prefixEnd_2275377 := by exact prefixLift 2275377
  have htrace : WordTrace (prefixWord ++ tailWord_2275377) baseStart_2275377 baseEnd_2275377 := by
    simpa [prefixWord, tailWord_2275377, baseEnd_2275377] using wordTrace_append hprefix tailTrace_2275377
  have hstable : (prefixWord ++ tailWord_2275377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275377).length < 2 ^ (prefixWord ++ tailWord_2275377).sum := by decide
  have hdescent : baseEnd_2275377 < baseStart_2275377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275407 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 1, 4]
def baseStart_2275407 : Nat := 118140960795 + 2275407 * 2 ^ 59
def prefixEnd_2275407 : Nat := 4983230072969 + 3 ^ 40 * 2275407 * 2
def baseEnd_2275407 : Nat := 778918317070056128898733

theorem tailTrace_2275407 : CollatzResearch.WordTrace tailWord_2275407 prefixEnd_2275407 778918317070056128898733 := by
  unfold tailWord_2275407
  simp only [CollatzResearch.WordTrace]
  refine ⟨82990911267596522422000475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55327274178397681614666983 82990911267596522422000475)
  ·
    refine ⟨124486366901394783633000713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82990911267596522422000475 124486366901394783633000713)
    ·
      refine ⟨93364775176046087724750535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124486366901394783633000713 93364775176046087724750535)
      ·
        refine ⟨140047162764069131587125803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93364775176046087724750535 140047162764069131587125803)
        ·
          refine ⟨210070744146103697380688705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140047162764069131587125803 210070744146103697380688705)
          ·
            refine ⟨157553058109577773035516529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210070744146103697380688705 157553058109577773035516529)
            ·
              refine ⟨118164793582183329776637397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157553058109577773035516529 118164793582183329776637397)
              ·
                refine ⟨2769487349582421791639939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118164793582183329776637397 2769487349582421791639939)
                ·
                  refine ⟨4154231024373632687459909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769487349582421791639939 4154231024373632687459909)
                  ·
                    refine ⟨778918317070056128898733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154231024373632687459909 778918317070056128898733)
                    ·
                      rfl

theorem cell22_2275407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_2275407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275407 prefixEnd_2275407 := by exact prefixLift 2275407
  have htrace : WordTrace (prefixWord ++ tailWord_2275407) baseStart_2275407 baseEnd_2275407 := by
    simpa [prefixWord, tailWord_2275407, baseEnd_2275407] using wordTrace_append hprefix tailTrace_2275407
  have hstable : (prefixWord ++ tailWord_2275407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275407).length < 2 ^ (prefixWord ++ tailWord_2275407).sum := by decide
  have hdescent : baseEnd_2275407 < baseStart_2275407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275452 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2275452 : Nat := 118140960795 + 2275452 * 2 ^ 59
def prefixEnd_2275452 : Nat := 4983230072969 + 3 ^ 40 * 2275452 * 2
def baseEnd_2275452 : Nat := 778933721489691011523595

theorem tailTrace_2275452 : CollatzResearch.WordTrace tailWord_2275452 prefixEnd_2275452 778933721489691011523595 := by
  unfold tailWord_2275452
  simp only [CollatzResearch.WordTrace]
  refine ⟨41496276276216747553694305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55328368368288996738259073 41496276276216747553694305)
  ·
    refine ⟨31122207207162560665270729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41496276276216747553694305 31122207207162560665270729)
    ·
      refine ⟨23341655405371920498953047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31122207207162560665270729 23341655405371920498953047)
      ·
        refine ⟨35012483108057880748429571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23341655405371920498953047 35012483108057880748429571)
        ·
          refine ⟨52518724662086821122644357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35012483108057880748429571 52518724662086821122644357)
          ·
            refine ⟨9847260874141278960495817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52518724662086821122644357 9847260874141278960495817)
            ·
              refine ⟨7385445655605959220371863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9847260874141278960495817 7385445655605959220371863)
              ·
                refine ⟨11078168483408938830557795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7385445655605959220371863 11078168483408938830557795)
                ·
                  refine ⟨16617252725113408245836693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11078168483408938830557795 16617252725113408245836693)
                  ·
                    refine ⟨778933721489691011523595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16617252725113408245836693 778933721489691011523595)
                    ·
                      rfl

theorem cell22_2275452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2275452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275452 prefixEnd_2275452 := by exact prefixLift 2275452
  have htrace : WordTrace (prefixWord ++ tailWord_2275452) baseStart_2275452 baseEnd_2275452 := by
    simpa [prefixWord, tailWord_2275452, baseEnd_2275452] using wordTrace_append hprefix tailTrace_2275452
  have hstable : (prefixWord ++ tailWord_2275452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275452).length < 2 ^ (prefixWord ++ tailWord_2275452).sum := by decide
  have hdescent : baseEnd_2275452 < baseStart_2275452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275488 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_2275488 : Nat := 118140960795 + 2275488 * 2 ^ 59
def prefixEnd_2275488 : Nat := 4983230072969 + 3 ^ 40 * 2275488 * 2
def baseEnd_2275488 : Nat := 778946045025398917623485

theorem tailTrace_2275488 : CollatzResearch.WordTrace tailWord_2275488 prefixEnd_2275488 778946045025398917623485 := by
  unfold tailWord_2275488
  simp only [CollatzResearch.WordTrace]
  refine ⟨41496932790151536627849559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55329243720202048837132745 41496932790151536627849559)
  ·
    refine ⟨62245399185227304941774339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41496932790151536627849559 62245399185227304941774339)
    ·
      refine ⟨93368098777840957412661509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62245399185227304941774339 93368098777840957412661509)
      ·
        refine ⟨17506518520845179514874033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93368098777840957412661509 17506518520845179514874033)
        ·
          refine ⟨13129888890633884636155525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17506518520845179514874033 13129888890633884636155525)
          ·
            refine ⟨2461854166993853369279161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13129888890633884636155525 2461854166993853369279161)
            ·
              refine ⟨1846390625245390026959371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461854166993853369279161 1846390625245390026959371)
              ·
                refine ⟨2769585937868085040439057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846390625245390026959371 2769585937868085040439057)
                ·
                  refine ⟨2077189453401063780329293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2769585937868085040439057 2077189453401063780329293)
                  ·
                    refine ⟨778946045025398917623485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077189453401063780329293 778946045025398917623485)
                    ·
                      rfl

theorem cell22_2275488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_2275488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275488 prefixEnd_2275488 := by exact prefixLift 2275488
  have htrace : WordTrace (prefixWord ++ tailWord_2275488) baseStart_2275488 baseEnd_2275488 := by
    simpa [prefixWord, tailWord_2275488, baseEnd_2275488] using wordTrace_append hprefix tailTrace_2275488
  have hstable : (prefixWord ++ tailWord_2275488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275488).length < 2 ^ (prefixWord ++ tailWord_2275488).sum := by decide
  have hdescent : baseEnd_2275488 < baseStart_2275488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275544 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2275544 : Nat := 118140960795 + 2275544 * 2 ^ 59
def prefixEnd_2275544 : Nat := 4983230072969 + 3 ^ 40 * 2275544 * 2
def baseEnd_2275544 : Nat := 778965214969833438223313

theorem tailTrace_2275544 : CollatzResearch.WordTrace tailWord_2275544 prefixEnd_2275544 778965214969833438223313 := by
  unfold tailWord_2275544
  simp only [CollatzResearch.WordTrace]
  refine ⟨41497954034050097409868843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55330605378733463213158457 41497954034050097409868843)
  ·
    refine ⟨62246931051075146114803265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41497954034050097409868843 62246931051075146114803265)
    ·
      refine ⟨46685198288306359586102449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62246931051075146114803265 46685198288306359586102449)
      ·
        refine ⟨35013898716229769689576837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46685198288306359586102449 35013898716229769689576837)
        ·
          refine ⟨6565106009293081816795657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35013898716229769689576837 6565106009293081816795657)
          ·
            refine ⟨4923829506969811362596743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6565106009293081816795657 4923829506969811362596743)
            ·
              refine ⟨7385744260454717043895115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923829506969811362596743 7385744260454717043895115)
              ·
                refine ⟨11078616390682075565842673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7385744260454717043895115 11078616390682075565842673)
                ·
                  refine ⟨8308962293011556674382005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11078616390682075565842673 8308962293011556674382005)
                  ·
                    refine ⟨778965214969833438223313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8308962293011556674382005 778965214969833438223313)
                    ·
                      rfl

theorem cell22_2275544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2275544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275544 prefixEnd_2275544 := by exact prefixLift 2275544
  have htrace : WordTrace (prefixWord ++ tailWord_2275544) baseStart_2275544 baseEnd_2275544 := by
    simpa [prefixWord, tailWord_2275544, baseEnd_2275544] using wordTrace_append hprefix tailTrace_2275544
  have hstable : (prefixWord ++ tailWord_2275544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275544).length < 2 ^ (prefixWord ++ tailWord_2275544).sum := by decide
  have hdescent : baseEnd_2275544 < baseStart_2275544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275636 : List Nat := [2, 5, 1, 1, 1, 4, 8]
def baseStart_2275636 : Nat := 118140960795 + 2275636 * 2 ^ 59
def prefixEnd_2275636 : Nat := 4983230072969 + 3 ^ 40 * 2275636 * 2
def baseEnd_2275636 : Nat := 28851729942591698700853

theorem tailTrace_2275636 : CollatzResearch.WordTrace tailWord_2275636 prefixEnd_2275636 28851729942591698700853 := by
  unfold tailWord_2275636
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499631791883447266043381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55332842389177929688057841 41499631791883447266043381)
  ·
    refine ⟨3890590480489073181191567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41499631791883447266043381 3890590480489073181191567)
    ·
      refine ⟨5835885720733609771787351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890590480489073181191567 5835885720733609771787351)
      ·
        refine ⟨8753828581100414657681027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835885720733609771787351 8753828581100414657681027)
        ·
          refine ⟨13130742871650621986521541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753828581100414657681027 13130742871650621986521541)
          ·
            refine ⟨2462014288434491622472789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13130742871650621986521541 2462014288434491622472789)
            ·
              refine ⟨28851729942591698700853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2462014288434491622472789 28851729942591698700853)
              ·
                rfl

theorem cell22_2275636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 8].length) (baseStart_2275636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275636 prefixEnd_2275636 := by exact prefixLift 2275636
  have htrace : WordTrace (prefixWord ++ tailWord_2275636) baseStart_2275636 baseEnd_2275636 := by
    simpa [prefixWord, tailWord_2275636, baseEnd_2275636] using wordTrace_append hprefix tailTrace_2275636
  have hstable : (prefixWord ++ tailWord_2275636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275636).length < 2 ^ (prefixWord ++ tailWord_2275636).sum := by decide
  have hdescent : baseEnd_2275636 < baseStart_2275636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275651 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 3, 3]
def baseStart_2275651 : Nat := 118140960795 + 2275651 * 2 ^ 59
def prefixEnd_2275651 : Nat := 4983230072969 + 3 ^ 40 * 2275651 * 2
def baseEnd_2275651 : Nat := 779001843256520825797985

theorem tailTrace_2275651 : CollatzResearch.WordTrace tailWord_2275651 prefixEnd_2275651 779001843256520825797985 := by
  unfold tailWord_2275651
  simp only [CollatzResearch.WordTrace]
  refine ⟨82999810678712552093882807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55333207119141701395921871 82999810678712552093882807)
  ·
    refine ⟨124499716018068828140824211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82999810678712552093882807 124499716018068828140824211)
    ·
      refine ⟨186749574027103242211236317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124499716018068828140824211 186749574027103242211236317)
      ·
        refine ⟨70031090260163715829213619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186749574027103242211236317 70031090260163715829213619)
        ·
          refine ⟨105046635390245573743820429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70031090260163715829213619 105046635390245573743820429)
          ·
            refine ⟨39392488271342090153932661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105046635390245573743820429 39392488271342090153932661)
            ·
              refine ⟨3693045775438320951931187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39392488271342090153932661 3693045775438320951931187)
              ·
                refine ⟨5539568663157481427896781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693045775438320951931187 5539568663157481427896781)
                ·
                  refine ⟨2077338248684055535461293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5539568663157481427896781 2077338248684055535461293)
                  ·
                    refine ⟨779001843256520825797985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077338248684055535461293 779001843256520825797985)
                    ·
                      rfl

theorem cell22_2275651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].length) (baseStart_2275651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275651 prefixEnd_2275651 := by exact prefixLift 2275651
  have htrace : WordTrace (prefixWord ++ tailWord_2275651) baseStart_2275651 baseEnd_2275651 := by
    simpa [prefixWord, tailWord_2275651, baseEnd_2275651] using wordTrace_append hprefix tailTrace_2275651
  have hstable : (prefixWord ++ tailWord_2275651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275651).length < 2 ^ (prefixWord ++ tailWord_2275651).sum := by decide
  have hdescent : baseEnd_2275651 < baseStart_2275651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275726 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2275726 : Nat := 118140960795 + 2275726 * 2 ^ 59
def prefixEnd_2275726 : Nat := 4983230072969 + 3 ^ 40 * 2275726 * 2
def baseEnd_2275726 : Nat := 259675839096415210057585

theorem tailTrace_2275726 : CollatzResearch.WordTrace tailWord_2275726 prefixEnd_2275726 259675839096415210057585 := by
  unfold tailWord_2275726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375318269180104987857879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55335030768960559935242021 10375318269180104987857879)
  ·
    refine ⟨15562977403770157481786819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10375318269180104987857879 15562977403770157481786819)
    ·
      refine ⟨23344466105655236222680229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15562977403770157481786819 23344466105655236222680229)
      ·
        refine ⟨4377087394810356791752543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23344466105655236222680229 4377087394810356791752543)
        ·
          refine ⟨6565631092215535187628815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377087394810356791752543 6565631092215535187628815)
          ·
            refine ⟨9848446638323302781443223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565631092215535187628815 9848446638323302781443223)
            ·
              refine ⟨14772669957484954172164835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848446638323302781443223 14772669957484954172164835)
              ·
                refine ⟨22159004936227431258247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14772669957484954172164835 22159004936227431258247253)
                ·
                  refine ⟨259675839096415210057585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22159004936227431258247253 259675839096415210057585)
                  ·
                    rfl

theorem cell22_2275726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2275726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275726 prefixEnd_2275726 := by exact prefixLift 2275726
  have htrace : WordTrace (prefixWord ++ tailWord_2275726) baseStart_2275726 baseEnd_2275726 := by
    simpa [prefixWord, tailWord_2275726, baseEnd_2275726] using wordTrace_append hprefix tailTrace_2275726
  have hstable : (prefixWord ++ tailWord_2275726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275726).length < 2 ^ (prefixWord ++ tailWord_2275726).sum := by decide
  have hdescent : baseEnd_2275726 < baseStart_2275726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275743 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 4]
def baseStart_2275743 : Nat := 118140960795 + 2275743 * 2 ^ 59
def prefixEnd_2275743 : Nat := 4983230072969 + 3 ^ 40 * 2275743 * 2
def baseEnd_2275743 : Nat := 259677778912221084165901

theorem tailTrace_2275743 : CollatzResearch.WordTrace tailWord_2275743 prefixEnd_2275743 259677778912221084165901 := by
  unfold tailWord_2275743
  simp only [CollatzResearch.WordTrace]
  refine ⟨83003166194379251806231883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55335444129586167870821255 83003166194379251806231883)
  ·
    refine ⟨124504749291568877709347825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83003166194379251806231883 124504749291568877709347825)
    ·
      refine ⟨93378561968676658282010869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124504749291568877709347825 93378561968676658282010869)
      ·
        refine ⟨8754240184563436713938519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93378561968676658282010869 8754240184563436713938519)
        ·
          refine ⟨13131360276845155070907779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8754240184563436713938519 13131360276845155070907779)
          ·
            refine ⟨19697040415267732606361669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13131360276845155070907779 19697040415267732606361669)
            ·
              refine ⟨3693195077862699863692813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19697040415267732606361669 3693195077862699863692813)
              ·
                refine ⟨1384948154198512448884805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3693195077862699863692813 1384948154198512448884805)
                ·
                  refine ⟨259677778912221084165901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384948154198512448884805 259677778912221084165901)
                  ·
                    rfl

theorem cell22_2275743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 4].length) (baseStart_2275743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275743 prefixEnd_2275743 := by exact prefixLift 2275743
  have htrace : WordTrace (prefixWord ++ tailWord_2275743) baseStart_2275743 baseEnd_2275743 := by
    simpa [prefixWord, tailWord_2275743, baseEnd_2275743] using wordTrace_append hprefix tailTrace_2275743
  have hstable : (prefixWord ++ tailWord_2275743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275743).length < 2 ^ (prefixWord ++ tailWord_2275743).sum := by decide
  have hdescent : baseEnd_2275743 < baseStart_2275743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275745 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2275745 : Nat := 118140960795 + 2275745 * 2 ^ 59
def prefixEnd_2275745 : Nat := 4983230072969 + 3 ^ 40 * 2275745 * 2
def baseEnd_2275745 : Nat := 779034021377535913947697

theorem tailTrace_2275745 : CollatzResearch.WordTrace tailWord_2275745 prefixEnd_2275745 779034021377535913947697 := by
  unfold tailWord_2275745
  simp only [CollatzResearch.WordTrace]
  refine ⟨83003239140372006147804689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55335492760248004098536459 83003239140372006147804689)
  ·
    refine ⟨62252429355279004610853517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83003239140372006147804689 62252429355279004610853517)
    ·
      refine ⟨23344661008229626729070069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62252429355279004610853517 23344661008229626729070069)
      ·
        refine ⟨2188561969521527505850319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23344661008229626729070069 2188561969521527505850319)
        ·
          refine ⟨3282842954282291258775479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188561969521527505850319 3282842954282291258775479)
          ·
            refine ⟨4924264431423436888163219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282842954282291258775479 4924264431423436888163219)
            ·
              refine ⟨7386396647135155332244829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4924264431423436888163219 7386396647135155332244829)
              ·
                refine ⟨2769898742675683249591811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7386396647135155332244829 2769898742675683249591811)
                ·
                  refine ⟨4154848114013524874387717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769898742675683249591811 4154848114013524874387717)
                  ·
                    refine ⟨779034021377535913947697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154848114013524874387717 779034021377535913947697)
                    ·
                      rfl

theorem cell22_2275745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2275745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275745 prefixEnd_2275745 := by exact prefixLift 2275745
  have htrace : WordTrace (prefixWord ++ tailWord_2275745) baseStart_2275745 baseEnd_2275745 := by
    simpa [prefixWord, tailWord_2275745, baseEnd_2275745] using wordTrace_append hprefix tailTrace_2275745
  have hstable : (prefixWord ++ tailWord_2275745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275745).length < 2 ^ (prefixWord ++ tailWord_2275745).sum := by decide
  have hdescent : baseEnd_2275745 < baseStart_2275745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275794 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2275794 : Nat := 118140960795 + 2275794 * 2 ^ 59
def prefixEnd_2275794 : Nat := 4983230072969 + 3 ^ 40 * 2275794 * 2
def baseEnd_2275794 : Nat := 259683598359638706490849

theorem tailTrace_2275794 : CollatzResearch.WordTrace tailWord_2275794 prefixEnd_2275794 259683598359638706490849 := by
  unfold tailWord_2275794
  simp only [CollatzResearch.WordTrace]
  refine ⟨20751256579298621879084609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55336684211462991677558957 20751256579298621879084609)
  ·
    refine ⟨15563442434473966409313457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20751256579298621879084609 15563442434473966409313457)
    ·
      refine ⟨11672581825855474806985093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15563442434473966409313457 11672581825855474806985093)
      ·
        refine ⟨2188609092347901526309705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11672581825855474806985093 2188609092347901526309705)
        ·
          refine ⟨1641456819260926144732279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188609092347901526309705 1641456819260926144732279)
          ·
            refine ⟨2462185228891389217098419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641456819260926144732279 2462185228891389217098419)
            ·
              refine ⟨3693277843337083825647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462185228891389217098419 3693277843337083825647629)
              ·
                refine ⟨1384979191251406434617861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3693277843337083825647629 1384979191251406434617861)
                ·
                  refine ⟨259683598359638706490849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384979191251406434617861 259683598359638706490849)
                  ·
                    rfl

theorem cell22_2275794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2275794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275794 prefixEnd_2275794 := by exact prefixLift 2275794
  have htrace : WordTrace (prefixWord ++ tailWord_2275794) baseStart_2275794 baseEnd_2275794 := by
    simpa [prefixWord, tailWord_2275794, baseEnd_2275794] using wordTrace_append hprefix tailTrace_2275794
  have hstable : (prefixWord ++ tailWord_2275794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275794).length < 2 ^ (prefixWord ++ tailWord_2275794).sum := by decide
  have hdescent : baseEnd_2275794 < baseStart_2275794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275816 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_2275816 : Nat := 118140960795 + 2275816 * 2 ^ 59
def prefixEnd_2275816 : Nat := 4983230072969 + 3 ^ 40 * 2275816 * 2
def baseEnd_2275816 : Nat := 259686108709505131807493

theorem tailTrace_2275816 : CollatzResearch.WordTrace tailWord_2275816 prefixEnd_2275816 259686108709505131807493 := by
  unfold tailWord_2275816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41502914361557392636819651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55337219148743190182426201 41502914361557392636819651)
  ·
    refine ⟨62254371542336088955229477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41502914361557392636819651 62254371542336088955229477)
    ·
      refine ⟨11672694664188016679105527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62254371542336088955229477 11672694664188016679105527)
      ·
        refine ⟨17509041996282025018658291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11672694664188016679105527 17509041996282025018658291)
        ·
          refine ⟨26263562994423037527987437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17509041996282025018658291 26263562994423037527987437)
          ·
            refine ⟨9848836122908639072995289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26263562994423037527987437 9848836122908639072995289)
            ·
              refine ⟨7386627092181479304746467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9848836122908639072995289 7386627092181479304746467)
              ·
                refine ⟨11079940638272218957119701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7386627092181479304746467 11079940638272218957119701)
                ·
                  refine ⟨259686108709505131807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11079940638272218957119701 259686108709505131807493)
                  ·
                    rfl

theorem cell22_2275816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_2275816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275816 prefixEnd_2275816 := by exact prefixLift 2275816
  have htrace : WordTrace (prefixWord ++ tailWord_2275816) baseStart_2275816 baseEnd_2275816 := by
    simpa [prefixWord, tailWord_2275816, baseEnd_2275816] using wordTrace_append hprefix tailTrace_2275816
  have hstable : (prefixWord ++ tailWord_2275816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275816).length < 2 ^ (prefixWord ++ tailWord_2275816).sum := by decide
  have hdescent : baseEnd_2275816 < baseStart_2275816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275833 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 5]
def baseStart_2275833 : Nat := 118140960795 + 2275833 * 2 ^ 59
def prefixEnd_2275833 : Nat := 4983230072969 + 3 ^ 40 * 2275833 * 2
def baseEnd_2275833 : Nat := 259688048525311005915809

theorem tailTrace_2275833 : CollatzResearch.WordTrace tailWord_2275833 prefixEnd_2275833 259688048525311005915809 := by
  unfold tailWord_2275833
  simp only [CollatzResearch.WordTrace]
  refine ⟨83006448764053197177008153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55337632509368798118005435 83006448764053197177008153)
  ·
    refine ⟨62254836573039897882756115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83006448764053197177008153 62254836573039897882756115)
    ·
      refine ⟨93382254859559846824134173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62254836573039897882756115 93382254859559846824134173)
      ·
        refine ⟨35018345572334942559050315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93382254859559846824134173 35018345572334942559050315)
        ·
          refine ⟨52527518358502413838575473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35018345572334942559050315 52527518358502413838575473)
          ·
            refine ⟨39395638768876810378931605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52527518358502413838575473 39395638768876810378931605)
            ·
              refine ⟨1846670567291100486512419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39395638768876810378931605 1846670567291100486512419)
              ·
                refine ⟨2770005850936650729768629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846670567291100486512419 2770005850936650729768629)
                ·
                  refine ⟨259688048525311005915809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2770005850936650729768629 259688048525311005915809)
                  ·
                    rfl

theorem cell22_2275833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_2275833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275833 prefixEnd_2275833 := by exact prefixLift 2275833
  have htrace : WordTrace (prefixWord ++ tailWord_2275833) baseStart_2275833 baseEnd_2275833 := by
    simpa [prefixWord, tailWord_2275833, baseEnd_2275833] using wordTrace_append hprefix tailTrace_2275833
  have hstable : (prefixWord ++ tailWord_2275833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275833).length < 2 ^ (prefixWord ++ tailWord_2275833).sum := by decide
  have hdescent : baseEnd_2275833 < baseStart_2275833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275891 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_2275891 : Nat := 118140960795 + 2275891 * 2 ^ 59
def prefixEnd_2275891 : Nat := 4983230072969 + 3 ^ 40 * 2275891 * 2
def baseEnd_2275891 : Nat := 779084000161240199797249

theorem tailTrace_2275891 : CollatzResearch.WordTrace tailWord_2275891 prefixEnd_2275891 779084000161240199797249 := by
  unfold tailWord_2275891
  simp only [CollatzResearch.WordTrace]
  refine ⟨83008564197843073082619527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55339042798562048721746351 83008564197843073082619527)
  ·
    refine ⟨124512846296764609623929291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83008564197843073082619527 124512846296764609623929291)
    ·
      refine ⟨186769269445146914435893937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124512846296764609623929291 186769269445146914435893937)
      ·
        refine ⟨140076952083860185826920453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186769269445146914435893937 140076952083860185826920453)
        ·
          refine ⟨26264428515723784842547585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140076952083860185826920453 26264428515723784842547585)
          ·
            refine ⟨19698321386792838631910689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26264428515723784842547585 19698321386792838631910689)
            ·
              refine ⟨14773741040094628973933017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19698321386792838631910689 14773741040094628973933017)
              ·
                refine ⟨11080305780070971730449763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14773741040094628973933017 11080305780070971730449763)
                ·
                  refine ⟨16620458670106457595674645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11080305780070971730449763 16620458670106457595674645)
                  ·
                    refine ⟨779084000161240199797249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16620458670106457595674645 779084000161240199797249)
                    ·
                      rfl

theorem cell22_2275891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_2275891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275891 prefixEnd_2275891 := by exact prefixLift 2275891
  have htrace : WordTrace (prefixWord ++ tailWord_2275891) baseStart_2275891 baseEnd_2275891 := by
    simpa [prefixWord, tailWord_2275891, baseEnd_2275891] using wordTrace_append hprefix tailTrace_2275891
  have hstable : (prefixWord ++ tailWord_2275891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275891).length < 2 ^ (prefixWord ++ tailWord_2275891).sum := by decide
  have hdescent : baseEnd_2275891 < baseStart_2275891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275893 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2275893 : Nat := 118140960795 + 2275893 * 2 ^ 59
def prefixEnd_2275893 : Nat := 4983230072969 + 3 ^ 40 * 2275893 * 2
def baseEnd_2275893 : Nat := 779084684802112861247243

theorem tailTrace_2275893 : CollatzResearch.WordTrace tailWord_2275893 prefixEnd_2275893 779084684802112861247243 := by
  unfold tailWord_2275893
  simp only [CollatzResearch.WordTrace]
  refine ⟨83008637143835827424192333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55339091429223884949461555 83008637143835827424192333)
  ·
    refine ⟨31128238928938435284072125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83008637143835827424192333 31128238928938435284072125)
    ·
      refine ⟨11673089598351913231527047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31128238928938435284072125 11673089598351913231527047)
      ·
        refine ⟨17509634397527869847290571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11673089598351913231527047 17509634397527869847290571)
        ·
          refine ⟨26264451596291804770935857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17509634397527869847290571 26264451596291804770935857)
          ·
            refine ⟨19698338697218853578201893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26264451596291804770935857 19698338697218853578201893)
            ·
              refine ⟨3693438505728535045912855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19698338697218853578201893 3693438505728535045912855)
              ·
                refine ⟨5540157758592802568869283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693438505728535045912855 5540157758592802568869283)
                ·
                  refine ⟨8310236637889203853303925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5540157758592802568869283 8310236637889203853303925)
                  ·
                    refine ⟨779084684802112861247243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8310236637889203853303925 779084684802112861247243)
                    ·
                      rfl

theorem cell22_2275893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2275893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275893 prefixEnd_2275893 := by exact prefixLift 2275893
  have htrace : WordTrace (prefixWord ++ tailWord_2275893) baseStart_2275893 baseEnd_2275893 := by
    simpa [prefixWord, tailWord_2275893, baseEnd_2275893] using wordTrace_append hprefix tailTrace_2275893
  have hstable : (prefixWord ++ tailWord_2275893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275893).length < 2 ^ (prefixWord ++ tailWord_2275893).sum := by decide
  have hdescent : baseEnd_2275893 < baseStart_2275893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275936 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_2275936 : Nat := 118140960795 + 2275936 * 2 ^ 59
def prefixEnd_2275936 : Nat := 4983230072969 + 3 ^ 40 * 2275936 * 2
def baseEnd_2275936 : Nat := 779099404580875082422111

theorem tailTrace_2275936 : CollatzResearch.WordTrace tailWord_2275936 prefixEnd_2275936 779099404580875082422111 := by
  unfold tailWord_2275936
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505102741340022884003831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55340136988453363845338441 41505102741340022884003831)
  ·
    refine ⟨62257654112010034326005747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41505102741340022884003831 62257654112010034326005747)
    ·
      refine ⟨93386481168015051489008621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62257654112010034326005747 93386481168015051489008621)
      ·
        refine ⟨35019930438005644308378233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93386481168015051489008621 35019930438005644308378233)
        ·
          refine ⟨26264947828504233231283675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35019930438005644308378233 26264947828504233231283675)
          ·
            refine ⟨39397421742756349846925513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26264947828504233231283675 39397421742756349846925513)
            ·
              refine ⟨29548066307067262385194135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39397421742756349846925513 29548066307067262385194135)
              ·
                refine ⟨44322099460600893577791203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29548066307067262385194135 44322099460600893577791203)
                ·
                  refine ⟨66483149190901340366686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44322099460600893577791203 66483149190901340366686805)
                  ·
                    refine ⟨779099404580875082422111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66483149190901340366686805 779099404580875082422111)
                    ·
                      rfl

theorem cell22_2275936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_2275936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275936 prefixEnd_2275936 := by exact prefixLift 2275936
  have htrace : WordTrace (prefixWord ++ tailWord_2275936) baseStart_2275936 baseEnd_2275936 := by
    simpa [prefixWord, tailWord_2275936, baseEnd_2275936] using wordTrace_append hprefix tailTrace_2275936
  have hstable : (prefixWord ++ tailWord_2275936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275936).length < 2 ^ (prefixWord ++ tailWord_2275936).sum := by decide
  have hdescent : baseEnd_2275936 < baseStart_2275936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275944 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2275944 : Nat := 118140960795 + 2275944 * 2 ^ 59
def prefixEnd_2275944 : Nat := 4983230072969 + 3 ^ 40 * 2275944 * 2
def baseEnd_2275944 : Nat := 779102143144365728222087

theorem tailTrace_2275944 : CollatzResearch.WordTrace tailWord_2275944 prefixEnd_2275944 779102143144365728222087 := by
  unfold tailWord_2275944
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505248633325531567149443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55340331511100708756199257 41505248633325531567149443)
  ·
    refine ⟨62257872949988297350724165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41505248633325531567149443 62257872949988297350724165)
    ·
      refine ⟨11673351178122805753260781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62257872949988297350724165 11673351178122805753260781)
      ·
        refine ⟨4377506691796052157472793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11673351178122805753260781 4377506691796052157472793)
        ·
          refine ⟨3283130018847039118104595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4377506691796052157472793 3283130018847039118104595)
          ·
            refine ⟨4924695028270558677156893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283130018847039118104595 4924695028270558677156893)
            ·
              refine ⟨1846760635601459503933835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4924695028270558677156893 1846760635601459503933835)
              ·
                refine ⟨2770140953402189255900753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846760635601459503933835 2770140953402189255900753)
                ·
                  refine ⟨2077605715051641941925565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770140953402189255900753 2077605715051641941925565)
                  ·
                    refine ⟨779102143144365728222087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077605715051641941925565 779102143144365728222087)
                    ·
                      rfl

theorem cell22_2275944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2275944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275944 prefixEnd_2275944 := by exact prefixLift 2275944
  have htrace : WordTrace (prefixWord ++ tailWord_2275944) baseStart_2275944 baseEnd_2275944 := by
    simpa [prefixWord, tailWord_2275944, baseEnd_2275944] using wordTrace_append hprefix tailTrace_2275944
  have hstable : (prefixWord ++ tailWord_2275944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275944).length < 2 ^ (prefixWord ++ tailWord_2275944).sum := by decide
  have hdescent : baseEnd_2275944 < baseStart_2275944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275957 : List Nat := [1, 3, 4, 2, 2, 2, 2, 6]
def baseStart_2275957 : Nat := 118140960795 + 2275957 * 2 ^ 59
def prefixEnd_2275957 : Nat := 4983230072969 + 3 ^ 40 * 2275957 * 2
def baseEnd_2275957 : Nat := 86567399256670891960783

theorem tailTrace_2275957 : CollatzResearch.WordTrace tailWord_2275957 prefixEnd_2275957 86567399256670891960783 := by
  unfold tailWord_2275957
  simp only [CollatzResearch.WordTrace]
  refine ⟨83010971415603966354522125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55340647610402644236348083 83010971415603966354522125)
  ·
    refine ⟨31129114280851487382945797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83010971415603966354522125 31129114280851487382945797)
    ·
      refine ⟨5836708927659653884302337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31129114280851487382945797 5836708927659653884302337)
      ·
        refine ⟨4377531695744740413226753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5836708927659653884302337 4377531695744740413226753)
        ·
          refine ⟨3283148771808555309920065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4377531695744740413226753 3283148771808555309920065)
          ·
            refine ⟨2462361578856416482440049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283148771808555309920065 2462361578856416482440049)
            ·
              refine ⟨1846771184142312361830037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462361578856416482440049 1846771184142312361830037)
              ·
                refine ⟨86567399256670891960783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1846771184142312361830037 86567399256670891960783)
                ·
                  rfl

theorem cell22_2275957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 6].length) (baseStart_2275957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2275957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2275957 prefixEnd_2275957 := by exact prefixLift 2275957
  have htrace : WordTrace (prefixWord ++ tailWord_2275957) baseStart_2275957 baseEnd_2275957 := by
    simpa [prefixWord, tailWord_2275957, baseEnd_2275957] using wordTrace_append hprefix tailTrace_2275957
  have hstable : (prefixWord ++ tailWord_2275957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275957).length < 2 ^ (prefixWord ++ tailWord_2275957).sum := by decide
  have hdescent : baseEnd_2275957 < baseStart_2275957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276015 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 1, 4]
def baseStart_2276015 : Nat := 118140960795 + 2276015 * 2 ^ 59
def prefixEnd_2276015 : Nat := 4983230072969 + 3 ^ 40 * 2276015 * 2
def baseEnd_2276015 : Nat := 779126447895345209696869

theorem tailTrace_2276015 : CollatzResearch.WordTrace tailWord_2276015 prefixEnd_2276015 779126447895345209696869 := by
  unfold tailWord_2276015
  simp only [CollatzResearch.WordTrace]
  refine ⟨83013086849393842260133499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55342057899595894840088999 83013086849393842260133499)
  ·
    refine ⟨124519630274090763390200249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83013086849393842260133499 124519630274090763390200249)
    ·
      refine ⟨93389722705568072542650187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124519630274090763390200249 93389722705568072542650187)
      ·
        refine ⟨140084584058352108813975281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93389722705568072542650187 140084584058352108813975281)
        ·
          refine ⟨105063438043764081610481461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140084584058352108813975281 105063438043764081610481461)
          ·
            refine ⟨9849697316602882650982637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105063438043764081610481461 9849697316602882650982637)
            ·
              refine ⟨3693636493726080994118489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9849697316602882650982637 3693636493726080994118489)
              ·
                refine ⟨2770227370294560745588867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693636493726080994118489 2770227370294560745588867)
                ·
                  refine ⟨4155341055441841118383301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770227370294560745588867 4155341055441841118383301)
                  ·
                    refine ⟨779126447895345209696869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155341055441841118383301 779126447895345209696869)
                    ·
                      rfl

theorem cell22_2276015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_2276015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276015 prefixEnd_2276015 := by exact prefixLift 2276015
  have htrace : WordTrace (prefixWord ++ tailWord_2276015) baseStart_2276015 baseEnd_2276015 := by
    simpa [prefixWord, tailWord_2276015, baseEnd_2276015] using wordTrace_append hprefix tailTrace_2276015
  have hstable : (prefixWord ++ tailWord_2276015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276015).length < 2 ^ (prefixWord ++ tailWord_2276015).sum := by decide
  have hdescent : baseEnd_2276015 < baseStart_2276015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276032 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_2276032 : Nat := 118140960795 + 2276032 * 2 ^ 59
def prefixEnd_2276032 : Nat := 4983230072969 + 3 ^ 40 * 2276032 * 2
def baseEnd_2276032 : Nat := 779132267342762832021817

theorem tailTrace_2276032 : CollatzResearch.WordTrace tailWord_2276032 prefixEnd_2276032 779132267342762832021817 := by
  unfold tailWord_2276032
  simp only [CollatzResearch.WordTrace]
  refine ⟨41506853445166127081751175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55342471260221502775668233 41506853445166127081751175)
  ·
    refine ⟨62260280167749190622626763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41506853445166127081751175 62260280167749190622626763)
    ·
      refine ⟨93390420251623785933940145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62260280167749190622626763 93390420251623785933940145)
      ·
        refine ⟨70042815188717839450455109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93390420251623785933940145 70042815188717839450455109)
        ·
          refine ⟨13133027847884594896960333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70042815188717839450455109 13133027847884594896960333)
          ·
            refine ⟨4924885442956723086360125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13133027847884594896960333 4924885442956723086360125)
            ·
              refine ⟨1846832041108771157385047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4924885442956723086360125 1846832041108771157385047)
              ·
                refine ⟨2770248061663156736077571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846832041108771157385047 2770248061663156736077571)
                ·
                  refine ⟨4155372092494735104116357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770248061663156736077571 4155372092494735104116357)
                  ·
                    refine ⟨779132267342762832021817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155372092494735104116357 779132267342762832021817)
                    ·
                      rfl

theorem cell22_2276032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_2276032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276032 prefixEnd_2276032 := by exact prefixLift 2276032
  have htrace : WordTrace (prefixWord ++ tailWord_2276032) baseStart_2276032 baseEnd_2276032 := by
    simpa [prefixWord, tailWord_2276032, baseEnd_2276032] using wordTrace_append hprefix tailTrace_2276032
  have hstable : (prefixWord ++ tailWord_2276032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276032).length < 2 ^ (prefixWord ++ tailWord_2276032).sum := by decide
  have hdescent : baseEnd_2276032 < baseStart_2276032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276158 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2276158 : Nat := 118140960795 + 2276158 * 2 ^ 59
def prefixEnd_2276158 : Nat := 4983230072969 + 3 ^ 40 * 2276158 * 2
def baseEnd_2276158 : Nat := 779175399717740503371431

theorem tailTrace_2276158 : CollatzResearch.WordTrace tailWord_2276158 prefixEnd_2276158 779175399717740503371431 := by
  unfold tailWord_2276158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377287810984472210323641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55345534991917185121726085 10377287810984472210323641)
  ·
    refine ⟨7782965858238354157742731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10377287810984472210323641 7782965858238354157742731)
    ·
      refine ⟨11674448787357531236614097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7782965858238354157742731 11674448787357531236614097)
      ·
        refine ⟨8755836590518148427460573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11674448787357531236614097 8755836590518148427460573)
        ·
          refine ⟨3283438721444305660297715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8755836590518148427460573 3283438721444305660297715)
          ·
            refine ⟨4925158082166458490446573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283438721444305660297715 4925158082166458490446573)
            ·
              refine ⟨1846934280812421933917465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4925158082166458490446573 1846934280812421933917465)
              ·
                refine ⟨1385200710609316450438099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846934280812421933917465 1385200710609316450438099)
                ·
                  refine ⟨2077801065913974675657149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385200710609316450438099 2077801065913974675657149)
                  ·
                    refine ⟨779175399717740503371431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077801065913974675657149 779175399717740503371431)
                    ·
                      rfl

theorem cell22_2276158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2276158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276158 prefixEnd_2276158 := by exact prefixLift 2276158
  have htrace : WordTrace (prefixWord ++ tailWord_2276158) baseStart_2276158 baseEnd_2276158 := by
    simpa [prefixWord, tailWord_2276158, baseEnd_2276158] using wordTrace_append hprefix tailTrace_2276158
  have hstable : (prefixWord ++ tailWord_2276158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276158).length < 2 ^ (prefixWord ++ tailWord_2276158).sum := by decide
  have hdescent : baseEnd_2276158 < baseStart_2276158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276246 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2276246 : Nat := 118140960795 + 2276246 * 2 ^ 59
def prefixEnd_2276246 : Nat := 4983230072969 + 3 ^ 40 * 2276246 * 2
def baseEnd_2276246 : Nat := 779205523916137607171161

theorem tailTrace_2276246 : CollatzResearch.WordTrace tailWord_2276246 prefixEnd_2276246 779205523916137607171161 := by
  unfold tailWord_2276246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188844506972310544487037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55347674741037979141195061 5188844506972310544487037)
  ·
    refine ⟨1945816690114616454182639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5188844506972310544487037 1945816690114616454182639)
    ·
      refine ⟨2918725035171924681273959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945816690114616454182639 2918725035171924681273959)
      ·
        refine ⟨4378087552757887021910939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918725035171924681273959 4378087552757887021910939)
        ·
          refine ⟨6567131329136830532866409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378087552757887021910939 6567131329136830532866409)
          ·
            refine ⟨4925348496852622899649807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6567131329136830532866409 4925348496852622899649807)
            ·
              refine ⟨7388022745278934349474711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925348496852622899649807 7388022745278934349474711)
              ·
                refine ⟨11082034117918401524212067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388022745278934349474711 11082034117918401524212067)
                ·
                  refine ⟨16623051176877602286318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082034117918401524212067 16623051176877602286318101)
                  ·
                    refine ⟨779205523916137607171161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16623051176877602286318101 779205523916137607171161)
                    ·
                      rfl

theorem cell22_2276246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2276246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276246 prefixEnd_2276246 := by exact prefixLift 2276246
  have htrace : WordTrace (prefixWord ++ tailWord_2276246) baseStart_2276246 baseEnd_2276246 := by
    simpa [prefixWord, tailWord_2276246, baseEnd_2276246] using wordTrace_append hprefix tailTrace_2276246
  have hstable : (prefixWord ++ tailWord_2276246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276246).length < 2 ^ (prefixWord ++ tailWord_2276246).sum := by decide
  have hdescent : baseEnd_2276246 < baseStart_2276246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276259 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 1, 3]
def baseStart_2276259 : Nat := 118140960795 + 2276259 * 2 ^ 59
def prefixEnd_2276259 : Nat := 4983230072969 + 3 ^ 40 * 2276259 * 2
def baseEnd_2276259 : Nat := 779209974081809906596121

theorem tailTrace_2276259 : CollatzResearch.WordTrace tailWord_2276259 prefixEnd_2276259 779209974081809906596121 := by
  unfold tailWord_2276259
  simp only [CollatzResearch.WordTrace]
  refine ⟨83021986260509871932015831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55347990840339914621343887 83021986260509871932015831)
  ·
    refine ⟨124532979390764807898023747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83021986260509871932015831 124532979390764807898023747)
    ·
      refine ⟨186799469086147211847035621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124532979390764807898023747 186799469086147211847035621)
      ·
        refine ⟨35024900453652602221319179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186799469086147211847035621 35024900453652602221319179)
        ·
          refine ⟨52537350680478903331978769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35024900453652602221319179 52537350680478903331978769)
          ·
            refine ⟨39403013010359177498984077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52537350680478903331978769 39403013010359177498984077)
            ·
              refine ⟨14776129878884691562119029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39403013010359177498984077 14776129878884691562119029)
              ·
                refine ⟨1385262176145439833948659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14776129878884691562119029 1385262176145439833948659)
                ·
                  refine ⟨2077893264218159750922989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385262176145439833948659 2077893264218159750922989)
                  ·
                    refine ⟨779209974081809906596121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077893264218159750922989 779209974081809906596121)
                    ·
                      rfl

theorem cell22_2276259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 3].length) (baseStart_2276259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276259 prefixEnd_2276259 := by exact prefixLift 2276259
  have htrace : WordTrace (prefixWord ++ tailWord_2276259) baseStart_2276259 baseEnd_2276259 := by
    simpa [prefixWord, tailWord_2276259, baseEnd_2276259] using wordTrace_append hprefix tailTrace_2276259
  have hstable : (prefixWord ++ tailWord_2276259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276259).length < 2 ^ (prefixWord ++ tailWord_2276259).sum := by decide
  have hdescent : baseEnd_2276259 < baseStart_2276259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276276 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2276276 : Nat := 118140960795 + 2276276 * 2 ^ 59
def prefixEnd_2276276 : Nat := 4983230072969 + 3 ^ 40 * 2276276 * 2
def baseEnd_2276276 : Nat := 779215793529227528921069

theorem tailTrace_2276276 : CollatzResearch.WordTrace tailWord_2276276 prefixEnd_2276276 779215793529227528921069 := by
  unfold tailWord_2276276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511303150724141917692341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55348404200965522556923121 41511303150724141917692341)
  ·
    refine ⟨3891684670380388304783657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41511303150724141917692341 3891684670380388304783657)
    ·
      refine ⟨2918763502785291228587743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3891684670380388304783657 2918763502785291228587743)
      ·
        refine ⟨4378145254177936842881615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918763502785291228587743 4378145254177936842881615)
        ·
          refine ⟨6567217881266905264322423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378145254177936842881615 6567217881266905264322423)
          ·
            refine ⟨9850826821900357896483635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567217881266905264322423 9850826821900357896483635)
            ·
              refine ⟨14776240232850536844725453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850826821900357896483635 14776240232850536844725453)
              ·
                refine ⟨5541090087318951316772045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14776240232850536844725453 5541090087318951316772045)
                ·
                  refine ⟨2077908782744606743789517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5541090087318951316772045 2077908782744606743789517)
                  ·
                    refine ⟨779215793529227528921069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077908782744606743789517 779215793529227528921069)
                    ·
                      rfl

theorem cell22_2276276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2276276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276276 prefixEnd_2276276 := by exact prefixLift 2276276
  have htrace : WordTrace (prefixWord ++ tailWord_2276276) baseStart_2276276 baseEnd_2276276 := by
    simpa [prefixWord, tailWord_2276276, baseEnd_2276276] using wordTrace_append hprefix tailTrace_2276276
  have hstable : (prefixWord ++ tailWord_2276276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276276).length < 2 ^ (prefixWord ++ tailWord_2276276).sum := by decide
  have hdescent : baseEnd_2276276 < baseStart_2276276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276310 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2276310 : Nat := 118140960795 + 2276310 * 2 ^ 59
def prefixEnd_2276310 : Nat := 4983230072969 + 3 ^ 40 * 2276310 * 2
def baseEnd_2276310 : Nat := 779227432424062773570965

theorem tailTrace_2276310 : CollatzResearch.WordTrace tailWord_2276310 prefixEnd_2276310 779227432424062773570965 := by
  unfold tailWord_2276310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188990398957819227632649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55349230922216738428081589 5188990398957819227632649)
  ·
    refine ⟨3891742799218364420724487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5188990398957819227632649 3891742799218364420724487)
    ·
      refine ⟨5837614198827546631086731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891742799218364420724487 5837614198827546631086731)
      ·
        refine ⟨8756421298241319946630097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837614198827546631086731 8756421298241319946630097)
        ·
          refine ⟨6567315973680989959972573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8756421298241319946630097 6567315973680989959972573)
          ·
            refine ⟨2462743490130371234989715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6567315973680989959972573 2462743490130371234989715)
            ·
              refine ⟨3694115235195556852484573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462743490130371234989715 3694115235195556852484573)
              ·
                refine ⟨1385293213198333819681715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3694115235195556852484573 1385293213198333819681715)
                ·
                  refine ⟨2077939819797500729522573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385293213198333819681715 2077939819797500729522573)
                  ·
                    refine ⟨779227432424062773570965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077939819797500729522573 779227432424062773570965)
                    ·
                      rfl

theorem cell22_2276310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2276310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276310 prefixEnd_2276310 := by exact prefixLift 2276310
  have htrace : WordTrace (prefixWord ++ tailWord_2276310) baseStart_2276310 baseEnd_2276310 := by
    simpa [prefixWord, tailWord_2276310, baseEnd_2276310] using wordTrace_append hprefix tailTrace_2276310
  have hstable : (prefixWord ++ tailWord_2276310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276310).length < 2 ^ (prefixWord ++ tailWord_2276310).sum := by decide
  have hdescent : baseEnd_2276310 < baseStart_2276310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276340 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2276340 : Nat := 118140960795 + 2276340 * 2 ^ 59
def prefixEnd_2276340 : Nat := 4983230072969 + 3 ^ 40 * 2276340 * 2
def baseEnd_2276340 : Nat := 259745900679050898440291

theorem tailTrace_2276340 : CollatzResearch.WordTrace tailWord_2276340 prefixEnd_2276340 259745900679050898440291 := by
  unfold tailWord_2276340
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512470286608211382857237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55349960382144281843809649 41512470286608211382857237)
  ·
    refine ⟨1945897044684759908571433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41512470286608211382857237 1945897044684759908571433)
    ·
      refine ⟨1459422783513569931428575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1945897044684759908571433 1459422783513569931428575)
      ·
        refine ⟨2189134175270354897142863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459422783513569931428575 2189134175270354897142863)
        ·
          refine ⟨3283701262905532345714295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189134175270354897142863 3283701262905532345714295)
          ·
            refine ⟨4925551894358298518571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283701262905532345714295 4925551894358298518571443)
            ·
              refine ⟨7388327841537447777857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925551894358298518571443 7388327841537447777857165)
              ·
                refine ⟨2770622940576542916696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7388327841537447777857165 2770622940576542916696437)
                ·
                  refine ⟨259745900679050898440291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2770622940576542916696437 259745900679050898440291)
                  ·
                    rfl

theorem cell22_2276340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2276340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276340 prefixEnd_2276340 := by exact prefixLift 2276340
  have htrace : WordTrace (prefixWord ++ tailWord_2276340) baseStart_2276340 baseEnd_2276340 := by
    simpa [prefixWord, tailWord_2276340, baseEnd_2276340] using wordTrace_append hprefix tailTrace_2276340
  have hstable : (prefixWord ++ tailWord_2276340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276340).length < 2 ^ (prefixWord ++ tailWord_2276340).sum := by decide
  have hdescent : baseEnd_2276340 < baseStart_2276340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276362 : List Nat := [3, 1, 2, 2, 3, 1, 2, 8]
def baseStart_2276362 : Nat := 118140960795 + 2276362 * 2 ^ 59
def prefixEnd_2276362 : Nat := 4983230072969 + 3 ^ 40 * 2276362 * 2
def baseEnd_2276362 : Nat := 86582803676305774585645

theorem tailTrace_2276362 : CollatzResearch.WordTrace tailWord_2276362 prefixEnd_2276362 86582803676305774585645 := by
  unfold tailWord_2276362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756435744784180130753835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55350495319424480348676893 20756435744784180130753835)
  ·
    refine ⟨31134653617176270196130753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20756435744784180130753835 31134653617176270196130753)
    ·
      refine ⟨23350990212882202647098065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31134653617176270196130753 23350990212882202647098065)
      ·
        refine ⟨17513242659661651985323549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23350990212882202647098065 17513242659661651985323549)
        ·
          refine ⟨6567465997373119494496331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17513242659661651985323549 6567465997373119494496331)
          ·
            refine ⟨9851198996059679241744497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567465997373119494496331 9851198996059679241744497)
            ·
              refine ⟨7388399247044759431308373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851198996059679241744497 7388399247044759431308373)
              ·
                refine ⟨86582803676305774585645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7388399247044759431308373 86582803676305774585645)
                ·
                  rfl

theorem cell22_2276362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_2276362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276362 prefixEnd_2276362 := by exact prefixLift 2276362
  have htrace : WordTrace (prefixWord ++ tailWord_2276362) baseStart_2276362 baseEnd_2276362 := by
    simpa [prefixWord, tailWord_2276362, baseEnd_2276362] using wordTrace_append hprefix tailTrace_2276362
  have hstable : (prefixWord ++ tailWord_2276362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276362).length < 2 ^ (prefixWord ++ tailWord_2276362).sum := by decide
  have hdescent : baseEnd_2276362 < baseStart_2276362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276364 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_2276364 : Nat := 118140960795 + 2276364 * 2 ^ 59
def prefixEnd_2276364 : Nat := 4983230072969 + 3 ^ 40 * 2276364 * 2
def baseEnd_2276364 : Nat := 779245917727624632720799

theorem tailTrace_2276364 : CollatzResearch.WordTrace tailWord_2276364 prefixEnd_2276364 779245917727624632720799 := by
  unfold tailWord_2276364
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512907962564737432294073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55350543950086316576392097 41512907962564737432294073)
  ·
    refine ⟨31134680971923553074220555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41512907962564737432294073 31134680971923553074220555)
    ·
      refine ⟨46702021457885329611330833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31134680971923553074220555 46702021457885329611330833)
      ·
        refine ⟨35026516093413997208498125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46702021457885329611330833 35026516093413997208498125)
        ·
          refine ⟨13134943535030248953186797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35026516093413997208498125 13134943535030248953186797)
          ·
            refine ⟨4925603825636343357445049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13134943535030248953186797 4925603825636343357445049)
            ·
              refine ⟨3694202869227257518083787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925603825636343357445049 3694202869227257518083787)
              ·
                refine ⟨5541304303840886277125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694202869227257518083787 5541304303840886277125681)
                ·
                  refine ⟨4155978227880664707844261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541304303840886277125681 4155978227880664707844261)
                  ·
                    refine ⟨779245917727624632720799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155978227880664707844261 779245917727624632720799)
                    ·
                      rfl

theorem cell22_2276364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_2276364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276364 prefixEnd_2276364 := by exact prefixLift 2276364
  have htrace : WordTrace (prefixWord ++ tailWord_2276364) baseStart_2276364 baseEnd_2276364 := by
    simpa [prefixWord, tailWord_2276364, baseEnd_2276364] using wordTrace_append hprefix tailTrace_2276364
  have hstable : (prefixWord ++ tailWord_2276364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276364).length < 2 ^ (prefixWord ++ tailWord_2276364).sum := by decide
  have hdescent : baseEnd_2276364 < baseStart_2276364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276503 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 4]
def baseStart_2276503 : Nat := 118140960795 + 2276503 * 2 ^ 59
def prefixEnd_2276503 : Nat := 4983230072969 + 3 ^ 40 * 2276503 * 2
def baseEnd_2276503 : Nat := 259764500089424867831791

theorem tailTrace_2276503 : CollatzResearch.WordTrace tailWord_2276503 prefixEnd_2276503 259764500089424867831791 := by
  unfold tailWord_2276503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83030885671625901603898163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55353923781083934402598775 83030885671625901603898163)
  ·
    refine ⟨124546328507438852405847245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83030885671625901603898163 124546328507438852405847245)
    ·
      refine ⟨46704873190289569652192717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124546328507438852405847245 46704873190289569652192717)
      ·
        refine ⟨17514327446358588619572269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46704873190289569652192717 17514327446358588619572269)
        ·
          refine ⟨6567872792384470732339601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17514327446358588619572269 6567872792384470732339601)
          ·
            refine ⟨4925904594288353049254701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6567872792384470732339601 4925904594288353049254701)
            ·
              refine ⟨1847214222858132393470513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4925904594288353049254701 1847214222858132393470513)
              ·
                refine ⟨1385410667143599295102885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847214222858132393470513 1385410667143599295102885)
                ·
                  refine ⟨259764500089424867831791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385410667143599295102885 259764500089424867831791)
                  ·
                    rfl

theorem cell22_2276503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 4].length) (baseStart_2276503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276503 prefixEnd_2276503 := by exact prefixLift 2276503
  have htrace : WordTrace (prefixWord ++ tailWord_2276503) baseStart_2276503 baseEnd_2276503 := by
    simpa [prefixWord, tailWord_2276503, baseEnd_2276503] using wordTrace_append hprefix tailTrace_2276503
  have hstable : (prefixWord ++ tailWord_2276503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276503).length < 2 ^ (prefixWord ++ tailWord_2276503).sum := by decide
  have hdescent : baseEnd_2276503 < baseStart_2276503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276610 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2276610 : Nat := 118140960795 + 2276610 * 2 ^ 59
def prefixEnd_2276610 : Nat := 4983230072969 + 3 ^ 40 * 2276610 * 2
def baseEnd_2276610 : Nat := 259776709518320663690015

theorem tailTrace_2276610 : CollatzResearch.WordTrace tailWord_2276610 prefixEnd_2276610 259776709518320663690015 := by
  unfold tailWord_2276610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20758697070559564719510821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55356525521492172585362189 20758697070559564719510821)
  ·
    refine ⟨3892255700729918384908279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20758697070559564719510821 3892255700729918384908279)
    ·
      refine ⟨5838383551094877577362419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3892255700729918384908279 5838383551094877577362419)
      ·
        refine ⟨8757575326642316366043629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838383551094877577362419 8757575326642316366043629)
        ·
          refine ⟨3284090747490868637266361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8757575326642316366043629 3284090747490868637266361)
          ·
            refine ⟨2463068060618151477949771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284090747490868637266361 2463068060618151477949771)
            ·
              refine ⟨3694602090927227216924657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463068060618151477949771 3694602090927227216924657)
              ·
                refine ⟨2770951568195420412693493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694602090927227216924657 2770951568195420412693493)
                ·
                  refine ⟨259776709518320663690015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2770951568195420412693493 259776709518320663690015)
                  ·
                    rfl

theorem cell22_2276610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2276610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276610 prefixEnd_2276610 := by exact prefixLift 2276610
  have htrace : WordTrace (prefixWord ++ tailWord_2276610) baseStart_2276610 baseEnd_2276610 := by
    simpa [prefixWord, tailWord_2276610, baseEnd_2276610] using wordTrace_append hprefix tailTrace_2276610
  have hstable : (prefixWord ++ tailWord_2276610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276610).length < 2 ^ (prefixWord ++ tailWord_2276610).sum := by decide
  have hdescent : baseEnd_2276610 < baseStart_2276610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276636 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2276636 : Nat := 118140960795 + 2276636 * 2 ^ 59
def prefixEnd_2276636 : Nat := 4983230072969 + 3 ^ 40 * 2276636 * 2
def baseEnd_2276636 : Nat := 779339028886306589919965

theorem tailTrace_2276636 : CollatzResearch.WordTrace tailWord_2276636 prefixEnd_2276636 779339028886306589919965 := by
  unfold tailWord_2276636
  simp only [CollatzResearch.WordTrace]
  refine ⟨41517868290072032659244881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55357157720096043545659841 41517868290072032659244881)
  ·
    refine ⟨31138401217554024494433661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41517868290072032659244881 31138401217554024494433661)
    ·
      refine ⟨11676900456582759185412623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31138401217554024494433661 11676900456582759185412623)
      ·
        refine ⟨17515350684874138778118935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11676900456582759185412623 17515350684874138778118935)
        ·
          refine ⟨26273026027311208167178403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17515350684874138778118935 26273026027311208167178403)
          ·
            refine ⟨39409539040966812250767605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26273026027311208167178403 39409539040966812250767605)
            ·
              refine ⟨3694644285090638648509463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39409539040966812250767605 3694644285090638648509463)
              ·
                refine ⟨5541966427635957972764195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694644285090638648509463 5541966427635957972764195)
                ·
                  refine ⟨8312949641453936959146293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541966427635957972764195 8312949641453936959146293)
                  ·
                    refine ⟨779339028886306589919965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8312949641453936959146293 779339028886306589919965)
                    ·
                      rfl

theorem cell22_2276636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2276636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276636 prefixEnd_2276636 := by exact prefixLift 2276636
  have htrace : WordTrace (prefixWord ++ tailWord_2276636) baseStart_2276636 baseEnd_2276636 := by
    simpa [prefixWord, tailWord_2276636, baseEnd_2276636] using wordTrace_append hprefix tailTrace_2276636
  have hstable : (prefixWord ++ tailWord_2276636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276636).length < 2 ^ (prefixWord ++ tailWord_2276636).sum := by decide
  have hdescent : baseEnd_2276636 < baseStart_2276636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276741 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_2276741 : Nat := 118140960795 + 2276741 * 2 ^ 59
def prefixEnd_2276741 : Nat := 4983230072969 + 3 ^ 40 * 2276741 * 2
def baseEnd_2276741 : Nat := 779374972532121316044643

theorem tailTrace_2276741 : CollatzResearch.WordTrace tailWord_2276741 prefixEnd_2276741 779374972532121316044643 := by
  unfold tailWord_2276741
  simp only [CollatzResearch.WordTrace]
  refine ⟨83039566244763668251062077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55359710829842445500708051 83039566244763668251062077)
  ·
    refine ⟨31139837341786375594148279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83039566244763668251062077 31139837341786375594148279)
    ·
      refine ⟨46709756012679563391222419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31139837341786375594148279 46709756012679563391222419)
      ·
        refine ⟨70064634019019345086833629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46709756012679563391222419 70064634019019345086833629)
        ·
          refine ⟨26274237757132254407562611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70064634019019345086833629 26274237757132254407562611)
          ·
            refine ⟨39411356635698381611343917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26274237757132254407562611 39411356635698381611343917)
            ·
              refine ⟨14779258738386893104253969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39411356635698381611343917 14779258738386893104253969)
              ·
                refine ⟨11084444053790169828190477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14779258738386893104253969 11084444053790169828190477)
                ·
                  refine ⟨4156666520171313685571429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11084444053790169828190477 4156666520171313685571429)
                  ·
                    refine ⟨779374972532121316044643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156666520171313685571429 779374972532121316044643)
                    ·
                      rfl

theorem cell22_2276741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_2276741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276741 prefixEnd_2276741 := by exact prefixLift 2276741
  have htrace : WordTrace (prefixWord ++ tailWord_2276741) baseStart_2276741 baseEnd_2276741 := by
    simpa [prefixWord, tailWord_2276741, baseEnd_2276741] using wordTrace_append hprefix tailTrace_2276741
  have hstable : (prefixWord ++ tailWord_2276741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276741).length < 2 ^ (prefixWord ++ tailWord_2276741).sum := by decide
  have hdescent : baseEnd_2276741 < baseStart_2276741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276771 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_2276771 : Nat := 118140960795 + 2276771 * 2 ^ 59
def prefixEnd_2276771 : Nat := 4983230072969 + 3 ^ 40 * 2276771 * 2
def baseEnd_2276771 : Nat := 779385242145211237794551

theorem tailTrace_2276771 : CollatzResearch.WordTrace tailWord_2276771 prefixEnd_2276771 779385242145211237794551 := by
  unfold tailWord_2276771
  simp only [CollatzResearch.WordTrace]
  refine ⟨83040660434654983374654167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55360440289769988916436111 83040660434654983374654167)
  ·
    refine ⟨124560990651982475061981251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83040660434654983374654167 124560990651982475061981251)
    ·
      refine ⟨186841485977973712592971877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124560990651982475061981251 186841485977973712592971877)
      ·
        refine ⟨35032778620870071111182227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186841485977973712592971877 35032778620870071111182227)
        ·
          refine ⟨52549167931305106666773341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35032778620870071111182227 52549167931305106666773341)
          ·
            refine ⟨19705937974239415000040003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52549167931305106666773341 19705937974239415000040003)
            ·
              refine ⟨29558906961359122500060005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19705937974239415000040003 29558906961359122500060005)
              ·
                refine ⟨5542295055254835468761251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29558906961359122500060005 5542295055254835468761251)
                ·
                  refine ⟨8313442582882253203141877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542295055254835468761251 8313442582882253203141877)
                  ·
                    refine ⟨779385242145211237794551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8313442582882253203141877 779385242145211237794551)
                    ·
                      rfl

theorem cell22_2276771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_2276771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276771 prefixEnd_2276771 := by exact prefixLift 2276771
  have htrace : WordTrace (prefixWord ++ tailWord_2276771) baseStart_2276771 baseEnd_2276771 := by
    simpa [prefixWord, tailWord_2276771, baseEnd_2276771] using wordTrace_append hprefix tailTrace_2276771
  have hstable : (prefixWord ++ tailWord_2276771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276771).length < 2 ^ (prefixWord ++ tailWord_2276771).sum := by decide
  have hdescent : baseEnd_2276771 < baseStart_2276771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276910 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2276910 : Nat := 118140960795 + 2276910 * 2 ^ 59
def prefixEnd_2276910 : Nat := 4983230072969 + 3 ^ 40 * 2276910 * 2
def baseEnd_2276910 : Nat := 779432824685861208569125

theorem tailTrace_2276910 : CollatzResearch.WordTrace tailWord_2276910 prefixEnd_2276910 779432824685861208569125 := by
  unfold tailWord_2276910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380716272643926264245523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55363820120767606742642789 10380716272643926264245523)
  ·
    refine ⟨15571074408965889396368285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10380716272643926264245523 15571074408965889396368285)
    ·
      refine ⟨5839152903362208523638107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15571074408965889396368285 5839152903362208523638107)
      ·
        refine ⟨8758729355043312785457161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839152903362208523638107 8758729355043312785457161)
        ·
          refine ⟨6569047016282484589092871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8758729355043312785457161 6569047016282484589092871)
          ·
            refine ⟨9853570524423726883639307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6569047016282484589092871 9853570524423726883639307)
            ·
              refine ⟨14780355786635590325458961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9853570524423726883639307 14780355786635590325458961)
              ·
                refine ⟨11085266839976692744094221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14780355786635590325458961 11085266839976692744094221)
                ·
                  refine ⟨4156975064991259779035333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11085266839976692744094221 4156975064991259779035333)
                  ·
                    refine ⟨779432824685861208569125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156975064991259779035333 779432824685861208569125)
                    ·
                      rfl

theorem cell22_2276910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2276910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276910 prefixEnd_2276910 := by exact prefixLift 2276910
  have htrace : WordTrace (prefixWord ++ tailWord_2276910) baseStart_2276910 baseEnd_2276910 := by
    simpa [prefixWord, tailWord_2276910, baseEnd_2276910] using wordTrace_append hprefix tailTrace_2276910
  have hstable : (prefixWord ++ tailWord_2276910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276910).length < 2 ^ (prefixWord ++ tailWord_2276910).sum := by decide
  have hdescent : baseEnd_2276910 < baseStart_2276910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276925 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2276925 : Nat := 118140960795 + 2276925 * 2 ^ 59
def prefixEnd_2276925 : Nat := 4983230072969 + 3 ^ 40 * 2276925 * 2
def baseEnd_2276925 : Nat := 259812653164135389814693

theorem tailTrace_2276925 : CollatzResearch.WordTrace tailWord_2276925 prefixEnd_2276925 259812653164135389814693 := by
  unfold tailWord_2276925
  simp only [CollatzResearch.WordTrace]
  refine ⟨83046277276097067675760229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55364184850731378450506819 83046277276097067675760229)
  ·
    refine ⟨15571176989268200189205043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83046277276097067675760229 15571176989268200189205043)
    ·
      refine ⟨23356765483902300283807565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15571176989268200189205043 23356765483902300283807565)
      ·
        refine ⟨8758787056463362606427837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23356765483902300283807565 8758787056463362606427837)
        ·
          refine ⟨3284545146173760977410439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8758787056463362606427837 3284545146173760977410439)
          ·
            refine ⟨4926817719260641466115659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284545146173760977410439 4926817719260641466115659)
            ·
              refine ⟨7390226578890962199173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926817719260641466115659 7390226578890962199173489)
              ·
                refine ⟨5542669934168221649380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390226578890962199173489 5542669934168221649380117)
                ·
                  refine ⟨259812653164135389814693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5542669934168221649380117 259812653164135389814693)
                  ·
                    rfl

theorem cell22_2276925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2276925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276925 prefixEnd_2276925 := by exact prefixLift 2276925
  have htrace : WordTrace (prefixWord ++ tailWord_2276925) baseStart_2276925 baseEnd_2276925 := by
    simpa [prefixWord, tailWord_2276925, baseEnd_2276925] using wordTrace_append hprefix tailTrace_2276925
  have hstable : (prefixWord ++ tailWord_2276925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276925).length < 2 ^ (prefixWord ++ tailWord_2276925).sum := by decide
  have hdescent : baseEnd_2276925 < baseStart_2276925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276938 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2276938 : Nat := 118140960795 + 2276938 * 2 ^ 59
def prefixEnd_2276938 : Nat := 4983230072969 + 3 ^ 40 * 2276938 * 2
def baseEnd_2276938 : Nat := 779442409658078468869039

theorem tailTrace_2276938 : CollatzResearch.WordTrace tailWord_2276938 prefixEnd_2276938 779442409658078468869039 := by
  unfold tailWord_2276938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761687856262492723995867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55364500950033313930655645 20761687856262492723995867)
  ·
    refine ⟨31142531784393739085993801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20761687856262492723995867 31142531784393739085993801)
    ·
      refine ⟨23356898838295304314495351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31142531784393739085993801 23356898838295304314495351)
      ·
        refine ⟨35035348257442956471743027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23356898838295304314495351 35035348257442956471743027)
        ·
          refine ⟨52553022386164434707614541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35035348257442956471743027 52553022386164434707614541)
          ·
            refine ⟨19707383394811663015355453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52553022386164434707614541 19707383394811663015355453)
            ·
              refine ⟨7390268773054373630758295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19707383394811663015355453 7390268773054373630758295)
              ·
                refine ⟨11085403159581560446137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7390268773054373630758295 11085403159581560446137443)
                ·
                  refine ⟨16628104739372340669206165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11085403159581560446137443 16628104739372340669206165)
                  ·
                    refine ⟨779442409658078468869039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16628104739372340669206165 779442409658078468869039)
                    ·
                      rfl

theorem cell22_2276938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2276938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276938 prefixEnd_2276938 := by exact prefixLift 2276938
  have htrace : WordTrace (prefixWord ++ tailWord_2276938) baseStart_2276938 baseEnd_2276938 := by
    simpa [prefixWord, tailWord_2276938, baseEnd_2276938] using wordTrace_append hprefix tailTrace_2276938
  have hstable : (prefixWord ++ tailWord_2276938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276938).length < 2 ^ (prefixWord ++ tailWord_2276938).sum := by decide
  have hdescent : baseEnd_2276938 < baseStart_2276938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276974 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2276974 : Nat := 118140960795 + 2276974 * 2 ^ 59
def prefixEnd_2276974 : Nat := 4983230072969 + 3 ^ 40 * 2276974 * 2
def baseEnd_2276974 : Nat := 779454733193786374968929

theorem tailTrace_2276974 : CollatzResearch.WordTrace tailWord_2276974 prefixEnd_2276974 779454733193786374968929 := by
  unfold tailWord_2276974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10381008056614943630536747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55365376301946366029529317 10381008056614943630536747)
  ·
    refine ⟨15571512084922415445805121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10381008056614943630536747 15571512084922415445805121)
    ·
      refine ⟨11678634063691811584353841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15571512084922415445805121 11678634063691811584353841)
      ·
        refine ⟨8758975547768858688265381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11678634063691811584353841 8758975547768858688265381)
        ·
          refine ⟨1642307915206661004049759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8758975547768858688265381 1642307915206661004049759)
          ·
            refine ⟨2463461872809991506074639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642307915206661004049759 2463461872809991506074639)
            ·
              refine ⟨3695192809214987259111959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463461872809991506074639 3695192809214987259111959)
              ·
                refine ⟨5542789213822480888667939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695192809214987259111959 5542789213822480888667939)
                ·
                  refine ⟨8314183820733721333001909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542789213822480888667939 8314183820733721333001909)
                  ·
                    refine ⟨779454733193786374968929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314183820733721333001909 779454733193786374968929)
                    ·
                      rfl

theorem cell22_2276974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2276974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276974 prefixEnd_2276974 := by exact prefixLift 2276974
  have htrace : WordTrace (prefixWord ++ tailWord_2276974) baseStart_2276974 baseEnd_2276974 := by
    simpa [prefixWord, tailWord_2276974, baseEnd_2276974] using wordTrace_append hprefix tailTrace_2276974
  have hstable : (prefixWord ++ tailWord_2276974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276974).length < 2 ^ (prefixWord ++ tailWord_2276974).sum := by decide
  have hdescent : baseEnd_2276974 < baseStart_2276974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276985 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_2276985 : Nat := 118140960795 + 2276985 * 2 ^ 59
def prefixEnd_2276985 : Nat := 4983230072969 + 3 ^ 40 * 2276985 * 2
def baseEnd_2276985 : Nat := 779458498718586012943895

theorem tailTrace_2276985 : CollatzResearch.WordTrace tailWord_2276985 prefixEnd_2276985 779458498718586012943895 := by
  unfold tailWord_2276985
  simp only [CollatzResearch.WordTrace]
  refine ⟨83048465655879697922944409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55365643770586465281962939 83048465655879697922944409)
  ·
    refine ⟨62286349241909773442208307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83048465655879697922944409 62286349241909773442208307)
    ·
      refine ⟨93429523862864660163312461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62286349241909773442208307 93429523862864660163312461)
      ·
        refine ⟨35036071448574247561242173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93429523862864660163312461 35036071448574247561242173)
        ·
          refine ⟨13138526793215342835465815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35036071448574247561242173 13138526793215342835465815)
          ·
            refine ⟨19707790189823014253198723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13138526793215342835465815 19707790189823014253198723)
            ·
              refine ⟨29561685284734521379798085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19707790189823014253198723 29561685284734521379798085)
              ·
                refine ⟨5542815990887722758712141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29561685284734521379798085 5542815990887722758712141)
                ·
                  refine ⟨2078555996582896034517053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542815990887722758712141 2078555996582896034517053)
                  ·
                    refine ⟨779458498718586012943895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078555996582896034517053 779458498718586012943895)
                    ·
                      rfl

theorem cell22_2276985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_2276985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2276985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2276985 prefixEnd_2276985 := by exact prefixLift 2276985
  have htrace : WordTrace (prefixWord ++ tailWord_2276985) baseStart_2276985 baseEnd_2276985 := by
    simpa [prefixWord, tailWord_2276985, baseEnd_2276985] using wordTrace_append hprefix tailTrace_2276985
  have hstable : (prefixWord ++ tailWord_2276985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276985).length < 2 ^ (prefixWord ++ tailWord_2276985).sum := by decide
  have hdescent : baseEnd_2276985 < baseStart_2276985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277013 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2277013 : Nat := 118140960795 + 2277013 * 2 ^ 59
def prefixEnd_2277013 : Nat := 4983230072969 + 3 ^ 40 * 2277013 * 2
def baseEnd_2277013 : Nat := 779468083690803273243809

theorem tailTrace_2277013 : CollatzResearch.WordTrace tailWord_2277013 prefixEnd_2277013 779468083690803273243809 := by
  unfold tailWord_2277013
  simp only [CollatzResearch.WordTrace]
  refine ⟨83049486899778258704963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55366324599852172469975795 83049486899778258704963693)
  ·
    refine ⟨31143557587416847014361385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83049486899778258704963693 31143557587416847014361385)
    ·
      refine ⟨23357668190562635260771039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31143557587416847014361385 23357668190562635260771039)
      ·
        refine ⟨35036502285843952891156559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357668190562635260771039 35036502285843952891156559)
        ·
          refine ⟨52554753428765929336734839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35036502285843952891156559 52554753428765929336734839)
          ·
            refine ⟨78832130143148894005102259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52554753428765929336734839 78832130143148894005102259)
            ·
              refine ⟨118248195214723341007653389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78832130143148894005102259 118248195214723341007653389)
              ·
                refine ⟨44343073205521252877870021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118248195214723341007653389 44343073205521252877870021)
                ·
                  refine ⟨8314326226035234914600629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44343073205521252877870021 8314326226035234914600629)
                  ·
                    refine ⟨779468083690803273243809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314326226035234914600629 779468083690803273243809)
                    ·
                      rfl

theorem cell22_2277013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2277013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277013 prefixEnd_2277013 := by exact prefixLift 2277013
  have htrace : WordTrace (prefixWord ++ tailWord_2277013) baseStart_2277013 baseEnd_2277013 := by
    simpa [prefixWord, tailWord_2277013, baseEnd_2277013] using wordTrace_append hprefix tailTrace_2277013
  have hstable : (prefixWord ++ tailWord_2277013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277013).length < 2 ^ (prefixWord ++ tailWord_2277013).sum := by decide
  have hdescent : baseEnd_2277013 < baseStart_2277013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277043 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 8]
def baseStart_2277043 : Nat := 118140960795 + 2277043 * 2 ^ 59
def prefixEnd_2277043 : Nat := 4983230072969 + 3 ^ 40 * 2277043 * 2
def baseEnd_2277043 : Nat := 259826117767964398331239

theorem tailTrace_2277043 : CollatzResearch.WordTrace tailWord_2277043 prefixEnd_2277043 259826117767964398331239 := by
  unfold tailWord_2277043
  simp only [CollatzResearch.WordTrace]
  refine ⟨83050581089669573828555783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55367054059779715885703855 83050581089669573828555783)
  ·
    refine ⟨124575871634504360742833675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83050581089669573828555783 124575871634504360742833675)
    ·
      refine ⟨186863807451756541114250513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124575871634504360742833675 186863807451756541114250513)
      ·
        refine ⟨140147855588817405835687885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186863807451756541114250513 140147855588817405835687885)
        ·
          refine ⟨52555445845806527188382957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140147855588817405835687885 52555445845806527188382957)
          ·
            refine ⟨19708292192177447695643609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52555445845806527188382957 19708292192177447695643609)
            ·
              refine ⟨14781219144133085771732707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19708292192177447695643609 14781219144133085771732707)
              ·
                refine ⟨22171828716199628657599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781219144133085771732707 22171828716199628657599061)
                ·
                  refine ⟨259826117767964398331239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22171828716199628657599061 259826117767964398331239)
                  ·
                    rfl

theorem cell22_2277043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_2277043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277043 prefixEnd_2277043 := by exact prefixLift 2277043
  have htrace : WordTrace (prefixWord ++ tailWord_2277043) baseStart_2277043 baseEnd_2277043 := by
    simpa [prefixWord, tailWord_2277043, baseEnd_2277043] using wordTrace_append hprefix tailTrace_2277043
  have hstable : (prefixWord ++ tailWord_2277043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277043).length < 2 ^ (prefixWord ++ tailWord_2277043).sum := by decide
  have hdescent : baseEnd_2277043 < baseStart_2277043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277092 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2277092 : Nat := 118140960795 + 2277092 * 2 ^ 59
def prefixEnd_2277092 : Nat := 4983230072969 + 3 ^ 40 * 2277092 * 2
def baseEnd_2277092 : Nat := 779495127005273400518567

theorem tailTrace_2277092 : CollatzResearch.WordTrace tailWord_2277092 prefixEnd_2277092 779495127005273400518567 := by
  unfold tailWord_2277092
  simp only [CollatzResearch.WordTrace]
  refine ⟨41526184133246027598544765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55368245510994703464726353 41526184133246027598544765)
  ·
    refine ⟨15572319049967260349454287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41526184133246027598544765 15572319049967260349454287)
    ·
      refine ⟨23358478574950890524181431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572319049967260349454287 23358478574950890524181431)
      ·
        refine ⟨35037717862426335786272147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23358478574950890524181431 35037717862426335786272147)
        ·
          refine ⟨52556576793639503679408221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35037717862426335786272147 52556576793639503679408221)
          ·
            refine ⟨19708716297614813879778083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52556576793639503679408221 19708716297614813879778083)
            ·
              refine ⟨29563074446422220819667125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19708716297614813879778083 29563074446422220819667125)
              ·
                refine ⟨2771538229352083201843793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29563074446422220819667125 2771538229352083201843793)
                ·
                  refine ⟨2078653672014062401382845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2771538229352083201843793 2078653672014062401382845)
                  ·
                    refine ⟨779495127005273400518567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078653672014062401382845 779495127005273400518567)
                    ·
                      rfl

theorem cell22_2277092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2277092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277092 prefixEnd_2277092 := by exact prefixLift 2277092
  have htrace : WordTrace (prefixWord ++ tailWord_2277092) baseStart_2277092 baseEnd_2277092 := by
    simpa [prefixWord, tailWord_2277092, baseEnd_2277092] using wordTrace_append hprefix tailTrace_2277092
  have hstable : (prefixWord ++ tailWord_2277092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277092).length < 2 ^ (prefixWord ++ tailWord_2277092).sum := by decide
  have hdescent : baseEnd_2277092 < baseStart_2277092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277225 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_2277225 : Nat := 118140960795 + 2277225 * 2 ^ 59
def prefixEnd_2277225 : Nat := 4983230072969 + 3 ^ 40 * 2277225 * 2
def baseEnd_2277225 : Nat := 779540655623305386943159

theorem tailTrace_2277225 : CollatzResearch.WordTrace tailWord_2277225 prefixEnd_2277225 779540655623305386943159 := by
  unfold tailWord_2277225
  simp only [CollatzResearch.WordTrace]
  refine ⟨83057219175010218911681129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55371479450006812607787419 83057219175010218911681129)
  ·
    refine ⟨62292914381257664183760847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83057219175010218911681129 62292914381257664183760847)
    ·
      refine ⟨93439371571886496275641271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62292914381257664183760847 93439371571886496275641271)
      ·
        refine ⟨140159057357829744413461907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93439371571886496275641271 140159057357829744413461907)
        ·
          refine ⟨210238586036744616620192861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140159057357829744413461907 210238586036744616620192861)
          ·
            refine ⟨78839469763779231232572323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210238586036744616620192861 78839469763779231232572323)
            ·
              refine ⟨118259204645668846848858485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78839469763779231232572323 118259204645668846848858485)
              ·
                refine ⟨11086800435531454392080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118259204645668846848858485 11086800435531454392080483)
                ·
                  refine ⟨16630200653297181588120725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11086800435531454392080483 16630200653297181588120725)
                  ·
                    refine ⟨779540655623305386943159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16630200653297181588120725 779540655623305386943159)
                    ·
                      rfl

theorem cell22_2277225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_2277225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277225 prefixEnd_2277225 := by exact prefixLift 2277225
  have htrace : WordTrace (prefixWord ++ tailWord_2277225) baseStart_2277225 baseEnd_2277225 := by
    simpa [prefixWord, tailWord_2277225, baseEnd_2277225] using wordTrace_append hprefix tailTrace_2277225
  have hstable : (prefixWord ++ tailWord_2277225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277225).length < 2 ^ (prefixWord ++ tailWord_2277225).sum := by decide
  have hdescent : baseEnd_2277225 < baseStart_2277225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277242 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_2277242 : Nat := 118140960795 + 2277242 * 2 ^ 59
def prefixEnd_2277242 : Nat := 4983230072969 + 3 ^ 40 * 2277242 * 2
def baseEnd_2277242 : Nat := 779546475070723009268107

theorem tailTrace_2277242 : CollatzResearch.WordTrace tailWord_2277242 prefixEnd_2277242 779546475070723009268107 := by
  unfold tailWord_2277242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20764459803987157703762495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55371892810632420543366653 20764459803987157703762495)
  ·
    refine ⟨31146689705980736555643743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20764459803987157703762495 31146689705980736555643743)
    ·
      refine ⟨46720034558971104833465615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31146689705980736555643743 46720034558971104833465615)
      ·
        refine ⟨70080051838456657250198423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46720034558971104833465615 70080051838456657250198423)
        ·
          refine ⟨105120077757684985875297635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70080051838456657250198423 105120077757684985875297635)
          ·
            refine ⟨157680116636527478812946453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105120077757684985875297635 157680116636527478812946453)
            ·
              refine ⟨7391255467337225569356865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157680116636527478812946453 7391255467337225569356865)
              ·
                refine ⟨5543441600502919177017649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7391255467337225569356865 5543441600502919177017649)
                ·
                  refine ⟨4157581200377189382763237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5543441600502919177017649 4157581200377189382763237)
                  ·
                    refine ⟨779546475070723009268107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157581200377189382763237 779546475070723009268107)
                    ·
                      rfl

theorem cell22_2277242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_2277242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277242 prefixEnd_2277242 := by exact prefixLift 2277242
  have htrace : WordTrace (prefixWord ++ tailWord_2277242) baseStart_2277242 baseEnd_2277242 := by
    simpa [prefixWord, tailWord_2277242, baseEnd_2277242] using wordTrace_append hprefix tailTrace_2277242
  have hstable : (prefixWord ++ tailWord_2277242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277242).length < 2 ^ (prefixWord ++ tailWord_2277242).sum := by decide
  have hdescent : baseEnd_2277242 < baseStart_2277242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277274 : List Nat := [3, 1, 1, 4, 2, 2, 3, 6]
def baseStart_2277274 : Nat := 118140960795 + 2277274 * 2 ^ 59
def prefixEnd_2277274 : Nat := 4983230072969 + 3 ^ 40 * 2277274 * 2
def baseEnd_2277274 : Nat := 86617492147187288052001

theorem tailTrace_2277274 : CollatzResearch.WordTrace tailWord_2277274 prefixEnd_2277274 86617492147187288052001 := by
  unfold tailWord_2277274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20764751587958175070053719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55372670901221800186809917 20764751587958175070053719)
  ·
    refine ⟨31147127381937262605080579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20764751587958175070053719 31147127381937262605080579)
    ·
      refine ⟨46720691072905893907620869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31147127381937262605080579 46720691072905893907620869)
      ·
        refine ⟨8760129576169855107678913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46720691072905893907620869 8760129576169855107678913)
        ·
          refine ⟨6570097182127391330759185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760129576169855107678913 6570097182127391330759185)
          ·
            refine ⟨4927572886595543498069389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6570097182127391330759185 4927572886595543498069389)
            ·
              refine ⟨1847839832473328811776021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4927572886595543498069389 1847839832473328811776021)
              ·
                refine ⟨86617492147187288052001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1847839832473328811776021 86617492147187288052001)
                ·
                  rfl

theorem cell22_2277274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_2277274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277274 prefixEnd_2277274 := by exact prefixLift 2277274
  have htrace : WordTrace (prefixWord ++ tailWord_2277274) baseStart_2277274 baseEnd_2277274 := by
    simpa [prefixWord, tailWord_2277274, baseEnd_2277274] using wordTrace_append hprefix tailTrace_2277274
  have hstable : (prefixWord ++ tailWord_2277274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277274).length < 2 ^ (prefixWord ++ tailWord_2277274).sum := by decide
  have hdescent : baseEnd_2277274 < baseStart_2277274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277276 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2277276 : Nat := 118140960795 + 2277276 * 2 ^ 59
def prefixEnd_2277276 : Nat := 4983230072969 + 3 ^ 40 * 2277276 * 2
def baseEnd_2277276 : Nat := 779558113965558253918003

theorem tailTrace_2277276 : CollatzResearch.WordTrace tailWord_2277276 prefixEnd_2277276 779558113965558253918003 := by
  unfold tailWord_2277276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41529539648912727310893841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55372719531883636414525121 41529539648912727310893841)
  ·
    refine ⟨31147154736684545483170381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41529539648912727310893841 31147154736684545483170381)
    ·
      refine ⟨11680183026256704556188893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31147154736684545483170381 11680183026256704556188893)
      ·
        refine ⟨4380068634846264208570835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11680183026256704556188893 4380068634846264208570835)
        ·
          refine ⟨6570102952269396312856253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380068634846264208570835 6570102952269396312856253)
          ·
            refine ⟨2463788607101023617321095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6570102952269396312856253 2463788607101023617321095)
            ·
              refine ⟨3695682910651535425981643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463788607101023617321095 3695682910651535425981643)
              ·
                refine ⟨5543524365977303138972465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695682910651535425981643 5543524365977303138972465)
                ·
                  refine ⟨4157643274482977354229349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5543524365977303138972465 4157643274482977354229349)
                  ·
                    refine ⟨779558113965558253918003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157643274482977354229349 779558113965558253918003)
                    ·
                      rfl

theorem cell22_2277276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2277276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277276 prefixEnd_2277276 := by exact prefixLift 2277276
  have htrace : WordTrace (prefixWord ++ tailWord_2277276) baseStart_2277276 baseEnd_2277276 := by
    simpa [prefixWord, tailWord_2277276, baseEnd_2277276] using wordTrace_append hprefix tailTrace_2277276
  have hstable : (prefixWord ++ tailWord_2277276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277276).length < 2 ^ (prefixWord ++ tailWord_2277276).sum := by decide
  have hdescent : baseEnd_2277276 < baseStart_2277276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277357 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2277357 : Nat := 118140960795 + 2277357 * 2 ^ 59
def prefixEnd_2277357 : Nat := 4983230072969 + 3 ^ 40 * 2277357 * 2
def baseEnd_2277357 : Nat := 779585841920901042642755

theorem tailTrace_2277357 : CollatzResearch.WordTrace tailWord_2277357 prefixEnd_2277357 779585841920901042642755 := by
  unfold tailWord_2277357
  simp only [CollatzResearch.WordTrace]
  refine ⟨83062033610532005455486325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55374689073688003636990883 83062033610532005455486325)
  ·
    refine ⟨7787065650987375511451843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83062033610532005455486325 7787065650987375511451843)
    ·
      refine ⟨11680598476481063267177765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7787065650987375511451843 11680598476481063267177765)
      ·
        refine ⟨2190112214340199362595831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11680598476481063267177765 2190112214340199362595831)
        ·
          refine ⟨3285168321510299043893747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190112214340199362595831 3285168321510299043893747)
          ·
            refine ⟨4927752482265448565840621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285168321510299043893747 4927752482265448565840621)
            ·
              refine ⟨1847907180849543212190233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4927752482265448565840621 1847907180849543212190233)
              ·
                refine ⟨1385930385637157409142675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847907180849543212190233 1385930385637157409142675)
                ·
                  refine ⟨2078895578455736113714013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385930385637157409142675 2078895578455736113714013)
                  ·
                    refine ⟨779585841920901042642755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078895578455736113714013 779585841920901042642755)
                    ·
                      rfl

theorem cell22_2277357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2277357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277357 prefixEnd_2277357 := by exact prefixLift 2277357
  have htrace : WordTrace (prefixWord ++ tailWord_2277357) baseStart_2277357 baseEnd_2277357 := by
    simpa [prefixWord, tailWord_2277357, baseEnd_2277357] using wordTrace_append hprefix tailTrace_2277357
  have hstable : (prefixWord ++ tailWord_2277357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277357).length < 2 ^ (prefixWord ++ tailWord_2277357).sum := by decide
  have hdescent : baseEnd_2277357 < baseStart_2277357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277409 : List Nat := [1, 2, 3, 2, 5, 9]
def baseStart_2277409 : Nat := 118140960795 + 2277409 * 2 ^ 59
def prefixEnd_2277409 : Nat := 4983230072969 + 3 ^ 40 * 2277409 * 2
def baseEnd_2277409 : Nat := 9624736328192472102995

theorem tailTrace_2277409 : CollatzResearch.WordTrace tailWord_2277409 prefixEnd_2277409 9624736328192472102995 := by
  unfold tailWord_2277409
  simp only [CollatzResearch.WordTrace]
  refine ⟨83063930206343618336379281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55375953470895745557586187 83063930206343618336379281)
  ·
    refine ⟨62297947654757713752284461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83063930206343618336379281 62297947654757713752284461)
    ·
      refine ⟨23361730370534142657106673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62297947654757713752284461 23361730370534142657106673)
      ·
        refine ⟨17521297777900606992830005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23361730370534142657106673 17521297777900606992830005)
        ·
          refine ⟨1642621666678181905577813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17521297777900606992830005 1642621666678181905577813)
          ·
            refine ⟨9624736328192472102995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1642621666678181905577813 9624736328192472102995)
            ·
              rfl

theorem cell22_2277409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 9].length) (baseStart_2277409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277409 prefixEnd_2277409 := by exact prefixLift 2277409
  have htrace : WordTrace (prefixWord ++ tailWord_2277409) baseStart_2277409 baseEnd_2277409 := by
    simpa [prefixWord, tailWord_2277409, baseEnd_2277409] using wordTrace_append hprefix tailTrace_2277409
  have hstable : (prefixWord ++ tailWord_2277409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277409).length < 2 ^ (prefixWord ++ tailWord_2277409).sum := by decide
  have hdescent : baseEnd_2277409 < baseStart_2277409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277441 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2277441 : Nat := 118140960795 + 2277441 * 2 ^ 59
def prefixEnd_2277441 : Nat := 4983230072969 + 3 ^ 40 * 2277441 * 2
def baseEnd_2277441 : Nat := 779614596837552823542497

theorem tailTrace_2277441 : CollatzResearch.WordTrace tailWord_2277441 prefixEnd_2277441 779614596837552823542497 := by
  unfold tailWord_2277441
  simp only [CollatzResearch.WordTrace]
  refine ⟨83065097342227687801544177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55376731561485125201029451 83065097342227687801544177)
  ·
    refine ⟨62298823006670765851158133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83065097342227687801544177 62298823006670765851158133)
    ·
      refine ⟨5840514656875384298546075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62298823006670765851158133 5840514656875384298546075)
      ·
        refine ⟨8760771985313076447819113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840514656875384298546075 8760771985313076447819113)
        ·
          refine ⟨6570578988984807335864335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760771985313076447819113 6570578988984807335864335)
          ·
            refine ⟨9855868483477211003796503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570578988984807335864335 9855868483477211003796503)
            ·
              refine ⟨14783802725215816505694755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855868483477211003796503 14783802725215816505694755)
              ·
                refine ⟨22175704087823724758542133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14783802725215816505694755 22175704087823724758542133)
                ·
                  refine ⟨2078972258233474196113325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22175704087823724758542133 2078972258233474196113325)
                  ·
                    refine ⟨779614596837552823542497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078972258233474196113325 779614596837552823542497)
                    ·
                      rfl

theorem cell22_2277441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2277441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277441 prefixEnd_2277441 := by exact prefixLift 2277441
  have htrace : WordTrace (prefixWord ++ tailWord_2277441) baseStart_2277441 baseEnd_2277441 := by
    simpa [prefixWord, tailWord_2277441, baseEnd_2277441] using wordTrace_append hprefix tailTrace_2277441
  have hstable : (prefixWord ++ tailWord_2277441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277441).length < 2 ^ (prefixWord ++ tailWord_2277441).sum := by decide
  have hdescent : baseEnd_2277441 < baseStart_2277441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277501 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2277501 : Nat := 118140960795 + 2277501 * 2 ^ 59
def prefixEnd_2277501 : Nat := 4983230072969 + 3 ^ 40 * 2277501 * 2
def baseEnd_2277501 : Nat := 779635136063732667042313

theorem tailTrace_2277501 : CollatzResearch.WordTrace tailWord_2277501 prefixEnd_2277501 779635136063732667042313 := by
  unfold tailWord_2277501
  simp only [CollatzResearch.WordTrace]
  refine ⟨83067285722010318048728357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55378190481340212032485571 83067285722010318048728357)
  ·
    refine ⟨15575116072876934634136567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83067285722010318048728357 15575116072876934634136567)
    ·
      refine ⟨23362674109315401951204851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15575116072876934634136567 23362674109315401951204851)
      ·
        refine ⟨35044011163973102926807277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23362674109315401951204851 35044011163973102926807277)
        ·
          refine ⟨13141504186489913597552729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35044011163973102926807277 13141504186489913597552729)
          ·
            refine ⟨9856128139867435198164547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13141504186489913597552729 9856128139867435198164547)
            ·
              refine ⟨14784192209801152797246821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9856128139867435198164547 14784192209801152797246821)
              ·
                refine ⟨2772036039337716149483779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14784192209801152797246821 2772036039337716149483779)
                ·
                  refine ⟨4158054059006574224225669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772036039337716149483779 4158054059006574224225669)
                  ·
                    refine ⟨779635136063732667042313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158054059006574224225669 779635136063732667042313)
                    ·
                      rfl

theorem cell22_2277501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2277501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277501 prefixEnd_2277501 := by exact prefixLift 2277501
  have htrace : WordTrace (prefixWord ++ tailWord_2277501) baseStart_2277501 baseEnd_2277501 := by
    simpa [prefixWord, tailWord_2277501, baseEnd_2277501] using wordTrace_append hprefix tailTrace_2277501
  have hstable : (prefixWord ++ tailWord_2277501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277501).length < 2 ^ (prefixWord ++ tailWord_2277501).sum := by decide
  have hdescent : baseEnd_2277501 < baseStart_2277501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277526 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2277526 : Nat := 118140960795 + 2277526 * 2 ^ 59
def prefixEnd_2277526 : Nat := 4983230072969 + 3 ^ 40 * 2277526 * 2
def baseEnd_2277526 : Nat := 779643694074640935167237

theorem tailTrace_2277526 : CollatzResearch.WordTrace tailWord_2277526 prefixEnd_2277526 779643694074640935167237 := by
  unfold tailWord_2277526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191762346682484207399277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55378798364613164878925621 5191762346682484207399277)
  ·
    refine ⟨1946910880005931577774729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5191762346682484207399277 1946910880005931577774729)
    ·
      refine ⟨1460183160004448683331047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946910880005931577774729 1460183160004448683331047)
      ·
        refine ⟨2190274740006673024996571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460183160004448683331047 2190274740006673024996571)
        ·
          refine ⟨3285412110010009537494857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190274740006673024996571 3285412110010009537494857)
          ·
            refine ⟨2464059082507507153121143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285412110010009537494857 2464059082507507153121143)
            ·
              refine ⟨3696088623761260729681715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464059082507507153121143 3696088623761260729681715)
              ·
                refine ⟨5544132935641891094522573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696088623761260729681715 5544132935641891094522573)
                ·
                  refine ⟨2079049850865709160445965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5544132935641891094522573 2079049850865709160445965)
                  ·
                    refine ⟨779643694074640935167237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079049850865709160445965 779643694074640935167237)
                    ·
                      rfl

theorem cell22_2277526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2277526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277526 prefixEnd_2277526 := by exact prefixLift 2277526
  have htrace : WordTrace (prefixWord ++ tailWord_2277526) baseStart_2277526 baseEnd_2277526 := by
    simpa [prefixWord, tailWord_2277526, baseEnd_2277526] using wordTrace_append hprefix tailTrace_2277526
  have hstable : (prefixWord ++ tailWord_2277526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277526).length < 2 ^ (prefixWord ++ tailWord_2277526).sum := by decide
  have hdescent : baseEnd_2277526 < baseStart_2277526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277745 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_2277745 : Nat := 118140960795 + 2277745 * 2 ^ 59
def prefixEnd_2277745 : Nat := 4983230072969 + 3 ^ 40 * 2277745 * 2
def baseEnd_2277745 : Nat := 779718662250197363941565

theorem tailTrace_2277745 : CollatzResearch.WordTrace tailWord_2277745 prefixEnd_2277745 779718662250197363941565 := by
  unfold tailWord_2277745
  simp only [CollatzResearch.WordTrace]
  refine ⟨83076185133126347720610689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55384123422084231813740459 83076185133126347720610689)
  ·
    refine ⟨62307138849844760790458017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83076185133126347720610689 62307138849844760790458017)
    ·
      refine ⟨46730354137383570592843513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62307138849844760790458017 46730354137383570592843513)
      ·
        refine ⟨35047765603037677944632635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46730354137383570592843513 35047765603037677944632635)
        ·
          refine ⟨52571648404556516916948953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35047765603037677944632635 52571648404556516916948953)
          ·
            refine ⟨39428736303417387687711715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52571648404556516916948953 39428736303417387687711715)
            ·
              refine ⟨59143104455126081531567573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39428736303417387687711715 59143104455126081531567573)
              ·
                refine ⟨1386166510667017535896115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59143104455126081531567573 1386166510667017535896115)
                ·
                  refine ⟨2079249766000526303844173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386166510667017535896115 2079249766000526303844173)
                  ·
                    refine ⟨779718662250197363941565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079249766000526303844173 779718662250197363941565)
                    ·
                      rfl

theorem cell22_2277745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_2277745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277745 prefixEnd_2277745 := by exact prefixLift 2277745
  have htrace : WordTrace (prefixWord ++ tailWord_2277745) baseStart_2277745 baseEnd_2277745 := by
    simpa [prefixWord, tailWord_2277745, baseEnd_2277745] using wordTrace_append hprefix tailTrace_2277745
  have hstable : (prefixWord ++ tailWord_2277745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277745).length < 2 ^ (prefixWord ++ tailWord_2277745).sum := by decide
  have hdescent : baseEnd_2277745 < baseStart_2277745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277820 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_2277820 : Nat := 118140960795 + 2277820 * 2 ^ 59
def prefixEnd_2277820 : Nat := 4983230072969 + 3 ^ 40 * 2277820 * 2
def baseEnd_2277820 : Nat := 259914778760974056105445

theorem tailTrace_2277820 : CollatzResearch.WordTrace tailWord_2277820 prefixEnd_2277820 259914778760974056105445 := by
  unfold tailWord_2277820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41539460303927317764795457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55385947071903090353060609 41539460303927317764795457)
  ·
    refine ⟨31154595227945488323596593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41539460303927317764795457 31154595227945488323596593)
    ·
      refine ⟨23365946420959116242697445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31154595227945488323596593 23365946420959116242697445)
      ·
        refine ⟨4381114953929834295505771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23365946420959116242697445 4381114953929834295505771)
        ·
          refine ⟨6571672430894751443258657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381114953929834295505771 6571672430894751443258657)
          ·
            refine ⟨4928754323171063582443993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6571672430894751443258657 4928754323171063582443993)
            ·
              refine ⟨3696565742378297686832995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928754323171063582443993 3696565742378297686832995)
              ·
                refine ⟨5544848613567446530249493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696565742378297686832995 5544848613567446530249493)
                ·
                  refine ⟨259914778760974056105445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5544848613567446530249493 259914778760974056105445)
                  ·
                    rfl

theorem cell22_2277820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_2277820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277820 prefixEnd_2277820 := by exact prefixLift 2277820
  have htrace : WordTrace (prefixWord ++ tailWord_2277820) baseStart_2277820 baseEnd_2277820 := by
    simpa [prefixWord, tailWord_2277820, baseEnd_2277820] using wordTrace_append hprefix tailTrace_2277820
  have hstable : (prefixWord ++ tailWord_2277820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277820).length < 2 ^ (prefixWord ++ tailWord_2277820).sum := by decide
  have hdescent : baseEnd_2277820 < baseStart_2277820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277942 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2277942 : Nat := 118140960795 + 2277942 * 2 ^ 59
def prefixEnd_2277942 : Nat := 4983230072969 + 3 ^ 40 * 2277942 * 2
def baseEnd_2277942 : Nat := 779786099376154516765961

theorem tailTrace_2277942 : CollatzResearch.WordTrace tailWord_2277942 prefixEnd_2277942 779786099376154516765961 := by
  unfold tailWord_2277942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192710644588290647845755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55388913542275100243688053 5192710644588290647845755)
  ·
    refine ⟨7789065966882435971768633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5192710644588290647845755 7789065966882435971768633)
    ·
      refine ⟨5841799475161826978826475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7789065966882435971768633 5841799475161826978826475)
      ·
        refine ⟨8762699212742740468239713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841799475161826978826475 8762699212742740468239713)
        ·
          refine ⟨6572024409557055351179785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8762699212742740468239713 6572024409557055351179785)
          ·
            refine ⟨4929018307167791513384839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6572024409557055351179785 4929018307167791513384839)
            ·
              refine ⟨7393527460751687270077259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929018307167791513384839 7393527460751687270077259)
              ·
                refine ⟨11090291191127530905115889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7393527460751687270077259 11090291191127530905115889)
                ·
                  refine ⟨8317718393345648178836917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11090291191127530905115889 8317718393345648178836917)
                  ·
                    refine ⟨779786099376154516765961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8317718393345648178836917 779786099376154516765961)
                    ·
                      rfl

theorem cell22_2277942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2277942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277942 prefixEnd_2277942 := by exact prefixLift 2277942
  have htrace : WordTrace (prefixWord ++ tailWord_2277942) baseStart_2277942 baseEnd_2277942 := by
    simpa [prefixWord, tailWord_2277942, baseEnd_2277942] using wordTrace_append hprefix tailTrace_2277942
  have hstable : (prefixWord ++ tailWord_2277942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277942).length < 2 ^ (prefixWord ++ tailWord_2277942).sum := by decide
  have hdescent : baseEnd_2277942 < baseStart_2277942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277970 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2277970 : Nat := 118140960795 + 2277970 * 2 ^ 59
def prefixEnd_2277970 : Nat := 4983230072969 + 3 ^ 40 * 2277970 * 2
def baseEnd_2277970 : Nat := 779795684348371777065875

theorem tailTrace_2277970 : CollatzResearch.WordTrace tailWord_2277970 prefixEnd_2277970 779795684348371777065875 := by
  unfold tailWord_2277970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771097889327802786887841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55389594371540807431700909 20771097889327802786887841)
  ·
    refine ⟨15578323416995852090165881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20771097889327802786887841 15578323416995852090165881)
    ·
      refine ⟨11683742562746889067624411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15578323416995852090165881 11683742562746889067624411)
      ·
        refine ⟨17525613844120333601436617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683742562746889067624411 17525613844120333601436617)
        ·
          refine ⟨13144210383090250201077463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17525613844120333601436617 13144210383090250201077463)
          ·
            refine ⟨19716315574635375301616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13144210383090250201077463 19716315574635375301616195)
            ·
              refine ⟨29574473361953062952424293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19716315574635375301616195 29574473361953062952424293)
              ·
                refine ⟨5545213755366199303579555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29574473361953062952424293 5545213755366199303579555)
                ·
                  refine ⟨8317820633049298955369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545213755366199303579555 8317820633049298955369333)
                  ·
                    refine ⟨779795684348371777065875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8317820633049298955369333 779795684348371777065875)
                    ·
                      rfl

theorem cell22_2277970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2277970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277970 prefixEnd_2277970 := by exact prefixLift 2277970
  have htrace : WordTrace (prefixWord ++ tailWord_2277970) baseStart_2277970 baseEnd_2277970 := by
    simpa [prefixWord, tailWord_2277970, baseEnd_2277970] using wordTrace_append hprefix tailTrace_2277970
  have hstable : (prefixWord ++ tailWord_2277970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277970).length < 2 ^ (prefixWord ++ tailWord_2277970).sum := by decide
  have hdescent : baseEnd_2277970 < baseStart_2277970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277972 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2277972 : Nat := 118140960795 + 2277972 * 2 ^ 59
def prefixEnd_2277972 : Nat := 4983230072969 + 3 ^ 40 * 2277972 * 2
def baseEnd_2277972 : Nat := 259932122996414812838623

theorem tailTrace_2277972 : CollatzResearch.WordTrace tailWord_2277972 prefixEnd_2277972 259932122996414812838623 := by
  unfold tailWord_2277972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41542232251651982744562085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55389643002202643659416113 41542232251651982744562085)
  ·
    refine ⟨7789168547184746764605391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41542232251651982744562085 7789168547184746764605391)
    ·
      refine ⟨11683752820777120146908087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7789168547184746764605391 11683752820777120146908087)
      ·
        refine ⟨17525629231165680220362131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683752820777120146908087 17525629231165680220362131)
        ·
          refine ⟨26288443846748520330543197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17525629231165680220362131 26288443846748520330543197)
          ·
            refine ⟨9858166442530695123953699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26288443846748520330543197 9858166442530695123953699)
            ·
              refine ⟨14787249663796042685930549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9858166442530695123953699 14787249663796042685930549)
              ·
                refine ⟨1386304655980879001805989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14787249663796042685930549 1386304655980879001805989)
                ·
                  refine ⟨259932122996414812838623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386304655980879001805989 259932122996414812838623)
                  ·
                    rfl

theorem cell22_2277972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2277972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2277972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2277972 prefixEnd_2277972 := by exact prefixLift 2277972
  have htrace : WordTrace (prefixWord ++ tailWord_2277972) baseStart_2277972 baseEnd_2277972 := by
    simpa [prefixWord, tailWord_2277972, baseEnd_2277972] using wordTrace_append hprefix tailTrace_2277972
  have hstable : (prefixWord ++ tailWord_2277972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277972).length < 2 ^ (prefixWord ++ tailWord_2277972).sum := by decide
  have hdescent : baseEnd_2277972 < baseStart_2277972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278015 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 5, 3]
def baseStart_2278015 : Nat := 118140960795 + 2278015 * 2 ^ 59
def prefixEnd_2278015 : Nat := 4983230072969 + 3 ^ 40 * 2278015 * 2
def baseEnd_2278015 : Nat := 779811088768006659690737

theorem tailTrace_2278015 : CollatzResearch.WordTrace tailWord_2278015 prefixEnd_2278015 779811088768006659690737 := by
  unfold tailWord_2278015
  simp only [CollatzResearch.WordTrace]
  refine ⟨83086032842148183832939499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55390688561432122555292999 83086032842148183832939499)
  ·
    refine ⟨124629049263222275749409249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83086032842148183832939499 124629049263222275749409249)
    ·
      refine ⟨93471786947416706812056937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124629049263222275749409249 93471786947416706812056937)
      ·
        refine ⟨70103840210562530109042703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93471786947416706812056937 70103840210562530109042703)
        ·
          refine ⟨105155760315843795163564055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70103840210562530109042703 105155760315843795163564055)
          ·
            refine ⟨157733640473765692745346083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105155760315843795163564055 157733640473765692745346083)
            ·
              refine ⟨236600460710648539118019125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157733640473765692745346083 236600460710648539118019125)
              ·
                refine ⟨22181293191623300542314293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236600460710648539118019125 22181293191623300542314293)
                ·
                  refine ⟨2079496236714684425841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22181293191623300542314293 2079496236714684425841965)
                  ·
                    refine ⟨779811088768006659690737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079496236714684425841965 779811088768006659690737)
                    ·
                      rfl

theorem cell22_2278015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_2278015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278015 prefixEnd_2278015 := by exact prefixLift 2278015
  have htrace : WordTrace (prefixWord ++ tailWord_2278015) baseStart_2278015 baseEnd_2278015 := by
    simpa [prefixWord, tailWord_2278015, baseEnd_2278015] using wordTrace_append hprefix tailTrace_2278015
  have hstable : (prefixWord ++ tailWord_2278015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278015).length < 2 ^ (prefixWord ++ tailWord_2278015).sum := by decide
  have hdescent : baseEnd_2278015 < baseStart_2278015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278045 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 7]
def baseStart_2278045 : Nat := 118140960795 + 2278045 * 2 ^ 59
def prefixEnd_2278045 : Nat := 4983230072969 + 3 ^ 40 * 2278045 * 2
def baseEnd_2278045 : Nat := 259940452793698860480215

theorem tailTrace_2278045 : CollatzResearch.WordTrace tailWord_2278045 prefixEnd_2278045 259940452793698860480215 := by
  unfold tailWord_2278045
  simp only [CollatzResearch.WordTrace]
  refine ⟨83087127032039498956531589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55391418021359665971021059 83087127032039498956531589)
  ·
    refine ⟨15578836318507406054349673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83087127032039498956531589 15578836318507406054349673)
    ·
      refine ⟨11684127238880554540762255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15578836318507406054349673 11684127238880554540762255)
      ·
        refine ⟨17526190858320831811143383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684127238880554540762255 17526190858320831811143383)
        ·
          refine ⟨26289286287481247716715075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17526190858320831811143383 26289286287481247716715075)
          ·
            refine ⟨39433929431221871575072613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26289286287481247716715075 39433929431221871575072613)
            ·
              refine ⟨7393861768354100920326115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39433929431221871575072613 7393861768354100920326115)
              ·
                refine ⟨11090792652531151380489173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7393861768354100920326115 11090792652531151380489173)
                ·
                  refine ⟨259940452793698860480215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11090792652531151380489173 259940452793698860480215)
                  ·
                    rfl

theorem cell22_2278045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_2278045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278045 prefixEnd_2278045 := by exact prefixLift 2278045
  have htrace : WordTrace (prefixWord ++ tailWord_2278045) baseStart_2278045 baseEnd_2278045 := by
    simpa [prefixWord, tailWord_2278045, baseEnd_2278045] using wordTrace_append hprefix tailTrace_2278045
  have hstable : (prefixWord ++ tailWord_2278045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278045).length < 2 ^ (prefixWord ++ tailWord_2278045).sum := by decide
  have hdescent : baseEnd_2278045 < baseStart_2278045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278055 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2278055 : Nat := 118140960795 + 2278055 * 2 ^ 59
def prefixEnd_2278055 : Nat := 4983230072969 + 3 ^ 40 * 2278055 * 2
def baseEnd_2278055 : Nat := 779824781585459888690615

theorem tailTrace_2278055 : CollatzResearch.WordTrace tailWord_2278055 prefixEnd_2278055 779824781585459888690615 := by
  unfold tailWord_2278055
  simp only [CollatzResearch.WordTrace]
  refine ⟨83087491762003270664395619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55391661174668847109597079 83087491762003270664395619)
  ·
    refine ⟨124631237643004905996593429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83087491762003270664395619 124631237643004905996593429)
    ·
      refine ⟨5842089264515854968590317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124631237643004905996593429 5842089264515854968590317)
      ·
        refine ⟨2190783474193445613221369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5842089264515854968590317 2190783474193445613221369)
        ·
          refine ⟨1643087605645084209916027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190783474193445613221369 1643087605645084209916027)
          ·
            refine ⟨2464631408467626314874041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643087605645084209916027 2464631408467626314874041)
            ·
              refine ⟨1848473556350719736155531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464631408467626314874041 1848473556350719736155531)
              ·
                refine ⟨2772710334526079604233297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848473556350719736155531 2772710334526079604233297)
                ·
                  refine ⟨2079532750894559703174973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772710334526079604233297 2079532750894559703174973)
                  ·
                    refine ⟨779824781585459888690615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079532750894559703174973 779824781585459888690615)
                    ·
                      rfl

theorem cell22_2278055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2278055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278055 prefixEnd_2278055 := by exact prefixLift 2278055
  have htrace : WordTrace (prefixWord ++ tailWord_2278055) baseStart_2278055 baseEnd_2278055 := by
    simpa [prefixWord, tailWord_2278055, baseEnd_2278055] using wordTrace_append hprefix tailTrace_2278055
  have hstable : (prefixWord ++ tailWord_2278055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278055).length < 2 ^ (prefixWord ++ tailWord_2278055).sum := by decide
  have hdescent : baseEnd_2278055 < baseStart_2278055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278100 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2278100 : Nat := 118140960795 + 2278100 * 2 ^ 59
def prefixEnd_2278100 : Nat := 4983230072969 + 3 ^ 40 * 2278100 * 2
def baseEnd_2278100 : Nat := 779840186005094771315477

theorem tailTrace_2278100 : CollatzResearch.WordTrace tailWord_2278100 prefixEnd_2278100 779840186005094771315477 := by
  unfold tailWord_2278100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41544566523420121674891877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55392755364560162233189169 41544566523420121674891877)
  ·
    refine ⟨7789606223141272814042227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41544566523420121674891877 7789606223141272814042227)
    ·
      refine ⟨11684409334711909221063341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7789606223141272814042227 11684409334711909221063341)
      ·
        refine ⟨4381653500516965957898753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11684409334711909221063341 4381653500516965957898753)
        ·
          refine ⟨3286240125387724468424065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4381653500516965957898753 3286240125387724468424065)
          ·
            refine ⟨2464680094040793351318049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286240125387724468424065 2464680094040793351318049)
            ·
              refine ⟨1848510070530595013488537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464680094040793351318049 1848510070530595013488537)
              ·
                refine ⟨1386382552897946260116403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848510070530595013488537 1386382552897946260116403)
                ·
                  refine ⟨2079573829346919390174605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386382552897946260116403 2079573829346919390174605)
                  ·
                    refine ⟨779840186005094771315477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079573829346919390174605 779840186005094771315477)
                    ·
                      rfl

theorem cell22_2278100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2278100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278100 prefixEnd_2278100 := by exact prefixLift 2278100
  have htrace : WordTrace (prefixWord ++ tailWord_2278100) baseStart_2278100 baseEnd_2278100 := by
    simpa [prefixWord, tailWord_2278100, baseEnd_2278100] using wordTrace_append hprefix tailTrace_2278100
  have hstable : (prefixWord ++ tailWord_2278100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278100).length < 2 ^ (prefixWord ++ tailWord_2278100).sum := by decide
  have hdescent : baseEnd_2278100 < baseStart_2278100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278105 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_2278105 : Nat := 118140960795 + 2278105 * 2 ^ 59
def prefixEnd_2278105 : Nat := 4983230072969 + 3 ^ 40 * 2278105 * 2
def baseEnd_2278105 : Nat := 779841897607276424940461

theorem tailTrace_2278105 : CollatzResearch.WordTrace tailWord_2278105 prefixEnd_2278105 779841897607276424940461 := by
  unfold tailWord_2278105
  simp only [CollatzResearch.WordTrace]
  refine ⟨83089315411822129203715769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55392876941214752802477179 83089315411822129203715769)
  ·
    refine ⟨62316986558866596902786827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83089315411822129203715769 62316986558866596902786827)
    ·
      refine ⟨93475479838299895354180241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62316986558866596902786827 93475479838299895354180241)
      ·
        refine ⟨70106609878724921515635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93475479838299895354180241 70106609878724921515635181)
        ·
          refine ⟨26289978704521845568363193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70106609878724921515635181 26289978704521845568363193)
          ·
            refine ⟨19717484028391384176272395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26289978704521845568363193 19717484028391384176272395)
            ·
              refine ⟨29576226042587076264408593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19717484028391384176272395 29576226042587076264408593)
              ·
                refine ⟨22182169531940307198306445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29576226042587076264408593 22182169531940307198306445)
                ·
                  refine ⟨8318313574477615199364917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22182169531940307198306445 8318313574477615199364917)
                  ·
                    refine ⟨779841897607276424940461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8318313574477615199364917 779841897607276424940461)
                    ·
                      rfl

theorem cell22_2278105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_2278105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278105 prefixEnd_2278105 := by exact prefixLift 2278105
  have htrace : WordTrace (prefixWord ++ tailWord_2278105) baseStart_2278105 baseEnd_2278105 := by
    simpa [prefixWord, tailWord_2278105, baseEnd_2278105] using wordTrace_append hprefix tailTrace_2278105
  have hstable : (prefixWord ++ tailWord_2278105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278105).length < 2 ^ (prefixWord ++ tailWord_2278105).sum := by decide
  have hdescent : baseEnd_2278105 < baseStart_2278105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278122 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_2278122 : Nat := 118140960795 + 2278122 * 2 ^ 59
def prefixEnd_2278122 : Nat := 4983230072969 + 3 ^ 40 * 2278122 * 2
def baseEnd_2278122 : Nat := 779847717054694047265409

theorem tailTrace_2278122 : CollatzResearch.WordTrace tailWord_2278122 prefixEnd_2278122 779847717054694047265409 := by
  unfold tailWord_2278122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772483863190135276771155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55393290301840360738056413 20772483863190135276771155)
  ·
    refine ⟨31158725794785202915156733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20772483863190135276771155 31158725794785202915156733)
    ·
      refine ⟨11684522173044451093183775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31158725794785202915156733 11684522173044451093183775)
      ·
        refine ⟨17526783259566676639775663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684522173044451093183775 17526783259566676639775663)
        ·
          refine ⟨26290174889350014959663495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17526783259566676639775663 26290174889350014959663495)
          ·
            refine ⟨39435262334025022439495243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26290174889350014959663495 39435262334025022439495243)
            ·
              refine ⟨59152893501037533659242865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39435262334025022439495243 59152893501037533659242865)
              ·
                refine ⟨44364670125778150244432149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59152893501037533659242865 44364670125778150244432149)
                ·
                  refine ⟨2079593912145850792707757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44364670125778150244432149 2079593912145850792707757)
                  ·
                    refine ⟨779847717054694047265409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079593912145850792707757 779847717054694047265409)
                    ·
                      rfl

theorem cell22_2278122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_2278122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278122 prefixEnd_2278122 := by exact prefixLift 2278122
  have htrace : WordTrace (prefixWord ++ tailWord_2278122) baseStart_2278122 baseEnd_2278122 := by
    simpa [prefixWord, tailWord_2278122, baseEnd_2278122] using wordTrace_append hprefix tailTrace_2278122
  have hstable : (prefixWord ++ tailWord_2278122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278122).length < 2 ^ (prefixWord ++ tailWord_2278122).sum := by decide
  have hdescent : baseEnd_2278122 < baseStart_2278122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278173 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2278173 : Nat := 118140960795 + 2278173 * 2 ^ 59
def prefixEnd_2278173 : Nat := 4983230072969 + 3 ^ 40 * 2278173 * 2
def baseEnd_2278173 : Nat := 779865175396946914240253

theorem tailTrace_2278173 : CollatzResearch.WordTrace tailWord_2278173 prefixEnd_2278173 779865175396946914240253 := by
  unfold tailWord_2278173
  simp only [CollatzResearch.WordTrace]
  refine ⟨83091795575575776817191173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55394530383717184544794115 83091795575575776817191173)
  ·
    refine ⟨15579711670420458153223345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83091795575575776817191173 15579711670420458153223345)
    ·
      refine ⟨11684783752815343614917509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15579711670420458153223345 11684783752815343614917509)
      ·
        refine ⟨2190896953652876927797033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11684783752815343614917509 2190896953652876927797033)
        ·
          refine ⟨1643172715239657695847775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190896953652876927797033 1643172715239657695847775)
          ·
            refine ⟨2464759072859486543771663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643172715239657695847775 2464759072859486543771663)
            ·
              refine ⟨3697138609289229815657495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464759072859486543771663 3697138609289229815657495)
              ·
                refine ⟨5545707913933844723486243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697138609289229815657495 5545707913933844723486243)
                ·
                  refine ⟨8318561870900767085229365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545707913933844723486243 8318561870900767085229365)
                  ·
                    refine ⟨779865175396946914240253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8318561870900767085229365 779865175396946914240253)
                    ·
                      rfl

theorem cell22_2278173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2278173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278173 prefixEnd_2278173 := by exact prefixLift 2278173
  have htrace : WordTrace (prefixWord ++ tailWord_2278173) baseStart_2278173 baseEnd_2278173 := by
    simpa [prefixWord, tailWord_2278173, baseEnd_2278173] using wordTrace_append hprefix tailTrace_2278173
  have hstable : (prefixWord ++ tailWord_2278173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278173).length < 2 ^ (prefixWord ++ tailWord_2278173).sum := by decide
  have hdescent : baseEnd_2278173 < baseStart_2278173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278184 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2278184 : Nat := 118140960795 + 2278184 * 2 ^ 59
def prefixEnd_2278184 : Nat := 4983230072969 + 3 ^ 40 * 2278184 * 2
def baseEnd_2278184 : Nat := 779868940921746552215219

theorem tailTrace_2278184 : CollatzResearch.WordTrace tailWord_2278184 prefixEnd_2278184 779868940921746552215219 := by
  unfold tailWord_2278184
  simp only [CollatzResearch.WordTrace]
  refine ⟨41546098389267962847920803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55394797852357283797227737 41546098389267962847920803)
  ·
    refine ⟨62319147583901944271881205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41546098389267962847920803 62319147583901944271881205)
    ·
      refine ⟨5842420085990807275488863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62319147583901944271881205 5842420085990807275488863)
      ·
        refine ⟨8763630128986210913233295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5842420085990807275488863 8763630128986210913233295)
        ·
          refine ⟨13145445193479316369849943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8763630128986210913233295 13145445193479316369849943)
          ·
            refine ⟨19718167790218974554774915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13145445193479316369849943 19718167790218974554774915)
            ·
              refine ⟨29577251685328461832162373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19718167790218974554774915 29577251685328461832162373)
              ·
                refine ⟨5545734690999086593530445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29577251685328461832162373 5545734690999086593530445)
                ·
                  refine ⟨2079650509124657472573917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5545734690999086593530445 2079650509124657472573917)
                  ·
                    refine ⟨779868940921746552215219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079650509124657472573917 779868940921746552215219)
                    ·
                      rfl

theorem cell22_2278184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2278184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278184 prefixEnd_2278184 := by exact prefixLift 2278184
  have htrace : WordTrace (prefixWord ++ tailWord_2278184) baseStart_2278184 baseEnd_2278184 := by
    simpa [prefixWord, tailWord_2278184, baseEnd_2278184] using wordTrace_append hprefix tailTrace_2278184
  have hstable : (prefixWord ++ tailWord_2278184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278184).length < 2 ^ (prefixWord ++ tailWord_2278184).sum := by decide
  have hdescent : baseEnd_2278184 < baseStart_2278184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278197 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2278197 : Nat := 118140960795 + 2278197 * 2 ^ 59
def prefixEnd_2278197 : Nat := 4983230072969 + 3 ^ 40 * 2278197 * 2
def baseEnd_2278197 : Nat := 259957797029139617213393

theorem tailTrace_2278197 : CollatzResearch.WordTrace tailWord_2278197 prefixEnd_2278197 259957797029139617213393 := by
  unfold tailWord_2278197
  simp only [CollatzResearch.WordTrace]
  refine ⟨83092670927488828916064845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55395113951659219277376563 83092670927488828916064845)
  ·
    refine ⟨31159751597808310843524317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83092670927488828916064845 31159751597808310843524317)
    ·
      refine ⟨11684906849178116566321619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31159751597808310843524317 11684906849178116566321619)
      ·
        refine ⟨17527360273767174849482429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684906849178116566321619 17527360273767174849482429)
        ·
          refine ⟨6572760102662690568555911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17527360273767174849482429 6572760102662690568555911)
          ·
            refine ⟨9859140153994035852833867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6572760102662690568555911 9859140153994035852833867)
            ·
              refine ⟨14788710230991053779250801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9859140153994035852833867 14788710230991053779250801)
              ·
                refine ⟨11091532673243290334438101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14788710230991053779250801 11091532673243290334438101)
                ·
                  refine ⟨259957797029139617213393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11091532673243290334438101 259957797029139617213393)
                  ·
                    rfl

theorem cell22_2278197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2278197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278197 prefixEnd_2278197 := by exact prefixLift 2278197
  have htrace : WordTrace (prefixWord ++ tailWord_2278197) baseStart_2278197 baseEnd_2278197 := by
    simpa [prefixWord, tailWord_2278197, baseEnd_2278197] using wordTrace_append hprefix tailTrace_2278197
  have hstable : (prefixWord ++ tailWord_2278197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278197).length < 2 ^ (prefixWord ++ tailWord_2278197).sum := by decide
  have hdescent : baseEnd_2278197 < baseStart_2278197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278231 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 5]
def baseStart_2278231 : Nat := 118140960795 + 2278231 * 2 ^ 59
def prefixEnd_2278231 : Nat := 4983230072969 + 3 ^ 40 * 2278231 * 2
def baseEnd_2278231 : Nat := 259961676660751365430025

theorem tailTrace_2278231 : CollatzResearch.WordTrace tailWord_2278231 prefixEnd_2278231 259961676660751365430025 := by
  unfold tailWord_2278231
  simp only [CollatzResearch.WordTrace]
  refine ⟨83093911009365652722802547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55395940672910435148535031 83093911009365652722802547)
  ·
    refine ⟨124640866514048479084203821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83093911009365652722802547 124640866514048479084203821)
    ·
      refine ⟨46740324942768179656576433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124640866514048479084203821 46740324942768179656576433)
      ·
        refine ⟨35055243707076134742432325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46740324942768179656576433 35055243707076134742432325)
        ·
          refine ⟨6572858195076775264206061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35055243707076134742432325 6572858195076775264206061)
          ·
            refine ⟨2464821823153790724077273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6572858195076775264206061 2464821823153790724077273)
            ·
              refine ⟨1848616367365343043057955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464821823153790724077273 1848616367365343043057955)
              ·
                refine ⟨2772924551048014564586933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848616367365343043057955 2772924551048014564586933)
                ·
                  refine ⟨259961676660751365430025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2772924551048014564586933 259961676660751365430025)
                  ·
                    rfl

theorem cell22_2278231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 5].length) (baseStart_2278231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278231 prefixEnd_2278231 := by exact prefixLift 2278231
  have htrace : WordTrace (prefixWord ++ tailWord_2278231) baseStart_2278231 baseEnd_2278231 := by
    simpa [prefixWord, tailWord_2278231, baseEnd_2278231] using wordTrace_append hprefix tailTrace_2278231
  have hstable : (prefixWord ++ tailWord_2278231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278231).length < 2 ^ (prefixWord ++ tailWord_2278231).sum := by decide
  have hdescent : baseEnd_2278231 < baseStart_2278231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278244 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2278244 : Nat := 118140960795 + 2278244 * 2 ^ 59
def prefixEnd_2278244 : Nat := 4983230072969 + 3 ^ 40 * 2278244 * 2
def baseEnd_2278244 : Nat := 779889480147926395715035

theorem tailTrace_2278244 : CollatzResearch.WordTrace tailWord_2278244 prefixEnd_2278244 779889480147926395715035 := by
  unfold tailWord_2278244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547192579159277971512893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55396256772212370628683857 41547192579159277971512893)
  ·
    refine ⟨15580197217184729239317335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41547192579159277971512893 15580197217184729239317335)
    ·
      refine ⟨23370295825777093858976003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580197217184729239317335 23370295825777093858976003)
      ·
        refine ⟨35055443738665640788464005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23370295825777093858976003 35055443738665640788464005)
        ·
          refine ⟨6572895700999807647837001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35055443738665640788464005 6572895700999807647837001)
          ·
            refine ⟨4929671775749855735877751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6572895700999807647837001 4929671775749855735877751)
            ·
              refine ⟨7394507663624783603816627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929671775749855735877751 7394507663624783603816627)
              ·
                refine ⟨11091761495437175405724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7394507663624783603816627 11091761495437175405724941)
                ·
                  refine ⟨4159410560788940777146853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11091761495437175405724941 4159410560788940777146853)
                  ·
                    refine ⟨779889480147926395715035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159410560788940777146853 779889480147926395715035)
                    ·
                      rfl

theorem cell22_2278244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2278244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278244 prefixEnd_2278244 := by exact prefixLift 2278244
  have htrace : WordTrace (prefixWord ++ tailWord_2278244) baseStart_2278244 baseEnd_2278244 := by
    simpa [prefixWord, tailWord_2278244, baseEnd_2278244] using wordTrace_append hprefix tailTrace_2278244
  have hstable : (prefixWord ++ tailWord_2278244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278244).length < 2 ^ (prefixWord ++ tailWord_2278244).sum := by decide
  have hdescent : baseEnd_2278244 < baseStart_2278244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278257 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2278257 : Nat := 118140960795 + 2278257 * 2 ^ 59
def prefixEnd_2278257 : Nat := 4983230072969 + 3 ^ 40 * 2278257 * 2
def baseEnd_2278257 : Nat := 779893930313598695139995

theorem tailTrace_2278257 : CollatzResearch.WordTrace tailWord_2278257 prefixEnd_2278257 779893930313598695139995 := by
  unfold tailWord_2278257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83094859307271459163249025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55396572871514306108832683 83094859307271459163249025)
  ·
    refine ⟨62321144480453594372436769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83094859307271459163249025 62321144480453594372436769)
    ·
      refine ⟨46740858360340195779327577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62321144480453594372436769 46740858360340195779327577)
      ·
        refine ⟨35055643770255146834495683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46740858360340195779327577 35055643770255146834495683)
        ·
          refine ⟨52583465655382720251743525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35055643770255146834495683 52583465655382720251743525)
          ·
            refine ⟨9859399810384260047201911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52583465655382720251743525 9859399810384260047201911)
            ·
              refine ⟨14789099715576390070802867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9859399810384260047201911 14789099715576390070802867)
              ·
                refine ⟨22183649573364585106204301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789099715576390070802867 22183649573364585106204301)
                ·
                  refine ⟨8318868590011719414826613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22183649573364585106204301 8318868590011719414826613)
                  ·
                    refine ⟨779893930313598695139995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8318868590011719414826613 779893930313598695139995)
                    ·
                      rfl

theorem cell22_2278257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2278257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278257 prefixEnd_2278257 := by exact prefixLift 2278257
  have htrace : WordTrace (prefixWord ++ tailWord_2278257) baseStart_2278257 baseEnd_2278257 := by
    simpa [prefixWord, tailWord_2278257, baseEnd_2278257] using wordTrace_append hprefix tailTrace_2278257
  have hstable : (prefixWord ++ tailWord_2278257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278257).length < 2 ^ (prefixWord ++ tailWord_2278257).sum := by decide
  have hdescent : baseEnd_2278257 < baseStart_2278257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278272 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_2278272 : Nat := 118140960795 + 2278272 * 2 ^ 59
def prefixEnd_2278272 : Nat := 4983230072969 + 3 ^ 40 * 2278272 * 2
def baseEnd_2278272 : Nat := 779899065120143656014949

theorem tailTrace_2278272 : CollatzResearch.WordTrace tailWord_2278272 prefixEnd_2278272 779899065120143656014949 := by
  unfold tailWord_2278272
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547703201108558362522535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55396937601478077816696713 41547703201108558362522535)
  ·
    refine ⟨62321554801662837543783803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41547703201108558362522535 62321554801662837543783803)
    ·
      refine ⟨93482332202494256315675705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62321554801662837543783803 93482332202494256315675705)
      ·
        refine ⟨70111749151870692236756779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93482332202494256315675705 70111749151870692236756779)
        ·
          refine ⟨105167623727806038355135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70111749151870692236756779 105167623727806038355135169)
          ·
            refine ⟨78875717795854528766351377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105167623727806038355135169 78875717795854528766351377)
            ·
              refine ⟨59156788346890896574763533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78875717795854528766351377 59156788346890896574763533)
              ·
                refine ⟨22183795630084086215536325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59156788346890896574763533 22183795630084086215536325)
                ·
                  refine ⟨4159461680640766165413061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22183795630084086215536325 4159461680640766165413061)
                  ·
                    refine ⟨779899065120143656014949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159461680640766165413061 779899065120143656014949)
                    ·
                      rfl

theorem cell22_2278272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_2278272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278272 prefixEnd_2278272 := by exact prefixLift 2278272
  have htrace : WordTrace (prefixWord ++ tailWord_2278272) baseStart_2278272 baseEnd_2278272 := by
    simpa [prefixWord, tailWord_2278272, baseEnd_2278272] using wordTrace_append hprefix tailTrace_2278272
  have hstable : (prefixWord ++ tailWord_2278272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278272).length < 2 ^ (prefixWord ++ tailWord_2278272).sum := by decide
  have hdescent : baseEnd_2278272 < baseStart_2278272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278306 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2278306 : Nat := 118140960795 + 2278306 * 2 ^ 59
def prefixEnd_2278306 : Nat := 4983230072969 + 3 ^ 40 * 2278306 * 2
def baseEnd_2278306 : Nat := 779910704014978900664845

theorem tailTrace_2278306 : CollatzResearch.WordTrace tailWord_2278306 prefixEnd_2278306 779910704014978900664845 := by
  unfold tailWord_2278306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774161621023485132945693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55397764322729293687855181 20774161621023485132945693)
  ·
    refine ⟨7790310607883806924854635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20774161621023485132945693 7790310607883806924854635)
    ·
      refine ⟨11685465911825710387281953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790310607883806924854635 11685465911825710387281953)
      ·
        refine ⟨8764099433869282790461465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11685465911825710387281953 8764099433869282790461465)
        ·
          refine ⟨6573074575401962092846099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8764099433869282790461465 6573074575401962092846099)
          ·
            refine ⟨9859611863102943139269149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573074575401962092846099 9859611863102943139269149)
            ·
              refine ⟨3697354448663603677225931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9859611863102943139269149 3697354448663603677225931)
              ·
                refine ⟨5546031672995405515838897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697354448663603677225931 5546031672995405515838897)
                ·
                  refine ⟨4159523754746554136879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546031672995405515838897 4159523754746554136879173)
                  ·
                    refine ⟨779910704014978900664845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159523754746554136879173 779910704014978900664845)
                    ·
                      rfl

theorem cell22_2278306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2278306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278306 prefixEnd_2278306 := by exact prefixLift 2278306
  have htrace : WordTrace (prefixWord ++ tailWord_2278306) baseStart_2278306 baseEnd_2278306 := by
    simpa [prefixWord, tailWord_2278306, baseEnd_2278306] using wordTrace_append hprefix tailTrace_2278306
  have hstable : (prefixWord ++ tailWord_2278306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278306).length < 2 ^ (prefixWord ++ tailWord_2278306).sum := by decide
  have hdescent : baseEnd_2278306 < baseStart_2278306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278336 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_2278336 : Nat := 118140960795 + 2278336 * 2 ^ 59
def prefixEnd_2278336 : Nat := 4983230072969 + 3 ^ 40 * 2278336 * 2
def baseEnd_2278336 : Nat := 779920973628068822414753

theorem tailTrace_2278336 : CollatzResearch.WordTrace tailWord_2278336 prefixEnd_2278336 779920973628068822414753 := by
  unfold tailWord_2278336
  simp only [CollatzResearch.WordTrace]
  refine ⟨41548870336992627827687431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55398493782656837103583241 41548870336992627827687431)
  ·
    refine ⟨62323305505488941741531147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41548870336992627827687431 62323305505488941741531147)
    ·
      refine ⟨93484958258233412612296721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62323305505488941741531147 93484958258233412612296721)
      ·
        refine ⟨70113718693675059459222541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93484958258233412612296721 70113718693675059459222541)
        ·
          refine ⟨26292644510128147297208453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70113718693675059459222541 26292644510128147297208453)
          ·
            refine ⟨4929870845649027618226585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26292644510128147297208453 4929870845649027618226585)
            ·
              refine ⟨3697403134236770713669939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929870845649027618226585 3697403134236770713669939)
              ·
                refine ⟨5546104701355156070504909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697403134236770713669939 5546104701355156070504909)
                ·
                  refine ⟨2079789263008183526439341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5546104701355156070504909 2079789263008183526439341)
                  ·
                    refine ⟨779920973628068822414753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079789263008183526439341 779920973628068822414753)
                    ·
                      rfl

theorem cell22_2278336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_2278336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278336 prefixEnd_2278336 := by exact prefixLift 2278336
  have htrace : WordTrace (prefixWord ++ tailWord_2278336) baseStart_2278336 baseEnd_2278336 := by
    simpa [prefixWord, tailWord_2278336, baseEnd_2278336] using wordTrace_append hprefix tailTrace_2278336
  have hstable : (prefixWord ++ tailWord_2278336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278336).length < 2 ^ (prefixWord ++ tailWord_2278336).sum := by decide
  have hdescent : baseEnd_2278336 < baseStart_2278336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278456 : List Nat := [2, 1, 2, 1, 5, 3, 1, 7]
def baseStart_2278456 : Nat := 118140960795 + 2278456 * 2 ^ 59
def prefixEnd_2278456 : Nat := 4983230072969 + 3 ^ 40 * 2278456 * 2
def baseEnd_2278456 : Nat := 86662450231158723268265

theorem tailTrace_2278456 : CollatzResearch.WordTrace tailWord_2278456 prefixEnd_2278456 86662450231158723268265 := by
  unfold tailWord_2278456
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551058716775258074871611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55401411622367010766495481 41551058716775258074871611)
  ·
    refine ⟨62326588075162887112307417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41551058716775258074871611 62326588075162887112307417)
    ·
      refine ⟨46744941056372165334230563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62326588075162887112307417 46744941056372165334230563)
      ·
        refine ⟨70117411584558248001345845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46744941056372165334230563 70117411584558248001345845)
        ·
          refine ⟨6573507336052335750126173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70117411584558248001345845 6573507336052335750126173)
          ·
            refine ⟨2465065251019625906297315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6573507336052335750126173 2465065251019625906297315)
            ·
              refine ⟨3697597876529438859445973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465065251019625906297315 3697597876529438859445973)
              ·
                refine ⟨86662450231158723268265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3697597876529438859445973 86662450231158723268265)
                ·
                  rfl

theorem cell22_2278456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_2278456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278456 prefixEnd_2278456 := by exact prefixLift 2278456
  have htrace : WordTrace (prefixWord ++ tailWord_2278456) baseStart_2278456 baseEnd_2278456 := by
    simpa [prefixWord, tailWord_2278456, baseEnd_2278456] using wordTrace_append hprefix tailTrace_2278456
  have hstable : (prefixWord ++ tailWord_2278456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278456).length < 2 ^ (prefixWord ++ tailWord_2278456).sum := by decide
  have hdescent : baseEnd_2278456 < baseStart_2278456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278471 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2278471 : Nat := 118140960795 + 2278471 * 2 ^ 59
def prefixEnd_2278471 : Nat := 4983230072969 + 3 ^ 40 * 2278471 * 2
def baseEnd_2278471 : Nat := 779967186886973470289339

theorem tailTrace_2278471 : CollatzResearch.WordTrace tailWord_2278471 prefixEnd_2278471 779967186886973470289339 := by
  unfold tailWord_2278471
  simp only [CollatzResearch.WordTrace]
  refine ⟨83102664528496173711539267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55401776352330782474359511 83102664528496173711539267)
  ·
    refine ⟨124653996792744260567308901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83102664528496173711539267 124653996792744260567308901)
    ·
      refine ⟨23372624398639548856370419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124653996792744260567308901 23372624398639548856370419)
      ·
        refine ⟨35058936597959323284555629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23372624398639548856370419 35058936597959323284555629)
        ·
          refine ⟨13147101224234746231708361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35058936597959323284555629 13147101224234746231708361)
          ·
            refine ⟨9860325918176059673781271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147101224234746231708361 9860325918176059673781271)
            ·
              refine ⟨14790488877264089510671907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860325918176059673781271 14790488877264089510671907)
              ·
                refine ⟨22185733315896134266007861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14790488877264089510671907 22185733315896134266007861)
                ·
                  refine ⟨2079912498365262587438237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22185733315896134266007861 2079912498365262587438237)
                  ·
                    refine ⟨779967186886973470289339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079912498365262587438237 779967186886973470289339)
                    ·
                      rfl

theorem cell22_2278471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2278471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278471 prefixEnd_2278471 := by exact prefixLift 2278471
  have htrace : WordTrace (prefixWord ++ tailWord_2278471) baseStart_2278471 baseEnd_2278471 := by
    simpa [prefixWord, tailWord_2278471, baseEnd_2278471] using wordTrace_append hprefix tailTrace_2278471
  have hstable : (prefixWord ++ tailWord_2278471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278471).length < 2 ^ (prefixWord ++ tailWord_2278471).sum := by decide
  have hdescent : baseEnd_2278471 < baseStart_2278471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278494 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2278494 : Nat := 118140960795 + 2278494 * 2 ^ 59
def prefixEnd_2278494 : Nat := 4983230072969 + 3 ^ 40 * 2278494 * 2
def baseEnd_2278494 : Nat := 779975060257009076964269

theorem tailTrace_2278494 : CollatzResearch.WordTrace tailWord_2278494 prefixEnd_2278494 779975060257009076964269 := by
  unfold tailWord_2278494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387937925926606079953317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55402335604941899093084357 10387937925926606079953317)
  ·
    refine ⟨1947738361111238639991247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10387937925926606079953317 1947738361111238639991247)
    ·
      refine ⟨2921607541666857959986871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947738361111238639991247 2921607541666857959986871)
      ·
        refine ⟨4382411312500286939980307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921607541666857959986871 4382411312500286939980307)
        ·
          refine ⟨6573616968750430409970461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382411312500286939980307 6573616968750430409970461)
          ·
            refine ⟨2465106363281411403738923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6573616968750430409970461 2465106363281411403738923)
            ·
              refine ⟨3697659544922117105608385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465106363281411403738923 3697659544922117105608385)
              ·
                refine ⟨2773244658691587829206289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697659544922117105608385 2773244658691587829206289)
                ·
                  refine ⟨2079933494018690871904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773244658691587829206289 2079933494018690871904717)
                  ·
                    refine ⟨779975060257009076964269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2079933494018690871904717 779975060257009076964269)
                    ·
                      rfl

theorem cell22_2278494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2278494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278494 prefixEnd_2278494 := by exact prefixLift 2278494
  have htrace : WordTrace (prefixWord ++ tailWord_2278494) baseStart_2278494 baseEnd_2278494 := by
    simpa [prefixWord, tailWord_2278494, baseEnd_2278494] using wordTrace_append hprefix tailTrace_2278494
  have hstable : (prefixWord ++ tailWord_2278494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278494).length < 2 ^ (prefixWord ++ tailWord_2278494).sum := by decide
  have hdescent : baseEnd_2278494 < baseStart_2278494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278582 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2278582 : Nat := 118140960795 + 2278582 * 2 ^ 59
def prefixEnd_2278582 : Nat := 4983230072969 + 3 ^ 40 * 2278582 * 2
def baseEnd_2278582 : Nat := 780005184455406180763999

theorem tailTrace_2278582 : CollatzResearch.WordTrace tailWord_2278582 prefixEnd_2278582 780005184455406180763999 := by
  unfold tailWord_2278582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194169564443377479301875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55404475354062693112553333 5194169564443377479301875)
  ·
    refine ⟨7791254346665066218952813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5194169564443377479301875 7791254346665066218952813)
    ·
      refine ⟨2921720379999399832107305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7791254346665066218952813 2921720379999399832107305)
      ·
        refine ⟨2191290284999549874080479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921720379999399832107305 2191290284999549874080479)
        ·
          refine ⟨3286935427499324811120719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191290284999549874080479 3286935427499324811120719)
          ·
            refine ⟨4930403141248987216681079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286935427499324811120719 4930403141248987216681079)
            ·
              refine ⟨7395604711873480825021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930403141248987216681079 7395604711873480825021619)
              ·
                refine ⟨11093407067810221237532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7395604711873480825021619 11093407067810221237532429)
                ·
                  refine ⟨4160027650428832964074661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11093407067810221237532429 4160027650428832964074661)
                  ·
                    refine ⟨780005184455406180763999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160027650428832964074661 780005184455406180763999)
                    ·
                      rfl

theorem cell22_2278582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2278582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278582 prefixEnd_2278582 := by exact prefixLift 2278582
  have htrace : WordTrace (prefixWord ++ tailWord_2278582) baseStart_2278582 baseEnd_2278582 := by
    simpa [prefixWord, tailWord_2278582, baseEnd_2278582] using wordTrace_append hprefix tailTrace_2278582
  have hstable : (prefixWord ++ tailWord_2278582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278582).length < 2 ^ (prefixWord ++ tailWord_2278582).sum := by decide
  have hdescent : baseEnd_2278582 < baseStart_2278582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278657 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2278657 : Nat := 118140960795 + 2278657 * 2 ^ 59
def prefixEnd_2278657 : Nat := 4983230072969 + 3 ^ 40 * 2278657 * 2
def baseEnd_2278657 : Nat := 780030858488130985138769

theorem tailTrace_2278657 : CollatzResearch.WordTrace tailWord_2278657 prefixEnd_2278657 780030858488130985138769 := by
  unfold tailWord_2278657
  simp only [CollatzResearch.WordTrace]
  refine ⟨83109448505822327477810225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55406299003881551651873483 83109448505822327477810225)
  ·
    refine ⟨62332086379366745608357669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83109448505822327477810225 62332086379366745608357669)
    ·
      refine ⟨11687266196131264801567063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62332086379366745608357669 11687266196131264801567063)
      ·
        refine ⟨17530899294196897202350595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11687266196131264801567063 17530899294196897202350595)
        ·
          refine ⟨26296348941295345803525893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17530899294196897202350595 26296348941295345803525893)
          ·
            refine ⟨4930565426492877338161105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26296348941295345803525893 4930565426492877338161105)
            ·
              refine ⟨3697924069869658003620829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930565426492877338161105 3697924069869658003620829)
              ·
                refine ⟨1386721526201121751357811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3697924069869658003620829 1386721526201121751357811)
                ·
                  refine ⟨2080082289301682627036717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386721526201121751357811 2080082289301682627036717)
                  ·
                    refine ⟨780030858488130985138769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080082289301682627036717 780030858488130985138769)
                    ·
                      rfl

theorem cell22_2278657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2278657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278657 prefixEnd_2278657 := by exact prefixLift 2278657
  have htrace : WordTrace (prefixWord ++ tailWord_2278657) baseStart_2278657 baseEnd_2278657 := by
    simpa [prefixWord, tailWord_2278657, baseEnd_2278657] using wordTrace_append hprefix tailTrace_2278657
  have hstable : (prefixWord ++ tailWord_2278657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278657).length < 2 ^ (prefixWord ++ tailWord_2278657).sum := by decide
  have hdescent : baseEnd_2278657 < baseStart_2278657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278670 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_2278670 : Nat := 118140960795 + 2278670 * 2 ^ 59
def prefixEnd_2278670 : Nat := 4983230072969 + 3 ^ 40 * 2278670 * 2
def baseEnd_2278670 : Nat := 260011769551267761521243

theorem tailTrace_2278670 : CollatzResearch.WordTrace tailWord_2278670 prefixEnd_2278670 260011769551267761521243 := by
  unfold tailWord_2278670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388740331846903837254183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55406615103183487132022309 10388740331846903837254183)
  ·
    refine ⟨15583110497770355755881275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10388740331846903837254183 15583110497770355755881275)
    ·
      refine ⟨23374665746655533633821913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15583110497770355755881275 23374665746655533633821913)
      ·
        refine ⟨17530999309991650225366435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23374665746655533633821913 17530999309991650225366435)
        ·
          refine ⟨26296498964987475338049653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17530999309991650225366435 26296498964987475338049653)
          ·
            refine ⟨2465296777967575812942155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26296498964987475338049653 2465296777967575812942155)
            ·
              refine ⟨3697945166951363719413233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465296777967575812942155 3697945166951363719413233)
              ·
                refine ⟨2773458875213522789559925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697945166951363719413233 2773458875213522789559925)
                ·
                  refine ⟨260011769551267761521243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773458875213522789559925 260011769551267761521243)
                  ·
                    rfl

theorem cell22_2278670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_2278670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278670 prefixEnd_2278670 := by exact prefixLift 2278670
  have htrace : WordTrace (prefixWord ++ tailWord_2278670) baseStart_2278670 baseEnd_2278670 := by
    simpa [prefixWord, tailWord_2278670, baseEnd_2278670] using wordTrace_append hprefix tailTrace_2278670
  have hstable : (prefixWord ++ tailWord_2278670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278670).length < 2 ^ (prefixWord ++ tailWord_2278670).sum := by decide
  have hdescent : baseEnd_2278670 < baseStart_2278670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278674 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2278674 : Nat := 118140960795 + 2278674 * 2 ^ 59
def prefixEnd_2278674 : Nat := 4983230072969 + 3 ^ 40 * 2278674 * 2
def baseEnd_2278674 : Nat := 780036677935548607463717

theorem tailTrace_2278674 : CollatzResearch.WordTrace tailWord_2278674 prefixEnd_2278674 780036677935548607463717 := by
  unfold tailWord_2278674
  simp only [CollatzResearch.WordTrace]
  refine ⟨20777517136690184845294769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55406712364507159587452717 20777517136690184845294769)
  ·
    refine ⟨15583137852517638633971077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20777517136690184845294769 15583137852517638633971077)
    ·
      refine ⟨2921838347347057243869577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15583137852517638633971077 2921838347347057243869577)
      ·
        refine ⟨2191378760510292932902183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921838347347057243869577 2191378760510292932902183)
        ·
          refine ⟨3287068140765439399353275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191378760510292932902183 3287068140765439399353275)
          ·
            refine ⟨4930602211148159099029913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287068140765439399353275 4930602211148159099029913)
            ·
              refine ⟨3697951658361119324272435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930602211148159099029913 3697951658361119324272435)
              ·
                refine ⟨5546927487541678986408653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697951658361119324272435 5546927487541678986408653)
                ·
                  refine ⟨2080097807828129619903245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5546927487541678986408653 2080097807828129619903245)
                  ·
                    refine ⟨780036677935548607463717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080097807828129619903245 780036677935548607463717)
                    ·
                      rfl

theorem cell22_2278674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2278674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278674 prefixEnd_2278674 := by exact prefixLift 2278674
  have htrace : WordTrace (prefixWord ++ tailWord_2278674) baseStart_2278674 baseEnd_2278674 := by
    simpa [prefixWord, tailWord_2278674, baseEnd_2278674] using wordTrace_append hprefix tailTrace_2278674
  have hstable : (prefixWord ++ tailWord_2278674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278674).length < 2 ^ (prefixWord ++ tailWord_2278674).sum := by decide
  have hdescent : baseEnd_2278674 < baseStart_2278674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278732 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_2278732 : Nat := 118140960795 + 2278732 * 2 ^ 59
def prefixEnd_2278732 : Nat := 4983230072969 + 3 ^ 40 * 2278732 * 2
def baseEnd_2278732 : Nat := 260018844173618596504513

theorem tailTrace_2278732 : CollatzResearch.WordTrace tailWord_2278732 prefixEnd_2278732 260018844173618596504513 := by
  unfold tailWord_2278732
  simp only [CollatzResearch.WordTrace]
  refine ⟨41556091990275307643395225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55408122653700410191193633 41556091990275307643395225)
  ·
    refine ⟨31167068992706480732546419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41556091990275307643395225 31167068992706480732546419)
    ·
      refine ⟨46750603489059721098819629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31167068992706480732546419 46750603489059721098819629)
      ·
        refine ⟨17531476308397395412057361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46750603489059721098819629 17531476308397395412057361)
        ·
          refine ⟨13148607231298046559043021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17531476308397395412057361 13148607231298046559043021)
          ·
            refine ⟨4930727711736767459641133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13148607231298046559043021 4930727711736767459641133)
            ·
              refine ⟨1849022891901287797365425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4930727711736767459641133 1849022891901287797365425)
              ·
                refine ⟨1386767168925965848024069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849022891901287797365425 1386767168925965848024069)
                ·
                  refine ⟨260018844173618596504513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386767168925965848024069 260018844173618596504513)
                  ·
                    rfl

theorem cell22_2278732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_2278732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278732 prefixEnd_2278732 := by exact prefixLift 2278732
  have htrace : WordTrace (prefixWord ++ tailWord_2278732) baseStart_2278732 baseEnd_2278732 := by
    simpa [prefixWord, tailWord_2278732, baseEnd_2278732] using wordTrace_append hprefix tailTrace_2278732
  have hstable : (prefixWord ++ tailWord_2278732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278732).length < 2 ^ (prefixWord ++ tailWord_2278732).sum := by decide
  have hdescent : baseEnd_2278732 < baseStart_2278732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278743 : List Nat := [1, 1, 3, 2, 3, 3, 2, 7]
def baseStart_2278743 : Nat := 118140960795 + 2278743 * 2 ^ 59
def prefixEnd_2278743 : Nat := 4983230072969 + 3 ^ 40 * 2278743 * 2
def baseEnd_2278743 : Nat := 86673366449517269720945

theorem tailTrace_2278743 : CollatzResearch.WordTrace tailWord_2278743 prefixEnd_2278743 86673366449517269720945 := by
  unfold tailWord_2278743
  simp only [CollatzResearch.WordTrace]
  refine ⟨83112585183510764165440883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55408390122340509443627255 83112585183510764165440883)
  ·
    refine ⟨124668877775266146248161325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83112585183510764165440883 124668877775266146248161325)
    ·
      refine ⟨46750829165724804843060497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124668877775266146248161325 46750829165724804843060497)
      ·
        refine ⟨35063121874293603632295373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46750829165724804843060497 35063121874293603632295373)
        ·
          refine ⟨13148670702860101362110765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35063121874293603632295373 13148670702860101362110765)
          ·
            refine ⟨4930751513572538010791537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13148670702860101362110765 4930751513572538010791537)
            ·
              refine ⟨3698063635179403508093653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930751513572538010791537 3698063635179403508093653)
              ·
                refine ⟨86673366449517269720945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3698063635179403508093653 86673366449517269720945)
                ·
                  rfl

theorem cell22_2278743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 7].length) (baseStart_2278743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278743 prefixEnd_2278743 := by exact prefixLift 2278743
  have htrace : WordTrace (prefixWord ++ tailWord_2278743) baseStart_2278743 baseEnd_2278743 := by
    simpa [prefixWord, tailWord_2278743, baseEnd_2278743] using wordTrace_append hprefix tailTrace_2278743
  have hstable : (prefixWord ++ tailWord_2278743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278743).length < 2 ^ (prefixWord ++ tailWord_2278743).sum := by decide
  have hdescent : baseEnd_2278743 < baseStart_2278743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278762 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2278762 : Nat := 118140960795 + 2278762 * 2 ^ 59
def prefixEnd_2278762 : Nat := 4983230072969 + 3 ^ 40 * 2278762 * 2
def baseEnd_2278762 : Nat := 780066802133945711263447

theorem tailTrace_2278762 : CollatzResearch.WordTrace tailWord_2278762 prefixEnd_2278762 780066802133945711263447 := by
  unfold tailWord_2278762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20778319542610482602595635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55408852113627953606921693 20778319542610482602595635)
  ·
    refine ⟨31167479313915723903893453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20778319542610482602595635 31167479313915723903893453)
    ·
      refine ⟨11687804742718396463960045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31167479313915723903893453 11687804742718396463960045)
      ·
        refine ⟨4382926778519398673985017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11687804742718396463960045 4382926778519398673985017)
        ·
          refine ⟨3287195083889549005488763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4382926778519398673985017 3287195083889549005488763)
          ·
            refine ⟨4930792625834323508233145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287195083889549005488763 4930792625834323508233145)
            ·
              refine ⟨3698094469375742631174859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930792625834323508233145 3698094469375742631174859)
              ·
                refine ⟨5547141704063613946762289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698094469375742631174859 5547141704063613946762289)
                ·
                  refine ⟨4160356278047710460071717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5547141704063613946762289 4160356278047710460071717)
                  ·
                    refine ⟨780066802133945711263447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160356278047710460071717 780066802133945711263447)
                    ·
                      rfl

theorem cell22_2278762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2278762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278762 prefixEnd_2278762 := by exact prefixLift 2278762
  have htrace : WordTrace (prefixWord ++ tailWord_2278762) baseStart_2278762 baseEnd_2278762 := by
    simpa [prefixWord, tailWord_2278762, baseEnd_2278762] using wordTrace_append hprefix tailTrace_2278762
  have hstable : (prefixWord ++ tailWord_2278762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278762).length < 2 ^ (prefixWord ++ tailWord_2278762).sum := by decide
  have hdescent : baseEnd_2278762 < baseStart_2278762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278833 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 8]
def baseStart_2278833 : Nat := 118140960795 + 2278833 * 2 ^ 59
def prefixEnd_2278833 : Nat := 4983230072969 + 3 ^ 40 * 2278833 * 2
def baseEnd_2278833 : Nat := 260030368961641730912743

theorem tailTrace_2278833 : CollatzResearch.WordTrace tailWord_2278833 prefixEnd_2278833 260030368961641730912743 := by
  unfold tailWord_2278833
  simp only [CollatzResearch.WordTrace]
  refine ⟨83115867753184709536217153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55410578502123139690811435 83115867753184709536217153)
  ·
    refine ⟨62336900814888532152162865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83115867753184709536217153 62336900814888532152162865)
    ·
      refine ⟨46752675611166399114122149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62336900814888532152162865 46752675611166399114122149)
      ·
        refine ⟨8766126677093699833897903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46752675611166399114122149 8766126677093699833897903)
        ·
          refine ⟨13149190015640549750846855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8766126677093699833897903 13149190015640549750846855)
          ·
            refine ⟨19723785023460824626270283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13149190015640549750846855 19723785023460824626270283)
            ·
              refine ⟨29585677535191236939405425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19723785023460824626270283 29585677535191236939405425)
              ·
                refine ⟨22189258151393427704554069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29585677535191236939405425 22189258151393427704554069)
                ·
                  refine ⟨260030368961641730912743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22189258151393427704554069 260030368961641730912743)
                  ·
                    rfl

theorem cell22_2278833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_2278833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278833 prefixEnd_2278833 := by exact prefixLift 2278833
  have htrace : WordTrace (prefixWord ++ tailWord_2278833) baseStart_2278833 baseEnd_2278833 := by
    simpa [prefixWord, tailWord_2278833, baseEnd_2278833] using wordTrace_append hprefix tailTrace_2278833
  have hstable : (prefixWord ++ tailWord_2278833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278833).length < 2 ^ (prefixWord ++ tailWord_2278833).sum := by decide
  have hdescent : baseEnd_2278833 < baseStart_2278833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278848 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_2278848 : Nat := 118140960795 + 2278848 * 2 ^ 59
def prefixEnd_2278848 : Nat := 4983230072969 + 3 ^ 40 * 2278848 * 2
def baseEnd_2278848 : Nat := 780096241691470153613183

theorem tailTrace_2278848 : CollatzResearch.WordTrace tailWord_2278848 prefixEnd_2278848 780096241691470153613183 := by
  unfold tailWord_2278848
  simp only [CollatzResearch.WordTrace]
  refine ⟨41558207424065183549006599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55410943232086911398675465 41558207424065183549006599)
  ·
    refine ⟨62337311136097775323509899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41558207424065183549006599 62337311136097775323509899)
    ·
      refine ⟨93505966704146662985264849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62337311136097775323509899 93505966704146662985264849)
      ·
        refine ⟨70129475028109997238948637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93505966704146662985264849 70129475028109997238948637)
        ·
          refine ⟨26298553135541248964605739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70129475028109997238948637 26298553135541248964605739)
          ·
            refine ⟨39447829703311873446908609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26298553135541248964605739 39447829703311873446908609)
            ·
              refine ⟨29585872277483905085181457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39447829703311873446908609 29585872277483905085181457)
              ·
                refine ⟨22189404208112928813886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29585872277483905085181457 22189404208112928813886093)
                ·
                  refine ⟨8321026578042348305207285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22189404208112928813886093 8321026578042348305207285)
                  ·
                    refine ⟨780096241691470153613183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8321026578042348305207285 780096241691470153613183)
                    ·
                      rfl

theorem cell22_2278848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_2278848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278848 prefixEnd_2278848 := by exact prefixLift 2278848
  have htrace : WordTrace (prefixWord ++ tailWord_2278848) baseStart_2278848 baseEnd_2278848 := by
    simpa [prefixWord, tailWord_2278848, baseEnd_2278848] using wordTrace_append hprefix tailTrace_2278848
  have hstable : (prefixWord ++ tailWord_2278848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278848).length < 2 ^ (prefixWord ++ tailWord_2278848).sum := by decide
  have hdescent : baseEnd_2278848 < baseStart_2278848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278863 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_2278863 : Nat := 118140960795 + 2278863 * 2 ^ 59
def prefixEnd_2278863 : Nat := 4983230072969 + 3 ^ 40 * 2278863 * 2
def baseEnd_2278863 : Nat := 780101376498015114488137

theorem tailTrace_2278863 : CollatzResearch.WordTrace tailWord_2278863 prefixEnd_2278863 780101376498015114488137 := by
  unfold tailWord_2278863
  simp only [CollatzResearch.WordTrace]
  refine ⟨83116961943076024659809243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55411307962050683106539495 83116961943076024659809243)
  ·
    refine ⟨124675442914614036989713865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83116961943076024659809243 124675442914614036989713865)
    ·
      refine ⟨93506582185960527742285399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124675442914614036989713865 93506582185960527742285399)
      ·
        refine ⟨140259873278940791613428099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93506582185960527742285399 140259873278940791613428099)
        ·
          refine ⟨210389809918411187420142149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140259873278940791613428099 210389809918411187420142149)
          ·
            refine ⟨39448089359702097641276653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210389809918411187420142149 39448089359702097641276653)
            ·
              refine ⟨14793033509888286615478745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39448089359702097641276653 14793033509888286615478745)
              ·
                refine ⟨11094775132416214961609059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14793033509888286615478745 11094775132416214961609059)
                ·
                  refine ⟨16642162698624322442413589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11094775132416214961609059 16642162698624322442413589)
                  ·
                    refine ⟨780101376498015114488137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16642162698624322442413589 780101376498015114488137)
                    ·
                      rfl

theorem cell22_2278863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_2278863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278863 prefixEnd_2278863 := by exact prefixLift 2278863
  have htrace : WordTrace (prefixWord ++ tailWord_2278863) baseStart_2278863 baseEnd_2278863 := by
    simpa [prefixWord, tailWord_2278863, baseEnd_2278863] using wordTrace_append hprefix tailTrace_2278863
  have hstable : (prefixWord ++ tailWord_2278863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278863).length < 2 ^ (prefixWord ++ tailWord_2278863).sum := by decide
  have hdescent : baseEnd_2278863 < baseStart_2278863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278901 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 4]
def baseStart_2278901 : Nat := 118140960795 + 2278901 * 2 ^ 59
def prefixEnd_2278901 : Nat := 4983230072969 + 3 ^ 40 * 2278901 * 2
def baseEnd_2278901 : Nat := 260038128224865227346007

theorem tailTrace_2278901 : CollatzResearch.WordTrace tailWord_2278901 prefixEnd_2278901 260038128224865227346007 := by
  unfold tailWord_2278901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83118347916938357149692557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55412231944625571433128371 83118347916938357149692557)
  ·
    refine ⟨31169380468851883931134709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83118347916938357149692557 31169380468851883931134709)
    ·
      refine ⟨2922129418954864118543879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31169380468851883931134709 2922129418954864118543879)
      ·
        refine ⟨4383194128432296177815819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922129418954864118543879 4383194128432296177815819)
        ·
          refine ⟨6574791192648444266723729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4383194128432296177815819 6574791192648444266723729)
          ·
            refine ⟨4931093394486333200042797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574791192648444266723729 4931093394486333200042797)
            ·
              refine ⟨1849160022932374950016049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931093394486333200042797 1849160022932374950016049)
              ·
                refine ⟨1386870017199281212512037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849160022932374950016049 1386870017199281212512037)
                ·
                  refine ⟨260038128224865227346007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386870017199281212512037 260038128224865227346007)
                  ·
                    rfl

theorem cell22_2278901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_2278901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278901 prefixEnd_2278901 := by exact prefixLift 2278901
  have htrace : WordTrace (prefixWord ++ tailWord_2278901) baseStart_2278901 baseEnd_2278901 := by
    simpa [prefixWord, tailWord_2278901, baseEnd_2278901] using wordTrace_append hprefix tailTrace_2278901
  have hstable : (prefixWord ++ tailWord_2278901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278901).length < 2 ^ (prefixWord ++ tailWord_2278901).sum := by decide
  have hdescent : baseEnd_2278901 < baseStart_2278901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278970 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_2278970 : Nat := 118140960795 + 2278970 * 2 ^ 59
def prefixEnd_2278970 : Nat := 4983230072969 + 3 ^ 40 * 2278970 * 2
def baseEnd_2278970 : Nat := 780138004784702502062809

theorem tailTrace_2278970 : CollatzResearch.WordTrace tailWord_2278970 prefixEnd_2278970 780138004784702502062809 := by
  unfold tailWord_2278970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20780216138422095483488591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55413909702458921289302909 20780216138422095483488591)
  ·
    refine ⟨31170324207633143225232887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20780216138422095483488591 31170324207633143225232887)
    ·
      refine ⟨46755486311449714837849331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31170324207633143225232887 46755486311449714837849331)
      ·
        refine ⟨70133229467174572256773997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46755486311449714837849331 70133229467174572256773997)
        ·
          refine ⟨26299961050190464596290249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70133229467174572256773997 26299961050190464596290249)
          ·
            refine ⟨19724970787642848447217687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26299961050190464596290249 19724970787642848447217687)
            ·
              refine ⟨29587456181464272670826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19724970787642848447217687 29587456181464272670826531)
              ·
                refine ⟨44381184272196409006239797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29587456181464272670826531 44381184272196409006239797)
                ·
                  refine ⟨4160736025518413344334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44381184272196409006239797 4160736025518413344334981)
                  ·
                    refine ⟨780138004784702502062809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160736025518413344334981 780138004784702502062809)
                    ·
                      rfl

theorem cell22_2278970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_2278970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278970 prefixEnd_2278970 := by exact prefixLift 2278970
  have htrace : WordTrace (prefixWord ++ tailWord_2278970) baseStart_2278970 baseEnd_2278970 := by
    simpa [prefixWord, tailWord_2278970, baseEnd_2278970] using wordTrace_append hprefix tailTrace_2278970
  have hstable : (prefixWord ++ tailWord_2278970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278970).length < 2 ^ (prefixWord ++ tailWord_2278970).sum := by decide
  have hdescent : baseEnd_2278970 < baseStart_2278970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278972 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2278972 : Nat := 118140960795 + 2278972 * 2 ^ 59
def prefixEnd_2278972 : Nat := 4983230072969 + 3 ^ 40 * 2278972 * 2
def baseEnd_2278972 : Nat := 780138689425575163512803

theorem tailTrace_2278972 : CollatzResearch.WordTrace tailWord_2278972 prefixEnd_2278972 780138689425575163512803 := by
  unfold tailWord_2278972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41560468749840568137763585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55413958333120757517018113 41560468749840568137763585)
  ·
    refine ⟨31170351562380426103322689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41560468749840568137763585 31170351562380426103322689)
    ·
      refine ⟨23377763671785319577492017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31170351562380426103322689 23377763671785319577492017)
      ·
        refine ⟨17533322753838989683119013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23377763671785319577492017 17533322753838989683119013)
        ·
          refine ⟨3287498016344810565584815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17533322753838989683119013 3287498016344810565584815)
          ·
            refine ⟨4931247024517215848377223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287498016344810565584815 4931247024517215848377223)
            ·
              refine ⟨7396870536775823772565835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931247024517215848377223 7396870536775823772565835)
              ·
                refine ⟨11095305805163735658848753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396870536775823772565835 11095305805163735658848753)
                ·
                  refine ⟨8321479353872801744136565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11095305805163735658848753 8321479353872801744136565)
                  ·
                    refine ⟨780138689425575163512803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8321479353872801744136565 780138689425575163512803)
                    ·
                      rfl

theorem cell22_2278972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2278972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2278972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2278972 prefixEnd_2278972 := by exact prefixLift 2278972
  have htrace : WordTrace (prefixWord ++ tailWord_2278972) baseStart_2278972 baseEnd_2278972 := by
    simpa [prefixWord, tailWord_2278972, baseEnd_2278972] using wordTrace_append hprefix tailTrace_2278972
  have hstable : (prefixWord ++ tailWord_2278972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278972).length < 2 ^ (prefixWord ++ tailWord_2278972).sum := by decide
  have hdescent : baseEnd_2278972 < baseStart_2278972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279004 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2279004 : Nat := 118140960795 + 2279004 * 2 ^ 59
def prefixEnd_2279004 : Nat := 4983230072969 + 3 ^ 40 * 2279004 * 2
def baseEnd_2279004 : Nat := 780149643679537746712705

theorem tailTrace_2279004 : CollatzResearch.WordTrace tailWord_2279004 prefixEnd_2279004 780149643679537746712705 := by
  unfold tailWord_2279004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41561052317782602870346033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55414736423710137160461377 41561052317782602870346033)
  ·
    refine ⟨31170789238336952152759525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41561052317782602870346033 31170789238336952152759525)
    ·
      refine ⟨5844522982188178528642411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31170789238336952152759525 5844522982188178528642411)
      ·
        refine ⟨8766784473282267792963617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5844522982188178528642411 8766784473282267792963617)
        ·
          refine ⟨6575088354961700844722713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766784473282267792963617 6575088354961700844722713)
          ·
            refine ⟨4931316266221275633542035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6575088354961700844722713 4931316266221275633542035)
            ·
              refine ⟨7396974399331913450313053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931316266221275633542035 7396974399331913450313053)
              ·
                refine ⟨2773865399749467543867395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7396974399331913450313053 2773865399749467543867395)
                ·
                  refine ⟨4160798099624201315801093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773865399749467543867395 4160798099624201315801093)
                  ·
                    refine ⟨780149643679537746712705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160798099624201315801093 780149643679537746712705)
                    ·
                      rfl

theorem cell22_2279004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2279004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279004 prefixEnd_2279004 := by exact prefixLift 2279004
  have htrace : WordTrace (prefixWord ++ tailWord_2279004) baseStart_2279004 baseEnd_2279004 := by
    simpa [prefixWord, tailWord_2279004, baseEnd_2279004] using wordTrace_append hprefix tailTrace_2279004
  have hstable : (prefixWord ++ tailWord_2279004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279004).length < 2 ^ (prefixWord ++ tailWord_2279004).sum := by decide
  have hdescent : baseEnd_2279004 < baseStart_2279004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279045 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_2279045 : Nat := 118140960795 + 2279045 * 2 ^ 59
def prefixEnd_2279045 : Nat := 4983230072969 + 3 ^ 40 * 2279045 * 2
def baseEnd_2279045 : Nat := 780163678817427306437579

theorem tailTrace_2279045 : CollatzResearch.WordTrace tailWord_2279045 prefixEnd_2279045 780163678817427306437579 := by
  unfold tailWord_2279045
  simp only [CollatzResearch.WordTrace]
  refine ⟨83123600028416669742934589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55415733352277779828623059 83123600028416669742934589)
  ·
    refine ⟨31171350010656251153600471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83123600028416669742934589 31171350010656251153600471)
    ·
      refine ⟨46757025015984376730400707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31171350010656251153600471 46757025015984376730400707)
      ·
        refine ⟨70135537523976565095601061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46757025015984376730400707 70135537523976565095601061)
        ·
          refine ⟨13150413285745605955425199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70135537523976565095601061 13150413285745605955425199)
          ·
            refine ⟨19725619928618408933137799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13150413285745605955425199 19725619928618408933137799)
            ·
              refine ⟨29588429892927613399706699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19725619928618408933137799 29588429892927613399706699)
              ·
                refine ⟨44382644839391420099560049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29588429892927613399706699 44382644839391420099560049)
                ·
                  refine ⟨33286983629543565074670037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44382644839391420099560049 33286983629543565074670037)
                  ·
                    refine ⟨780163678817427306437579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33286983629543565074670037 780163678817427306437579)
                    ·
                      rfl

theorem cell22_2279045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_2279045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279045 prefixEnd_2279045 := by exact prefixLift 2279045
  have htrace : WordTrace (prefixWord ++ tailWord_2279045) baseStart_2279045 baseEnd_2279045 := by
    simpa [prefixWord, tailWord_2279045, baseEnd_2279045] using wordTrace_append hprefix tailTrace_2279045
  have hstable : (prefixWord ++ tailWord_2279045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279045).length < 2 ^ (prefixWord ++ tailWord_2279045).sum := by decide
  have hdescent : baseEnd_2279045 < baseStart_2279045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279047 : List Nat := [1, 1, 4, 2, 1, 3, 4, 6]
def baseStart_2279047 : Nat := 118140960795 + 2279047 * 2 ^ 59
def prefixEnd_2279047 : Nat := 4983230072969 + 3 ^ 40 * 2279047 * 2
def baseEnd_2279047 : Nat := 86684929273144440876397

theorem tailTrace_2279047 : CollatzResearch.WordTrace tailWord_2279047 prefixEnd_2279047 86684929273144440876397 := by
  unfold tailWord_2279047
  simp only [CollatzResearch.WordTrace]
  refine ⟨83123672974409424084507395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55415781982939616056338263 83123672974409424084507395)
  ·
    refine ⟨124685509461614136126761093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83123672974409424084507395 124685509461614136126761093)
    ·
      refine ⟨23378533024052650523767705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124685509461614136126761093 23378533024052650523767705)
      ·
        refine ⟨17533899768039487892825779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23378533024052650523767705 17533899768039487892825779)
        ·
          refine ⟨26300849652059231839238669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533899768039487892825779 26300849652059231839238669)
          ·
            refine ⟨9862818619522211939714501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26300849652059231839238669 9862818619522211939714501)
            ·
              refine ⟨1849278491160414738696469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9862818619522211939714501 1849278491160414738696469)
              ·
                refine ⟨86684929273144440876397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1849278491160414738696469 86684929273144440876397)
                ·
                  rfl

theorem cell22_2279047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 6].length) (baseStart_2279047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279047 prefixEnd_2279047 := by exact prefixLift 2279047
  have htrace : WordTrace (prefixWord ++ tailWord_2279047) baseStart_2279047 baseEnd_2279047 := by
    simpa [prefixWord, tailWord_2279047, baseEnd_2279047] using wordTrace_append hprefix tailTrace_2279047
  have hstable : (prefixWord ++ tailWord_2279047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279047).length < 2 ^ (prefixWord ++ tailWord_2279047).sum := by decide
  have hdescent : baseEnd_2279047 < baseStart_2279047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279075 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 7]
def baseStart_2279075 : Nat := 118140960795 + 2279075 * 2 ^ 59
def prefixEnd_2279075 : Nat := 4983230072969 + 3 ^ 40 * 2279075 * 2
def baseEnd_2279075 : Nat := 260057982810172409395829

theorem tailTrace_2279075 : CollatzResearch.WordTrace tailWord_2279075 prefixEnd_2279075 260057982810172409395829 := by
  unfold tailWord_2279075
  simp only [CollatzResearch.WordTrace]
  refine ⟨83124694218307984866526679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55416462812205323244351119 83124694218307984866526679)
  ·
    refine ⟨124687041327461977299790019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83124694218307984866526679 124687041327461977299790019)
    ·
      refine ⟨187030561991192965949685029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124687041327461977299790019 187030561991192965949685029)
      ·
        refine ⟨35068230373348681115565943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187030561991192965949685029 35068230373348681115565943)
        ·
          refine ⟨52602345560023021673348915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35068230373348681115565943 52602345560023021673348915)
          ·
            refine ⟨78903518340034532510023373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52602345560023021673348915 78903518340034532510023373)
            ·
              refine ⟨29588819377512949691258765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78903518340034532510023373 29588819377512949691258765)
              ·
                refine ⟨11095807266567356134222037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29588819377512949691258765 11095807266567356134222037)
                ·
                  refine ⟨260057982810172409395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11095807266567356134222037 260057982810172409395829)
                  ·
                    rfl

theorem cell22_2279075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_2279075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279075 prefixEnd_2279075 := by exact prefixLift 2279075
  have htrace : WordTrace (prefixWord ++ tailWord_2279075) baseStart_2279075 baseEnd_2279075 := by
    simpa [prefixWord, tailWord_2279075, baseEnd_2279075] using wordTrace_append hprefix tailTrace_2279075
  have hstable : (prefixWord ++ tailWord_2279075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279075).length < 2 ^ (prefixWord ++ tailWord_2279075).sum := by decide
  have hdescent : baseEnd_2279075 < baseStart_2279075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279120 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_2279120 : Nat := 118140960795 + 2279120 * 2 ^ 59
def prefixEnd_2279120 : Nat := 4983230072969 + 3 ^ 40 * 2279120 * 2
def baseEnd_2279120 : Nat := 260063117616717370270783

theorem tailTrace_2279120 : CollatzResearch.WordTrace tailWord_2279120 prefixEnd_2279120 260063117616717370270783 := by
  unfold tailWord_2279120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41563167751572478775957407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55417557002096638367943209 41563167751572478775957407)
  ·
    refine ⟨62344751627358718163936111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41563167751572478775957407 62344751627358718163936111)
    ·
      refine ⟨93517127441038077245904167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62344751627358718163936111 93517127441038077245904167)
      ·
        refine ⟨140275691161557115868856251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93517127441038077245904167 140275691161557115868856251)
        ·
          refine ⟨210413536742335673803284377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140275691161557115868856251 210413536742335673803284377)
          ·
            refine ⟨157810152556751755352463283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210413536742335673803284377 157810152556751755352463283)
            ·
              refine ⟨236715228835127633028694925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157810152556751755352463283 236715228835127633028694925)
              ·
                refine ⟨88768210813172862385760597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236715228835127633028694925 88768210813172862385760597)
                ·
                  refine ⟨260063117616717370270783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88768210813172862385760597 260063117616717370270783)
                  ·
                    rfl

theorem cell22_2279120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_2279120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279120 prefixEnd_2279120 := by exact prefixLift 2279120
  have htrace : WordTrace (prefixWord ++ tailWord_2279120) baseStart_2279120 baseEnd_2279120 := by
    simpa [prefixWord, tailWord_2279120, baseEnd_2279120] using wordTrace_append hprefix tailTrace_2279120
  have hstable : (prefixWord ++ tailWord_2279120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279120).length < 2 ^ (prefixWord ++ tailWord_2279120).sum := by decide
  have hdescent : baseEnd_2279120 < baseStart_2279120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279321 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_2279321 : Nat := 118140960795 + 2279321 * 2 ^ 59
def prefixEnd_2279321 : Nat := 4983230072969 + 3 ^ 40 * 2279321 * 2
def baseEnd_2279321 : Nat := 780258159257854586536733

theorem tailTrace_2279321 : CollatzResearch.WordTrace tailWord_2279321 prefixEnd_2279321 780258159257854586536733 := by
  unfold tailWord_2279321
  simp only [CollatzResearch.WordTrace]
  refine ⟨83133666575416768879981817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55422444383611179253321211 83133666575416768879981817)
  ·
    refine ⟨62350249931562576659986363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83133666575416768879981817 62350249931562576659986363)
    ·
      refine ⟨93525374897343864989979545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62350249931562576659986363 93525374897343864989979545)
      ·
        refine ⟨70144031173007898742484659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93525374897343864989979545 70144031173007898742484659)
        ·
          refine ⟨105216046759511848113726989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70144031173007898742484659 105216046759511848113726989)
          ·
            refine ⟨39456017534816943042647621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105216046759511848113726989 39456017534816943042647621)
            ·
              refine ⟨7398003287778176820496429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39456017534816943042647621 7398003287778176820496429)
              ·
                refine ⟨2774251232916816307686161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7398003287778176820496429 2774251232916816307686161)
                ·
                  refine ⟨2080688424687612230764621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2774251232916816307686161 2080688424687612230764621)
                  ·
                    refine ⟨780258159257854586536733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080688424687612230764621 780258159257854586536733)
                    ·
                      rfl

theorem cell22_2279321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_2279321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279321 prefixEnd_2279321 := by exact prefixLift 2279321
  have htrace : WordTrace (prefixWord ++ tailWord_2279321) baseStart_2279321 baseEnd_2279321 := by
    simpa [prefixWord, tailWord_2279321, baseEnd_2279321] using wordTrace_append hprefix tailTrace_2279321
  have hstable : (prefixWord ++ tailWord_2279321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279321).length < 2 ^ (prefixWord ++ tailWord_2279321).sum := by decide
  have hdescent : baseEnd_2279321 < baseStart_2279321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279342 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2279342 : Nat := 118140960795 + 2279342 * 2 ^ 59
def prefixEnd_2279342 : Nat := 4983230072969 + 3 ^ 40 * 2279342 * 2
def baseEnd_2279342 : Nat := 780265347987017531761669

theorem tailTrace_2279342 : CollatzResearch.WordTrace tailWord_2279342 prefixEnd_2279342 780265347987017531761669 := by
  unfold tailWord_2279342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391804063542586183312035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55422955005560459644330853 10391804063542586183312035)
  ·
    refine ⟨15587706095313879274968053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10391804063542586183312035 15587706095313879274968053)
    ·
      refine ⟨1461347446435676182028255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15587706095313879274968053 1461347446435676182028255)
      ·
        refine ⟨2192021169653514273042383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461347446435676182028255 2192021169653514273042383)
        ·
          refine ⟨3288031754480271409563575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192021169653514273042383 3288031754480271409563575)
          ·
            refine ⟨4932047631720407114345363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288031754480271409563575 4932047631720407114345363)
            ·
              refine ⟨7398071447580610671518045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932047631720407114345363 7398071447580610671518045)
              ·
                refine ⟨2774276792842729001819267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7398071447580610671518045 2774276792842729001819267)
                ·
                  refine ⟨4161415189264093502728901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774276792842729001819267 4161415189264093502728901)
                  ·
                    refine ⟨780265347987017531761669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161415189264093502728901 780265347987017531761669)
                    ·
                      rfl

theorem cell22_2279342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2279342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279342 prefixEnd_2279342 := by exact prefixLift 2279342
  have htrace : WordTrace (prefixWord ++ tailWord_2279342) baseStart_2279342 baseEnd_2279342 := by
    simpa [prefixWord, tailWord_2279342, baseEnd_2279342] using wordTrace_append hprefix tailTrace_2279342
  have hstable : (prefixWord ++ tailWord_2279342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279342).length < 2 ^ (prefixWord ++ tailWord_2279342).sum := by decide
  have hdescent : baseEnd_2279342 < baseStart_2279342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279424 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_2279424 : Nat := 118140960795 + 2279424 * 2 ^ 59
def prefixEnd_2279424 : Nat := 4983230072969 + 3 ^ 40 * 2279424 * 2
def baseEnd_2279424 : Nat := 260097806087598883737139

theorem tailTrace_2279424 : CollatzResearch.WordTrace tailWord_2279424 prefixEnd_2279424 260097806087598883737139 := by
  unfold tailWord_2279424
  simp only [CollatzResearch.WordTrace]
  refine ⟨41568711647021808735490663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55424948862695744980654217 41568711647021808735490663)
  ·
    refine ⟨62353067470532713103235995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41568711647021808735490663 62353067470532713103235995)
    ·
      refine ⟨93529601205799069654853993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62353067470532713103235995 93529601205799069654853993)
      ·
        refine ⟨70147200904349302241140495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93529601205799069654853993 70147200904349302241140495)
        ·
          refine ⟨105220801356523953361710743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70147200904349302241140495 105220801356523953361710743)
          ·
            refine ⟨157831202034785930042566115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105220801356523953361710743 157831202034785930042566115)
            ·
              refine ⟨236746803052178895063849173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157831202034785930042566115 236746803052178895063849173)
              ·
                refine ⟨5548753196535442853058965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 236746803052178895063849173 5548753196535442853058965)
                ·
                  refine ⟨260097806087598883737139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5548753196535442853058965 260097806087598883737139)
                  ·
                    rfl

theorem cell22_2279424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_2279424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279424 prefixEnd_2279424 := by exact prefixLift 2279424
  have htrace : WordTrace (prefixWord ++ tailWord_2279424) baseStart_2279424 baseEnd_2279424 := by
    simpa [prefixWord, tailWord_2279424, baseEnd_2279424] using wordTrace_append hprefix tailTrace_2279424
  have hstable : (prefixWord ++ tailWord_2279424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279424).length < 2 ^ (prefixWord ++ tailWord_2279424).sum := by decide
  have hdescent : baseEnd_2279424 < baseStart_2279424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279458 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2279458 : Nat := 118140960795 + 2279458 * 2 ^ 59
def prefixEnd_2279458 : Nat := 4983230072969 + 3 ^ 40 * 2279458 * 2
def baseEnd_2279458 : Nat := 260101685719210631953771

theorem tailTrace_2279458 : CollatzResearch.WordTrace tailWord_2279458 prefixEnd_2279458 260101685719210631953771 := by
  unfold tailWord_2279458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20784665843980110319429757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55425775583946960851812685 20784665843980110319429757)
  ·
    refine ⟨7794249691492541369786159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20784665843980110319429757 7794249691492541369786159)
    ·
      refine ⟨11691374537238812054679239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7794249691492541369786159 11691374537238812054679239)
      ·
        refine ⟨17537061805858218082018859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11691374537238812054679239 17537061805858218082018859)
        ·
          refine ⟨26305592708787327123028289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537061805858218082018859 26305592708787327123028289)
          ·
            refine ⟨19729194531590495342271217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305592708787327123028289 19729194531590495342271217)
            ·
              refine ⟨14796895898692871506703413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19729194531590495342271217 14796895898692871506703413)
              ·
                refine ⟨1387208990502456703753445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14796895898692871506703413 1387208990502456703753445)
                ·
                  refine ⟨260101685719210631953771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387208990502456703753445 260101685719210631953771)
                  ·
                    rfl

theorem cell22_2279458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2279458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279458 prefixEnd_2279458 := by exact prefixLift 2279458
  have htrace : WordTrace (prefixWord ++ tailWord_2279458) baseStart_2279458 baseEnd_2279458 := by
    simpa [prefixWord, tailWord_2279458, baseEnd_2279458] using wordTrace_append hprefix tailTrace_2279458
  have hstable : (prefixWord ++ tailWord_2279458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279458).length < 2 ^ (prefixWord ++ tailWord_2279458).sum := by decide
  have hdescent : baseEnd_2279458 < baseStart_2279458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279469 : List Nat := [1, 5, 16]
def baseStart_2279469 : Nat := 118140960795 + 2279469 * 2 ^ 59
def prefixEnd_2279469 : Nat := 4983230072969 + 3 ^ 40 * 2279469 * 2
def baseEnd_2279469 : Nat := 356794157605135589317

theorem tailTrace_2279469 : CollatzResearch.WordTrace tailWord_2279469 prefixEnd_2279469 356794157605135589317 := by
  unfold tailWord_2279469
  simp only [CollatzResearch.WordTrace]
  refine ⟨83139064578880590156369461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55426043052587060104246307 83139064578880590156369461)
  ·
    refine ⟨7794287304270055327159637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83139064578880590156369461 7794287304270055327159637)
    ·
      refine ⟨356794157605135589317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 7794287304270055327159637 356794157605135589317)
      ·
        rfl

theorem cell22_2279469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 16].length) (baseStart_2279469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279469 prefixEnd_2279469 := by exact prefixLift 2279469
  have htrace : WordTrace (prefixWord ++ tailWord_2279469) baseStart_2279469 baseEnd_2279469 := by
    simpa [prefixWord, tailWord_2279469, baseEnd_2279469] using wordTrace_append hprefix tailTrace_2279469
  have hstable : (prefixWord ++ tailWord_2279469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279469).length < 2 ^ (prefixWord ++ tailWord_2279469).sum := by decide
  have hdescent : baseEnd_2279469 < baseStart_2279469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279473 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_2279473 : Nat := 118140960795 + 2279473 * 2 ^ 59
def prefixEnd_2279473 : Nat := 4983230072969 + 3 ^ 40 * 2279473 * 2
def baseEnd_2279473 : Nat := 780310191964176856736267

theorem tailTrace_2279473 : CollatzResearch.WordTrace tailWord_2279473 prefixEnd_2279473 780310191964176856736267 := by
  unfold tailWord_2279473
  simp only [CollatzResearch.WordTrace]
  refine ⟨83139210470866098839515073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55426140313910732559676715 83139210470866098839515073)
  ·
    refine ⟨62354407853149574129636305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83139210470866098839515073 62354407853149574129636305)
    ·
      refine ⟨46765805889862180597227229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62354407853149574129636305 46765805889862180597227229)
      ·
        refine ⟨17537177208698317723960211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46765805889862180597227229 17537177208698317723960211)
        ·
          refine ⟨26305765813047476585940317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537177208698317723960211 26305765813047476585940317)
          ·
            refine ⟨9864662179892803719727619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26305765813047476585940317 9864662179892803719727619)
            ·
              refine ⟨14796993269839205579591429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864662179892803719727619 14796993269839205579591429)
              ·
                refine ⟨2774436238094851046173393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14796993269839205579591429 2774436238094851046173393)
                ·
                  refine ⟨2080827178571138284630045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2774436238094851046173393 2080827178571138284630045)
                  ·
                    refine ⟨780310191964176856736267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080827178571138284630045 780310191964176856736267)
                    ·
                      rfl

theorem cell22_2279473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_2279473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279473 prefixEnd_2279473 := by exact prefixLift 2279473
  have htrace : WordTrace (prefixWord ++ tailWord_2279473) baseStart_2279473 baseEnd_2279473 := by
    simpa [prefixWord, tailWord_2279473, baseEnd_2279473] using wordTrace_append hprefix tailTrace_2279473
  have hstable : (prefixWord ++ tailWord_2279473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279473).length < 2 ^ (prefixWord ++ tailWord_2279473).sum := by decide
  have hdescent : baseEnd_2279473 < baseStart_2279473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279535 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 1, 3]
def baseStart_2279535 : Nat := 118140960795 + 2279535 * 2 ^ 59
def prefixEnd_2279535 : Nat := 4983230072969 + 3 ^ 40 * 2279535 * 2
def baseEnd_2279535 : Nat := 780331415831229361686077

theorem tailTrace_2279535 : CollatzResearch.WordTrace tailWord_2279535 prefixEnd_2279535 780331415831229361686077 := by
  unfold tailWord_2279535
  simp only [CollatzResearch.WordTrace]
  refine ⟨83141471796641483428272059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55427647864427655618848039 83141471796641483428272059)
  ·
    refine ⟨124712207694962225142408089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83141471796641483428272059 124712207694962225142408089)
    ·
      refine ⟨93534155771221668856806067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124712207694962225142408089 93534155771221668856806067)
      ·
        refine ⟨140301233656832503285209101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93534155771221668856806067 140301233656832503285209101)
        ·
          refine ⟨52612962621312188731953413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140301233656832503285209101 52612962621312188731953413)
          ·
            refine ⟨9864930491496035387241265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52612962621312188731953413 9864930491496035387241265)
            ·
              refine ⟨7398697868622026540430949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9864930491496035387241265 7398697868622026540430949)
              ·
                refine ⟨1387255850366629976330803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7398697868622026540430949 1387255850366629976330803)
                ·
                  refine ⟨2080883775549944964496205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387255850366629976330803 2080883775549944964496205)
                  ·
                    refine ⟨780331415831229361686077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080883775549944964496205 780331415831229361686077)
                    ·
                      rfl

theorem cell22_2279535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_2279535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279535 prefixEnd_2279535 := by exact prefixLift 2279535
  have htrace : WordTrace (prefixWord ++ tailWord_2279535) baseStart_2279535 baseEnd_2279535 := by
    simpa [prefixWord, tailWord_2279535, baseEnd_2279535] using wordTrace_append hprefix tailTrace_2279535
  have hstable : (prefixWord ++ tailWord_2279535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279535).length < 2 ^ (prefixWord ++ tailWord_2279535).sum := by decide
  have hdescent : baseEnd_2279535 < baseStart_2279535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279612 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_2279612 : Nat := 118140960795 + 2279612 * 2 ^ 59
def prefixEnd_2279612 : Nat := 4983230072969 + 3 ^ 40 * 2279612 * 2
def baseEnd_2279612 : Nat := 780357774504826827510841

theorem tailTrace_2279612 : CollatzResearch.WordTrace tailWord_2279612 prefixEnd_2279612 780357774504826827510841 := by
  unfold tailWord_2279612
  simp only [CollatzResearch.WordTrace]
  refine ⟨41572140108681262789412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55429520144908350385883393 41572140108681262789412545)
  ·
    refine ⟨31179105081510947092059409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41572140108681262789412545 31179105081510947092059409)
    ·
      refine ⟨23384328811133210319044557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31179105081510947092059409 23384328811133210319044557)
      ·
        refine ⟨8769123304174953869641709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23384328811133210319044557 8769123304174953869641709)
        ·
          refine ⟨3288421239065607701115641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8769123304174953869641709 3288421239065607701115641)
          ·
            refine ⟨2466315929299205775836731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288421239065607701115641 2466315929299205775836731)
            ·
              refine ⟨3699473893948808663755097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466315929299205775836731 3699473893948808663755097)
              ·
                refine ⟨2774605420461606497816323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699473893948808663755097 2774605420461606497816323)
                ·
                  refine ⟨4161908130692409746724485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774605420461606497816323 4161908130692409746724485)
                  ·
                    refine ⟨780357774504826827510841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161908130692409746724485 780357774504826827510841)
                    ·
                      rfl

theorem cell22_2279612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_2279612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279612 prefixEnd_2279612 := by exact prefixLift 2279612
  have htrace : WordTrace (prefixWord ++ tailWord_2279612) baseStart_2279612 baseEnd_2279612 := by
    simpa [prefixWord, tailWord_2279612, baseEnd_2279612] using wordTrace_append hprefix tailTrace_2279612
  have hstable : (prefixWord ++ tailWord_2279612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279612).length < 2 ^ (prefixWord ++ tailWord_2279612).sum := by decide
  have hdescent : baseEnd_2279612 < baseStart_2279612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279621 : List Nat := [1, 3, 1, 1, 1, 1, 6, 8]
def baseStart_2279621 : Nat := 118140960795 + 2279621 * 2 ^ 59
def prefixEnd_2279621 : Nat := 4983230072969 + 3 ^ 40 * 2279621 * 2
def baseEnd_2279621 : Nat := 86706761709861533781757

theorem tailTrace_2279621 : CollatzResearch.WordTrace tailWord_2279621 prefixEnd_2279621 86706761709861533781757 := by
  unfold tailWord_2279621
  simp only [CollatzResearch.WordTrace]
  refine ⟨83144608474329920115902717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55429738982886613410601811 83144608474329920115902717)
  ·
    refine ⟨31179228177873720043463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83144608474329920115902717 31179228177873720043463519)
    ·
      refine ⟨46768842266810580065195279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31179228177873720043463519 46768842266810580065195279)
      ·
        refine ⟨70153263400215870097792919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46768842266810580065195279 70153263400215870097792919)
        ·
          refine ⟨105229895100323805146689379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70153263400215870097792919 105229895100323805146689379)
          ·
            refine ⟨157844842650485707720034069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105229895100323805146689379 157844842650485707720034069)
            ·
              refine ⟨7398976999241517549376597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157844842650485707720034069 7398976999241517549376597)
              ·
                refine ⟨86706761709861533781757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7398976999241517549376597 86706761709861533781757)
                ·
                  rfl

theorem cell22_2279621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 8].length) (baseStart_2279621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279621 prefixEnd_2279621 := by exact prefixLift 2279621
  have htrace : WordTrace (prefixWord ++ tailWord_2279621) baseStart_2279621 baseEnd_2279621 := by
    simpa [prefixWord, tailWord_2279621, baseEnd_2279621] using wordTrace_append hprefix tailTrace_2279621
  have hstable : (prefixWord ++ tailWord_2279621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279621).length < 2 ^ (prefixWord ++ tailWord_2279621).sum := by decide
  have hdescent : baseEnd_2279621 < baseStart_2279621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279644 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_2279644 : Nat := 118140960795 + 2279644 * 2 ^ 59
def prefixEnd_2279644 : Nat := 4983230072969 + 3 ^ 40 * 2279644 * 2
def baseEnd_2279644 : Nat := 260122909586263136903581

theorem tailTrace_2279644 : CollatzResearch.WordTrace tailWord_2279644 prefixEnd_2279644 260122909586263136903581 := by
  unfold tailWord_2279644
  simp only [CollatzResearch.WordTrace]
  refine ⟨41572723676623297521994993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55430298235497730029326657 41572723676623297521994993)
  ·
    refine ⟨31179542757467473141496245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41572723676623297521994993 31179542757467473141496245)
    ·
      refine ⟨2923082133512575607015273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31179542757467473141496245 2923082133512575607015273)
      ·
        refine ⟨2192311600134431705261455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923082133512575607015273 2192311600134431705261455)
        ·
          refine ⟨3288467400201647557892183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192311600134431705261455 3288467400201647557892183)
          ·
            refine ⟨4932701100302471336838275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288467400201647557892183 4932701100302471336838275)
            ·
              refine ⟨7399051650453707005257413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932701100302471336838275 7399051650453707005257413)
              ·
                refine ⟨1387322184460070063485765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7399051650453707005257413 1387322184460070063485765)
                ·
                  refine ⟨260122909586263136903581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387322184460070063485765 260122909586263136903581)
                  ·
                    rfl

theorem cell22_2279644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_2279644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279644 prefixEnd_2279644 := by exact prefixLift 2279644
  have htrace : WordTrace (prefixWord ++ tailWord_2279644) baseStart_2279644 baseEnd_2279644 := by
    simpa [prefixWord, tailWord_2279644, baseEnd_2279644] using wordTrace_append hprefix tailTrace_2279644
  have hstable : (prefixWord ++ tailWord_2279644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279644).length < 2 ^ (prefixWord ++ tailWord_2279644).sum := by decide
  have hdescent : baseEnd_2279644 < baseStart_2279644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279655 : List Nat := [1, 1, 5, 3, 1, 3, 1, 7]
def baseStart_2279655 : Nat := 118140960795 + 2279655 * 2 ^ 59
def prefixEnd_2279655 : Nat := 4983230072969 + 3 ^ 40 * 2279655 * 2
def baseEnd_2279655 : Nat := 86708054920398783187301

theorem tailTrace_2279655 : CollatzResearch.WordTrace tailWord_2279655 prefixEnd_2279655 86708054920398783187301 := by
  unfold tailWord_2279655
  simp only [CollatzResearch.WordTrace]
  refine ⟨83145848556206743922640419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55430565704137829281760279 83145848556206743922640419)
  ·
    refine ⟨124718772834310115883960629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83145848556206743922640419 124718772834310115883960629)
    ·
      refine ⟨11692384953216573364121309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124718772834310115883960629 11692384953216573364121309)
      ·
        refine ⟨4384644357456215011545491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11692384953216573364121309 4384644357456215011545491)
        ·
          refine ⟨6576966536184322517318237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384644357456215011545491 6576966536184322517318237)
          ·
            refine ⟨2466362451069120943994339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6576966536184322517318237 2466362451069120943994339)
            ·
              refine ⟨3699543676603681415991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466362451069120943994339 3699543676603681415991509)
              ·
                refine ⟨86708054920398783187301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3699543676603681415991509 86708054920398783187301)
                ·
                  rfl

theorem cell22_2279655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 7].length) (baseStart_2279655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279655 prefixEnd_2279655 := by exact prefixLift 2279655
  have htrace : WordTrace (prefixWord ++ tailWord_2279655) baseStart_2279655 baseEnd_2279655 := by
    simpa [prefixWord, tailWord_2279655, baseEnd_2279655] using wordTrace_append hprefix tailTrace_2279655
  have hstable : (prefixWord ++ tailWord_2279655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279655).length < 2 ^ (prefixWord ++ tailWord_2279655).sum := by decide
  have hdescent : baseEnd_2279655 < baseStart_2279655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279670 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_2279670 : Nat := 118140960795 + 2279670 * 2 ^ 59
def prefixEnd_2279670 : Nat := 4983230072969 + 3 ^ 40 * 2279670 * 2
def baseEnd_2279670 : Nat := 780377629090134009560663

theorem tailTrace_2279670 : CollatzResearch.WordTrace tailWord_2279670 prefixEnd_2279670 780377629090134009560663 := by
  unfold tailWord_2279670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196649728197025092777279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55430930434101600989624309 5196649728197025092777279)
  ·
    refine ⟨7794974592295537639165919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196649728197025092777279 7794974592295537639165919)
    ·
      refine ⟨11692461888443306458748879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7794974592295537639165919 11692461888443306458748879)
      ·
        refine ⟨17538692832664959688123319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11692461888443306458748879 17538692832664959688123319)
        ·
          refine ⟨26308039248997439532184979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17538692832664959688123319 26308039248997439532184979)
          ·
            refine ⟨39462058873496159298277469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26308039248997439532184979 39462058873496159298277469)
            ·
              refine ⟨14798272077561059736854051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39462058873496159298277469 14798272077561059736854051)
              ·
                refine ⟨22197408116341589605281077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14798272077561059736854051 22197408116341589605281077)
                ·
                  refine ⟨2081007010907024025495101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22197408116341589605281077 2081007010907024025495101)
                  ·
                    refine ⟨780377629090134009560663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081007010907024025495101 780377629090134009560663)
                    ·
                      rfl

theorem cell22_2279670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_2279670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279670 prefixEnd_2279670 := by exact prefixLift 2279670
  have htrace : WordTrace (prefixWord ++ tailWord_2279670) baseStart_2279670 baseEnd_2279670 := by
    simpa [prefixWord, tailWord_2279670, baseEnd_2279670] using wordTrace_append hprefix tailTrace_2279670
  have hstable : (prefixWord ++ tailWord_2279670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279670).length < 2 ^ (prefixWord ++ tailWord_2279670).sum := by decide
  have hdescent : baseEnd_2279670 < baseStart_2279670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279713 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2279713 : Nat := 118140960795 + 2279713 * 2 ^ 59
def prefixEnd_2279713 : Nat := 4983230072969 + 3 ^ 40 * 2279713 * 2
def baseEnd_2279713 : Nat := 780392348868896230735531

theorem tailTrace_2279713 : CollatzResearch.WordTrace tailWord_2279713 prefixEnd_2279713 780392348868896230735531 := by
  unfold tailWord_2279713
  simp only [CollatzResearch.WordTrace]
  refine ⟨83147963989996619828251793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55431975993331079885501195 83147963989996619828251793)
  ·
    refine ⟨62360972992497464871188845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83147963989996619828251793 62360972992497464871188845)
    ·
      refine ⟨23385364872186549326695817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62360972992497464871188845 23385364872186549326695817)
      ·
        refine ⟨17539023654139911995021863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23385364872186549326695817 17539023654139911995021863)
        ·
          refine ⟨26308535481209867992532795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17539023654139911995021863 26308535481209867992532795)
          ·
            refine ⟨39462803221814801988799193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26308535481209867992532795 39462803221814801988799193)
            ·
              refine ⟨29597102416361101491599395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39462803221814801988799193 29597102416361101491599395)
              ·
                refine ⟨44395653624541652237399093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29597102416361101491599395 44395653624541652237399093)
                ·
                  refine ⟨4162092527300779897256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44395653624541652237399093 4162092527300779897256165)
                  ·
                    refine ⟨780392348868896230735531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4162092527300779897256165 780392348868896230735531)
                    ·
                      rfl

theorem cell22_2279713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2279713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279713 prefixEnd_2279713 := by exact prefixLift 2279713
  have htrace : WordTrace (prefixWord ++ tailWord_2279713) baseStart_2279713 baseEnd_2279713 := by
    simpa [prefixWord, tailWord_2279713, baseEnd_2279713] using wordTrace_append hprefix tailTrace_2279713
  have hstable : (prefixWord ++ tailWord_2279713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279713).length < 2 ^ (prefixWord ++ tailWord_2279713).sum := by decide
  have hdescent : baseEnd_2279713 < baseStart_2279713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279717 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 5]
def baseStart_2279717 : Nat := 118140960795 + 2279717 * 2 ^ 59
def prefixEnd_2279717 : Nat := 4983230072969 + 3 ^ 40 * 2279717 * 2
def baseEnd_2279717 : Nat := 260131239383547184545173

theorem tailTrace_2279717 : CollatzResearch.WordTrace tailWord_2279717 prefixEnd_2279717 260131239383547184545173 := by
  unfold tailWord_2279717
  simp only [CollatzResearch.WordTrace]
  refine ⟨83148109881982128511397405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55432073254654752340931603 83148109881982128511397405)
  ·
    refine ⟨31180541205743298191774027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83148109881982128511397405 31180541205743298191774027)
    ·
      refine ⟨46770811808614947287661041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31180541205743298191774027 46770811808614947287661041)
      ·
        refine ⟨35078108856461210465745781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46770811808614947287661041 35078108856461210465745781)
        ·
          refine ⟨3288572705293238481163667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35078108856461210465745781 3288572705293238481163667)
          ·
            refine ⟨4932859057939857721745501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288572705293238481163667 4932859057939857721745501)
            ·
              refine ⟨1849822146727446645654563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4932859057939857721745501 1849822146727446645654563)
              ·
                refine ⟨2774733220091169968481845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849822146727446645654563 2774733220091169968481845)
                ·
                  refine ⟨260131239383547184545173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774733220091169968481845 260131239383547184545173)
                  ·
                    rfl

theorem cell22_2279717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_2279717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279717 prefixEnd_2279717 := by exact prefixLift 2279717
  have htrace : WordTrace (prefixWord ++ tailWord_2279717) baseStart_2279717 baseEnd_2279717 := by
    simpa [prefixWord, tailWord_2279717, baseEnd_2279717] using wordTrace_append hprefix tailTrace_2279717
  have hstable : (prefixWord ++ tailWord_2279717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279717).length < 2 ^ (prefixWord ++ tailWord_2279717).sum := by decide
  have hdescent : baseEnd_2279717 < baseStart_2279717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279743 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_2279743 : Nat := 118140960795 + 2279743 * 2 ^ 59
def prefixEnd_2279743 : Nat := 4983230072969 + 3 ^ 40 * 2279743 * 2
def baseEnd_2279743 : Nat := 780402618481986152485439

theorem tailTrace_2279743 : CollatzResearch.WordTrace tailWord_2279743 prefixEnd_2279743 780402618481986152485439 := by
  unfold tailWord_2279743
  simp only [CollatzResearch.WordTrace]
  refine ⟨83149058179887934951843883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55432705453258623301229255 83149058179887934951843883)
  ·
    refine ⟨124723587269831902427765825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83149058179887934951843883 124723587269831902427765825)
    ·
      refine ⟨93542690452373926820824369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124723587269831902427765825 93542690452373926820824369)
      ·
        refine ⟨70157017839280445115618277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93542690452373926820824369 70157017839280445115618277)
        ·
          refine ⟨13154440844865083459178427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70157017839280445115618277 13154440844865083459178427)
          ·
            refine ⟨19731661267297625188767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154440844865083459178427 19731661267297625188767641)
            ·
              refine ⟨14798745950473218891575731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19731661267297625188767641 14798745950473218891575731)
              ·
                refine ⟨22198118925709828337363597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14798745950473218891575731 22198118925709828337363597)
                ·
                  refine ⟨8324294597141185626511349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22198118925709828337363597 8324294597141185626511349)
                  ·
                    refine ⟨780402618481986152485439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8324294597141185626511349 780402618481986152485439)
                    ·
                      rfl

theorem cell22_2279743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_2279743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279743 prefixEnd_2279743 := by exact prefixLift 2279743
  have htrace : WordTrace (prefixWord ++ tailWord_2279743) baseStart_2279743 baseEnd_2279743 := by
    simpa [prefixWord, tailWord_2279743, baseEnd_2279743] using wordTrace_append hprefix tailTrace_2279743
  have hstable : (prefixWord ++ tailWord_2279743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279743).length < 2 ^ (prefixWord ++ tailWord_2279743).sum := by decide
  have hdescent : baseEnd_2279743 < baseStart_2279743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279758 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2279758 : Nat := 118140960795 + 2279758 * 2 ^ 59
def prefixEnd_2279758 : Nat := 4983230072969 + 3 ^ 40 * 2279758 * 2
def baseEnd_2279758 : Nat := 780407753288531113360393

theorem tailTrace_2279758 : CollatzResearch.WordTrace tailWord_2279758 prefixEnd_2279758 780407753288531113360393 := by
  unfold tailWord_2279758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10393700659354199064204991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55433070183222395009093285 10393700659354199064204991)
  ·
    refine ⟨15590550989031298596307487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10393700659354199064204991 15590550989031298596307487)
    ·
      refine ⟨23385826483546947894461231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15590550989031298596307487 23385826483546947894461231)
      ·
        refine ⟨35078739725320421841691847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23385826483546947894461231 35078739725320421841691847)
        ·
          refine ⟨52618109587980632762537771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35078739725320421841691847 52618109587980632762537771)
          ·
            refine ⟨78927164381970949143806657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52618109587980632762537771 78927164381970949143806657)
            ·
              refine ⟨59195373286478211857854993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78927164381970949143806657 59195373286478211857854993)
              ·
                refine ⟨44396529964858658893391245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59195373286478211857854993 44396529964858658893391245)
                ·
                  refine ⟨16648698736821997085021717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44396529964858658893391245 16648698736821997085021717)
                  ·
                    refine ⟨780407753288531113360393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16648698736821997085021717 780407753288531113360393)
                    ·
                      rfl

theorem cell22_2279758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2279758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279758 prefixEnd_2279758 := by exact prefixLift 2279758
  have htrace : WordTrace (prefixWord ++ tailWord_2279758) baseStart_2279758 baseEnd_2279758 := by
    simpa [prefixWord, tailWord_2279758, baseEnd_2279758] using wordTrace_append hprefix tailTrace_2279758
  have hstable : (prefixWord ++ tailWord_2279758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279758).length < 2 ^ (prefixWord ++ tailWord_2279758).sum := by decide
  have hdescent : baseEnd_2279758 < baseStart_2279758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279760 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_2279760 : Nat := 118140960795 + 2279760 * 2 ^ 59
def prefixEnd_2279760 : Nat := 4983230072969 + 3 ^ 40 * 2279760 * 2
def baseEnd_2279760 : Nat := 780408437929403774810387

theorem tailTrace_2279760 : CollatzResearch.WordTrace tailWord_2279760 prefixEnd_2279760 780408437929403774810387 := by
  unfold tailWord_2279760
  simp only [CollatzResearch.WordTrace]
  refine ⟨41574839110413173427606367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55433118813884231236808489 41574839110413173427606367)
  ·
    refine ⟨62362258665619760141409551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41574839110413173427606367 62362258665619760141409551)
    ·
      refine ⟨93543387998429640212114327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62362258665619760141409551 93543387998429640212114327)
      ·
        refine ⟨140315081997644460318171491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93543387998429640212114327 140315081997644460318171491)
        ·
          refine ⟨210472622996466690477257237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140315081997644460318171491 210472622996466690477257237)
          ·
            refine ⟨9865904202959376116121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210472622996466690477257237 9865904202959376116121433)
            ·
              refine ⟨7399428152219532087091075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9865904202959376116121433 7399428152219532087091075)
              ·
                refine ⟨11099142228329298130636613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7399428152219532087091075 11099142228329298130636613)
                ·
                  refine ⟨2081089167811743399494365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11099142228329298130636613 2081089167811743399494365)
                  ·
                    refine ⟨780408437929403774810387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081089167811743399494365 780408437929403774810387)
                    ·
                      rfl

theorem cell22_2279760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_2279760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279760 prefixEnd_2279760 := by exact prefixLift 2279760
  have htrace : WordTrace (prefixWord ++ tailWord_2279760) baseStart_2279760 baseEnd_2279760 := by
    simpa [prefixWord, tailWord_2279760, baseEnd_2279760] using wordTrace_append hprefix tailTrace_2279760
  have hstable : (prefixWord ++ tailWord_2279760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279760).length < 2 ^ (prefixWord ++ tailWord_2279760).sum := by decide
  have hdescent : baseEnd_2279760 < baseStart_2279760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279873 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2279873 : Nat := 118140960795 + 2279873 * 2 ^ 59
def prefixEnd_2279873 : Nat := 4983230072969 + 3 ^ 40 * 2279873 * 2
def baseEnd_2279873 : Nat := 780447120138709146735041

theorem tailTrace_2279873 : CollatzResearch.WordTrace tailWord_2279873 prefixEnd_2279873 780447120138709146735041 := by
  unfold tailWord_2279873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83153799669416967154076273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55435866446277978102717515 83153799669416967154076273)
  ·
    refine ⟨62365349752062725365557205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83153799669416967154076273 62365349752062725365557205)
    ·
      refine ⟨1461687884813970125755247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62365349752062725365557205 1461687884813970125755247)
      ·
        refine ⟨2192531827220955188632871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461687884813970125755247 2192531827220955188632871)
        ·
          refine ⟨3288797740831432782949307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192531827220955188632871 3288797740831432782949307)
          ·
            refine ⟨4933196611247149174423961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288797740831432782949307 4933196611247149174423961)
            ·
              refine ⟨3699897458435361880817971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933196611247149174423961 3699897458435361880817971)
              ·
                refine ⟨5549846187653042821226957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699897458435361880817971 5549846187653042821226957)
                ·
                  refine ⟨2081192320369891057960109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5549846187653042821226957 2081192320369891057960109)
                  ·
                    refine ⟨780447120138709146735041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081192320369891057960109 780447120138709146735041)
                    ·
                      rfl

theorem cell22_2279873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2279873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279873 prefixEnd_2279873 := by exact prefixLift 2279873
  have htrace : WordTrace (prefixWord ++ tailWord_2279873) baseStart_2279873 baseEnd_2279873 := by
    simpa [prefixWord, tailWord_2279873, baseEnd_2279873] using wordTrace_append hprefix tailTrace_2279873
  have hstable : (prefixWord ++ tailWord_2279873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279873).length < 2 ^ (prefixWord ++ tailWord_2279873).sum := by decide
  have hdescent : baseEnd_2279873 < baseStart_2279873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279880 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_2279880 : Nat := 118140960795 + 2279880 * 2 ^ 59
def prefixEnd_2279880 : Nat := 4983230072969 + 3 ^ 40 * 2279880 * 2
def baseEnd_2279880 : Nat := 260149838793921153936673

theorem tailTrace_2279880 : CollatzResearch.WordTrace tailWord_2279880 prefixEnd_2279880 260149838793921153936673 := by
  unfold tailWord_2279880
  simp only [CollatzResearch.WordTrace]
  refine ⟨41577027490195803674790547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55436036653594404899720729 41577027490195803674790547)
  ·
    refine ⟨62365541235293705512185821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41577027490195803674790547 62365541235293705512185821)
    ·
      refine ⟨23387077963235139567069683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62365541235293705512185821 23387077963235139567069683)
      ·
        refine ⟨35080616944852709350604525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23387077963235139567069683 35080616944852709350604525)
        ·
          refine ⟨13155231354319766006476697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35080616944852709350604525 13155231354319766006476697)
          ·
            refine ⟨9866423515739824504857523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13155231354319766006476697 9866423515739824504857523)
            ·
              refine ⟨14799635273609736757286285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866423515739824504857523 14799635273609736757286285)
              ·
                refine ⟨5549863227603651283982357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14799635273609736757286285 5549863227603651283982357)
                ·
                  refine ⟨260149838793921153936673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5549863227603651283982357 260149838793921153936673)
                  ·
                    rfl

theorem cell22_2279880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_2279880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279880 prefixEnd_2279880 := by exact prefixLift 2279880
  have htrace : WordTrace (prefixWord ++ tailWord_2279880) baseStart_2279880 baseEnd_2279880 := by
    simpa [prefixWord, tailWord_2279880, baseEnd_2279880] using wordTrace_append hprefix tailTrace_2279880
  have hstable : (prefixWord ++ tailWord_2279880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279880).length < 2 ^ (prefixWord ++ tailWord_2279880).sum := by decide
  have hdescent : baseEnd_2279880 < baseStart_2279880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279912 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2279912 : Nat := 118140960795 + 2279912 * 2 ^ 59
def prefixEnd_2279912 : Nat := 4983230072969 + 3 ^ 40 * 2279912 * 2
def baseEnd_2279912 : Nat := 780460470635726045009921

theorem tailTrace_2279912 : CollatzResearch.WordTrace tailWord_2279912 prefixEnd_2279912 780460470635726045009921 := by
  unfold tailWord_2279912
  simp only [CollatzResearch.WordTrace]
  refine ⟨41577611058137838407372995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55436814744183784543163993 41577611058137838407372995)
  ·
    refine ⟨62366416587206757611059493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41577611058137838407372995 62366416587206757611059493)
    ·
      refine ⟨11693703110101267052073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62366416587206757611059493 11693703110101267052073655)
      ·
        refine ⟨17540554665151900578110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693703110101267052073655 17540554665151900578110483)
        ·
          refine ⟨26310831997727850867165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17540554665151900578110483 26310831997727850867165725)
          ·
            refine ⟨9866561999147944075187147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26310831997727850867165725 9866561999147944075187147)
            ·
              refine ⟨14799842998721916112780721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866561999147944075187147 14799842998721916112780721)
              ·
                refine ⟨11099882249041437084585541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14799842998721916112780721 11099882249041437084585541)
                ·
                  refine ⟨2081227921695269453359789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11099882249041437084585541 2081227921695269453359789)
                  ·
                    refine ⟨780460470635726045009921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081227921695269453359789 780460470635726045009921)
                    ·
                      rfl

theorem cell22_2279912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2279912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279912 prefixEnd_2279912 := by exact prefixLift 2279912
  have htrace : WordTrace (prefixWord ++ tailWord_2279912) baseStart_2279912 baseEnd_2279912 := by
    simpa [prefixWord, tailWord_2279912, baseEnd_2279912] using wordTrace_append hprefix tailTrace_2279912
  have hstable : (prefixWord ++ tailWord_2279912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279912).length < 2 ^ (prefixWord ++ tailWord_2279912).sum := by decide
  have hdescent : baseEnd_2279912 < baseStart_2279912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279914 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_2279914 : Nat := 118140960795 + 2279914 * 2 ^ 59
def prefixEnd_2279914 : Nat := 4983230072969 + 3 ^ 40 * 2279914 * 2
def baseEnd_2279914 : Nat := 260153718425532902153305

theorem tailTrace_2279914 : CollatzResearch.WordTrace tailWord_2279914 prefixEnd_2279914 260153718425532902153305 := by
  unfold tailWord_2279914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788823765567107789079699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55436863374845620770879197 20788823765567107789079699)
  ·
    refine ⟨31183235648350661683619549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20788823765567107789079699 31183235648350661683619549)
    ·
      refine ⟨11693713368131498131357331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31183235648350661683619549 11693713368131498131357331)
      ·
        refine ⟨17540570052197247197035997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693713368131498131357331 17540570052197247197035997)
        ·
          refine ⟨6577713769573967698888499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17540570052197247197035997 6577713769573967698888499)
          ·
            refine ⟨9866570654360951548332749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577713769573967698888499 9866570654360951548332749)
            ·
              refine ⟨3699963995385356830624781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9866570654360951548332749 3699963995385356830624781)
              ·
                refine ⟨1387486498269508811484293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3699963995385356830624781 1387486498269508811484293)
                ·
                  refine ⟨260153718425532902153305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387486498269508811484293 260153718425532902153305)
                  ·
                    rfl

theorem cell22_2279914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_2279914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279914 prefixEnd_2279914 := by exact prefixLift 2279914
  have htrace : WordTrace (prefixWord ++ tailWord_2279914) baseStart_2279914 baseEnd_2279914 := by
    simpa [prefixWord, tailWord_2279914, baseEnd_2279914] using wordTrace_append hprefix tailTrace_2279914
  have hstable : (prefixWord ++ tailWord_2279914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279914).length < 2 ^ (prefixWord ++ tailWord_2279914).sum := by decide
  have hdescent : baseEnd_2279914 < baseStart_2279914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279957 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_2279957 : Nat := 118140960795 + 2279957 * 2 ^ 59
def prefixEnd_2279957 : Nat := 4983230072969 + 3 ^ 40 * 2279957 * 2
def baseEnd_2279957 : Nat := 780475875055360927634783

theorem tailTrace_2279957 : CollatzResearch.WordTrace tailWord_2279957 prefixEnd_2279957 780475875055360927634783 := by
  unfold tailWord_2279957
  simp only [CollatzResearch.WordTrace]
  refine ⟨83156863401112649500134125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55437908934075099666756083 83156863401112649500134125)
  ·
    refine ⟨31183823775417243562550297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83156863401112649500134125 31183823775417243562550297)
    ·
      refine ⟨23387867831562932671912723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31183823775417243562550297 23387867831562932671912723)
      ·
        refine ⟨35081801747344399007869085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23387867831562932671912723 35081801747344399007869085)
        ·
          refine ⟨13155675655254149627950907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35081801747344399007869085 13155675655254149627950907)
          ·
            refine ⟨19733513482881224441926361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155675655254149627950907 19733513482881224441926361)
            ·
              refine ⟨14800135112160918331444771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19733513482881224441926361 14800135112160918331444771)
              ·
                refine ⟨22200202668241377497167157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800135112160918331444771 22200202668241377497167157)
                ·
                  refine ⟨2081269000147629140359421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22200202668241377497167157 2081269000147629140359421)
                  ·
                    refine ⟨780475875055360927634783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081269000147629140359421 780475875055360927634783)
                    ·
                      rfl

theorem cell22_2279957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_2279957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279957 prefixEnd_2279957 := by exact prefixLift 2279957
  have htrace : WordTrace (prefixWord ++ tailWord_2279957) baseStart_2279957 baseEnd_2279957 := by
    simpa [prefixWord, tailWord_2279957, baseEnd_2279957] using wordTrace_append hprefix tailTrace_2279957
  have hstable : (prefixWord ++ tailWord_2279957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279957).length < 2 ^ (prefixWord ++ tailWord_2279957).sum := by decide
  have hdescent : baseEnd_2279957 < baseStart_2279957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279987 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 5]
def baseStart_2279987 : Nat := 118140960795 + 2279987 * 2 ^ 59
def prefixEnd_2279987 : Nat := 4983230072969 + 3 ^ 40 * 2279987 * 2
def baseEnd_2279987 : Nat := 260162048222816949794897

theorem tailTrace_2279987 : CollatzResearch.WordTrace tailWord_2279987 prefixEnd_2279987 260162048222816949794897 := by
  unfold tailWord_2279987
  simp only [CollatzResearch.WordTrace]
  refine ⟨83157957591003964623726215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55438638394002643082484143 83157957591003964623726215)
  ·
    refine ⟨124736936386505946935589323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83157957591003964623726215 124736936386505946935589323)
    ·
      refine ⟨187105404579758920403383985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124736936386505946935589323 187105404579758920403383985)
      ·
        refine ⟨140329053434819190302537989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187105404579758920403383985 140329053434819190302537989)
        ·
          refine ⟨26311697519028598181725873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140329053434819190302537989 26311697519028598181725873)
          ·
            refine ⟨19733773139271448636294405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26311697519028598181725873 19733773139271448636294405)
            ·
              refine ⟨3700082463613396619305201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19733773139271448636294405 3700082463613396619305201)
              ·
                refine ⟨2775061847710047464478901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700082463613396619305201 2775061847710047464478901)
                ·
                  refine ⟨260162048222816949794897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775061847710047464478901 260162048222816949794897)
                  ·
                    rfl

theorem cell22_2279987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].length) (baseStart_2279987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2279987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2279987 prefixEnd_2279987 := by exact prefixLift 2279987
  have htrace : WordTrace (prefixWord ++ tailWord_2279987) baseStart_2279987 baseEnd_2279987 := by
    simpa [prefixWord, tailWord_2279987, baseEnd_2279987] using wordTrace_append hprefix tailTrace_2279987
  have hstable : (prefixWord ++ tailWord_2279987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279987).length < 2 ^ (prefixWord ++ tailWord_2279987).sum := by decide
  have hdescent : baseEnd_2279987 < baseStart_2279987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280015 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 8]
def baseStart_2280015 : Nat := 118140960795 + 2280015 * 2 ^ 59
def prefixEnd_2280015 : Nat := 4983230072969 + 3 ^ 40 * 2280015 * 2
def baseEnd_2280015 : Nat := 260165243213556036561535

theorem tailTrace_2280015 : CollatzResearch.WordTrace tailWord_2280015 prefixEnd_2280015 260165243213556036561535 := by
  unfold tailWord_2280015
  simp only [CollatzResearch.WordTrace]
  refine ⟨83158978834902525405745499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55439319223268350270496999 83158978834902525405745499)
  ·
    refine ⟨124738468252353788108618249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83158978834902525405745499 124738468252353788108618249)
    ·
      refine ⟨93553851189265341081463687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124738468252353788108618249 93553851189265341081463687)
      ·
        refine ⟨140330776783898011622195531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93553851189265341081463687 140330776783898011622195531)
        ·
          refine ⟨210496165175847017433293297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140330776783898011622195531 210496165175847017433293297)
          ·
            refine ⟨157872123881885263074969973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210496165175847017433293297 157872123881885263074969973)
            ·
              refine ⟨14800511613926743413278435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157872123881885263074969973 14800511613926743413278435)
              ·
                refine ⟨22200767420890115119917653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800511613926743413278435 22200767420890115119917653)
                ·
                  refine ⟨260165243213556036561535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22200767420890115119917653 260165243213556036561535)
                  ·
                    rfl

theorem cell22_2280015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_2280015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280015 prefixEnd_2280015 := by exact prefixLift 2280015
  have htrace : WordTrace (prefixWord ++ tailWord_2280015) baseStart_2280015 baseEnd_2280015 := by
    simpa [prefixWord, tailWord_2280015, baseEnd_2280015] using wordTrace_append hprefix tailTrace_2280015
  have hstable : (prefixWord ++ tailWord_2280015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280015).length < 2 ^ (prefixWord ++ tailWord_2280015).sum := by decide
  have hdescent : baseEnd_2280015 < baseStart_2280015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280017 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2280017 : Nat := 118140960795 + 2280017 * 2 ^ 59
def prefixEnd_2280017 : Nat := 4983230072969 + 3 ^ 40 * 2280017 * 2
def baseEnd_2280017 : Nat := 780496414281540771134599

theorem tailTrace_2280017 : CollatzResearch.WordTrace tailWord_2280017 prefixEnd_2280017 780496414281540771134599 := by
  unfold tailWord_2280017
  simp only [CollatzResearch.WordTrace]
  refine ⟨83159051780895279747318305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55439367853930186498212203 83159051780895279747318305)
  ·
    refine ⟨62369288835671459810488729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83159051780895279747318305 62369288835671459810488729)
    ·
      refine ⟨46776966626753594857866547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62369288835671459810488729 46776966626753594857866547)
      ·
        refine ⟨70165449940130392286799821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46776966626753594857866547 70165449940130392286799821)
        ·
          refine ⟨26312043727548897107549933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70165449940130392286799821 26312043727548897107549933)
          ·
            refine ⟨9867016397830836415331225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26312043727548897107549933 9867016397830836415331225)
            ·
              refine ⟨7400262298373127311498419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9867016397830836415331225 7400262298373127311498419)
              ·
                refine ⟨11100393447559690967247629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7400262298373127311498419 11100393447559690967247629)
                ·
                  refine ⟨4162647542834884112717861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11100393447559690967247629 4162647542834884112717861)
                  ·
                    refine ⟨780496414281540771134599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4162647542834884112717861 780496414281540771134599)
                    ·
                      rfl

theorem cell22_2280017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2280017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280017 prefixEnd_2280017 := by exact prefixLift 2280017
  have htrace : WordTrace (prefixWord ++ tailWord_2280017) baseStart_2280017 baseEnd_2280017 := by
    simpa [prefixWord, tailWord_2280017, baseEnd_2280017] using wordTrace_append hprefix tailTrace_2280017
  have hstable : (prefixWord ++ tailWord_2280017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280017).length < 2 ^ (prefixWord ++ tailWord_2280017).sum := by decide
  have hdescent : baseEnd_2280017 < baseStart_2280017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280064 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_2280064 : Nat := 118140960795 + 2280064 * 2 ^ 59
def prefixEnd_2280064 : Nat := 4983230072969 + 3 ^ 40 * 2280064 * 2
def baseEnd_2280064 : Nat := 780512503342048315209455

theorem tailTrace_2280064 : CollatzResearch.WordTrace tailWord_2280064 prefixEnd_2280064 780512503342048315209455 := by
  unfold tailWord_2280064
  simp only [CollatzResearch.WordTrace]
  refine ⟨41580383005862503387139623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55440510674483337849519497 41580383005862503387139623)
  ·
    refine ⟨62370574508793755080709435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41580383005862503387139623 62370574508793755080709435)
    ·
      refine ⟨93555861763190632621064153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62370574508793755080709435 93555861763190632621064153)
      ·
        refine ⟨70166896322392974465798115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93555861763190632621064153 70166896322392974465798115)
        ·
          refine ⟨105250344483589461698697173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70166896322392974465798115 105250344483589461698697173)
          ·
            refine ⟨2466804948834128008563215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 105250344483589461698697173 2466804948834128008563215)
            ·
              refine ⟨3700207423251192012844823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466804948834128008563215 3700207423251192012844823)
              ·
                refine ⟨5550311134876788019267235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700207423251192012844823 5550311134876788019267235)
                ·
                  refine ⟨8325466702315182028900853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550311134876788019267235 8325466702315182028900853)
                  ·
                    refine ⟨780512503342048315209455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8325466702315182028900853 780512503342048315209455)
                    ·
                      rfl

theorem cell22_2280064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_2280064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280064 prefixEnd_2280064 := by exact prefixLift 2280064
  have htrace : WordTrace (prefixWord ++ tailWord_2280064) baseStart_2280064 baseEnd_2280064 := by
    simpa [prefixWord, tailWord_2280064, baseEnd_2280064] using wordTrace_append hprefix tailTrace_2280064
  have hstable : (prefixWord ++ tailWord_2280064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280064).length < 2 ^ (prefixWord ++ tailWord_2280064).sum := by decide
  have hdescent : baseEnd_2280064 < baseStart_2280064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280156 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_2280156 : Nat := 118140960795 + 2280156 * 2 ^ 59
def prefixEnd_2280156 : Nat := 4983230072969 + 3 ^ 40 * 2280156 * 2
def baseEnd_2280156 : Nat := 260181332274063580636391

theorem tailTrace_2280156 : CollatzResearch.WordTrace tailWord_2280156 prefixEnd_2280156 260181332274063580636391 := by
  unfold tailWord_2280156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41582060763695853243314161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55442747684927804324418881 41582060763695853243314161)
  ·
    refine ⟨31186545572771889932485621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41582060763695853243314161 31186545572771889932485621)
    ·
      refine ⟨2923738647447364681170527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31186545572771889932485621 2923738647447364681170527)
      ·
        refine ⟨4385607971171047021755791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2923738647447364681170527 4385607971171047021755791)
        ·
          refine ⟨6578411956756570532633687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385607971171047021755791 6578411956756570532633687)
          ·
            refine ⟨9867617935134855798950531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578411956756570532633687 9867617935134855798950531)
            ·
              refine ⟨14801426902702283698425797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9867617935134855798950531 14801426902702283698425797)
              ·
                refine ⟨2775267544256678193454837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14801426902702283698425797 2775267544256678193454837)
                ·
                  refine ⟨260181332274063580636391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775267544256678193454837 260181332274063580636391)
                  ·
                    rfl

theorem cell22_2280156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_2280156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280156 prefixEnd_2280156 := by exact prefixLift 2280156
  have htrace : WordTrace (prefixWord ++ tailWord_2280156) baseStart_2280156 baseEnd_2280156 := by
    simpa [prefixWord, tailWord_2280156, baseEnd_2280156] using wordTrace_append hprefix tailTrace_2280156
  have hstable : (prefixWord ++ tailWord_2280156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280156).length < 2 ^ (prefixWord ++ tailWord_2280156).sum := by decide
  have hdescent : baseEnd_2280156 < baseStart_2280156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280274 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_2280274 : Nat := 118140960795 + 2280274 * 2 ^ 59
def prefixEnd_2280274 : Nat := 4983230072969 + 3 ^ 40 * 2280274 * 2
def baseEnd_2280274 : Nat := 260194796877892589152937

theorem tailTrace_2280274 : CollatzResearch.WordTrace tailWord_2280274 prefixEnd_2280274 260194796877892589152937 := by
  unfold tailWord_2280274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792106335241053159855969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55445616893976141759615917 20792106335241053159855969)
  ·
    refine ⟨15594079751430789869891977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20792106335241053159855969 15594079751430789869891977)
    ·
      refine ⟨11695559813573092402418983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15594079751430789869891977 11695559813573092402418983)
      ·
        refine ⟨17543339720359638603628475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11695559813573092402418983 17543339720359638603628475)
        ·
          refine ⟨26315009580539457905442713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17543339720359638603628475 26315009580539457905442713)
          ·
            refine ⟨19736257185404593429082035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26315009580539457905442713 19736257185404593429082035)
            ·
              refine ⟨29604385778106890143623053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19736257185404593429082035 29604385778106890143623053)
              ·
                refine ⟨11101644666790083803858645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29604385778106890143623053 11101644666790083803858645)
                ·
                  refine ⟨260194796877892589152937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11101644666790083803858645 260194796877892589152937)
                  ·
                    rfl

theorem cell22_2280274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2280274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280274 prefixEnd_2280274 := by exact prefixLift 2280274
  have htrace : WordTrace (prefixWord ++ tailWord_2280274) baseStart_2280274 baseEnd_2280274 := by
    simpa [prefixWord, tailWord_2280274, baseEnd_2280274] using wordTrace_append hprefix tailTrace_2280274
  have hstable : (prefixWord ++ tailWord_2280274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280274).length < 2 ^ (prefixWord ++ tailWord_2280274).sum := by decide
  have hdescent : baseEnd_2280274 < baseStart_2280274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280291 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 5]
def baseStart_2280291 : Nat := 118140960795 + 2280291 * 2 ^ 59
def prefixEnd_2280291 : Nat := 4983230072969 + 3 ^ 40 * 2280291 * 2
def baseEnd_2280291 : Nat := 260196736693698463261253

theorem tailTrace_2280291 : CollatzResearch.WordTrace tailWord_2280291 prefixEnd_2280291 260196736693698463261253 := by
  unfold tailWord_2280291
  simp only [CollatzResearch.WordTrace]
  refine ⟨83169045381902624542792727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55446030254601749695195151 83169045381902624542792727)
  ·
    refine ⟨124753568072853936814189091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83169045381902624542792727 124753568072853936814189091)
    ·
      refine ⟨187130352109280905221283637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124753568072853936814189091 187130352109280905221283637)
      ·
        refine ⟨17543470510245084864495341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187130352109280905221283637 17543470510245084864495341)
        ·
          refine ⟨6578801441341906824185753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17543470510245084864495341 6578801441341906824185753)
          ·
            refine ⟨4934101081006430118139315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6578801441341906824185753 4934101081006430118139315)
            ·
              refine ⟨7401151621509645177208973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934101081006430118139315 7401151621509645177208973)
              ·
                refine ⟨2775431858066116941453365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7401151621509645177208973 2775431858066116941453365)
                ·
                  refine ⟨260196736693698463261253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775431858066116941453365 260196736693698463261253)
                  ·
                    rfl

theorem cell22_2280291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].length) (baseStart_2280291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280291 prefixEnd_2280291 := by exact prefixLift 2280291
  have htrace : WordTrace (prefixWord ++ tailWord_2280291) baseStart_2280291 baseEnd_2280291 := by
    simpa [prefixWord, tailWord_2280291, baseEnd_2280291] using wordTrace_append hprefix tailTrace_2280291
  have hstable : (prefixWord ++ tailWord_2280291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280291).length < 2 ^ (prefixWord ++ tailWord_2280291).sum := by decide
  have hdescent : baseEnd_2280291 < baseStart_2280291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280351 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_2280351 : Nat := 118140960795 + 2280351 * 2 ^ 59
def prefixEnd_2280351 : Nat := 4983230072969 + 3 ^ 40 * 2280351 * 2
def baseEnd_2280351 : Nat := 780610749307275233283575

theorem tailTrace_2280351 : CollatzResearch.WordTrace tailWord_2280351 prefixEnd_2280351 780610749307275233283575 := by
  unfold tailWord_2280351
  simp only [CollatzResearch.WordTrace]
  refine ⟨83171233761685254789976907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55447489174456836526651271 83171233761685254789976907)
  ·
    refine ⟨124756850642527882184965361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83171233761685254789976907 124756850642527882184965361)
    ·
      refine ⟨93567637981895911638724021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124756850642527882184965361 93567637981895911638724021)
      ·
        refine ⟨8771966060802741716130377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93567637981895911638724021 8771966060802741716130377)
        ·
          refine ⟨6578974545602056287097783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8771966060802741716130377 6578974545602056287097783)
          ·
            refine ⟨9868461818403084430646675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578974545602056287097783 9868461818403084430646675)
            ·
              refine ⟨14802692727604626645970013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868461818403084430646675 14802692727604626645970013)
              ·
                refine ⟨5551009772851734992238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14802692727604626645970013 5551009772851734992238755)
                ·
                  refine ⟨8326514659277602488358133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5551009772851734992238755 8326514659277602488358133)
                  ·
                    refine ⟨780610749307275233283575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8326514659277602488358133 780610749307275233283575)
                    ·
                      rfl

theorem cell22_2280351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_2280351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280351 prefixEnd_2280351 := by exact prefixLift 2280351
  have htrace : WordTrace (prefixWord ++ tailWord_2280351) baseStart_2280351 baseEnd_2280351 := by
    simpa [prefixWord, tailWord_2280351, baseEnd_2280351] using wordTrace_append hprefix tailTrace_2280351
  have hstable : (prefixWord ++ tailWord_2280351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280351).length < 2 ^ (prefixWord ++ tailWord_2280351).sum := by decide
  have hdescent : baseEnd_2280351 < baseStart_2280351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280372 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2280372 : Nat := 118140960795 + 2280372 * 2 ^ 59
def prefixEnd_2280372 : Nat := 4983230072969 + 3 ^ 40 * 2280372 * 2
def baseEnd_2280372 : Nat := 780617938036438178508511

theorem tailTrace_2280372 : CollatzResearch.WordTrace tailWord_2280372 prefixEnd_2280372 780617938036438178508511 := by
  unfold tailWord_2280372
  simp only [CollatzResearch.WordTrace]
  refine ⟨41585999847304587688245685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55447999796406116917660913 41585999847304587688245685)
  ·
    refine ⟨3898687485684805095773033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41585999847304587688245685 3898687485684805095773033)
    ·
      refine ⟨2924015614263603821829775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3898687485684805095773033 2924015614263603821829775)
      ·
        refine ⟨4386023421395405732744663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924015614263603821829775 4386023421395405732744663)
        ·
          refine ⟨6579035132093108599116995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386023421395405732744663 6579035132093108599116995)
          ·
            refine ⟨9868552698139662898675493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579035132093108599116995 9868552698139662898675493)
            ·
              refine ⟨1850353630901186793501655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9868552698139662898675493 1850353630901186793501655)
              ·
                refine ⟨2775530446351780190252483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850353630901186793501655 2775530446351780190252483)
                ·
                  refine ⟨4163295669527670285378725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775530446351780190252483 4163295669527670285378725)
                  ·
                    refine ⟨780617938036438178508511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4163295669527670285378725 780617938036438178508511)
                    ·
                      rfl

theorem cell22_2280372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2280372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280372 prefixEnd_2280372 := by exact prefixLift 2280372
  have htrace : WordTrace (prefixWord ++ tailWord_2280372) baseStart_2280372 baseEnd_2280372 := by
    simpa [prefixWord, tailWord_2280372, baseEnd_2280372] using wordTrace_append hprefix tailTrace_2280372
  have hstable : (prefixWord ++ tailWord_2280372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280372).length < 2 ^ (prefixWord ++ tailWord_2280372).sum := by decide
  have hdescent : baseEnd_2280372 < baseStart_2280372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280381 : List Nat := [1, 4, 1, 2, 4, 1, 9]
def baseStart_2280381 : Nat := 118140960795 + 2280381 * 2 ^ 59
def prefixEnd_2280381 : Nat := 4983230072969 + 3 ^ 40 * 2280381 * 2
def baseEnd_2280381 : Nat := 28911889589643153890129

theorem tailTrace_2280381 : CollatzResearch.WordTrace tailWord_2280381 prefixEnd_2280381 28911889589643153890129 := by
  unfold tailWord_2280381
  simp only [CollatzResearch.WordTrace]
  refine ⟨83172327951576569913568997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55448218634384379942379331 83172327951576569913568997)
  ·
    refine ⟨15594811490920606858794187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83172327951576569913568997 15594811490920606858794187)
    ·
      refine ⟨23392217236380910288191281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15594811490920606858794187 23392217236380910288191281)
      ·
        refine ⟨17544162927285682716143461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23392217236380910288191281 17544162927285682716143461)
        ·
          refine ⟨3289530548866065509276899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17544162927285682716143461 3289530548866065509276899)
          ·
            refine ⟨4934295823299098263915349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289530548866065509276899 4934295823299098263915349)
            ·
              refine ⟨28911889589643153890129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4934295823299098263915349 28911889589643153890129)
              ·
                rfl

theorem cell22_2280381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 9].length) (baseStart_2280381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280381 prefixEnd_2280381 := by exact prefixLift 2280381
  have htrace : WordTrace (prefixWord ++ tailWord_2280381) baseStart_2280381 baseEnd_2280381 := by
    simpa [prefixWord, tailWord_2280381, baseEnd_2280381] using wordTrace_append hprefix tailTrace_2280381
  have hstable : (prefixWord ++ tailWord_2280381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280381).length < 2 ^ (prefixWord ++ tailWord_2280381).sum := by decide
  have hdescent : baseEnd_2280381 < baseStart_2280381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280402 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2280402 : Nat := 118140960795 + 2280402 * 2 ^ 59
def prefixEnd_2280402 : Nat := 4983230072969 + 3 ^ 40 * 2280402 * 2
def baseEnd_2280402 : Nat := 780628207649528100258419

theorem tailTrace_2280402 : CollatzResearch.WordTrace tailWord_2280402 prefixEnd_2280402 780628207649528100258419 := by
  unfold tailWord_2280402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20793273471125122625020865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55448729256333660333388973 20793273471125122625020865)
  ·
    refine ⟨15594955103343841968765649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20793273471125122625020865 15594955103343841968765649)
    ·
      refine ⟨11696216327507881476574237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15594955103343841968765649 11696216327507881476574237)
      ·
        refine ⟨4386081122815455553715339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11696216327507881476574237 4386081122815455553715339)
        ·
          refine ⟨6579121684223183330573009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386081122815455553715339 6579121684223183330573009)
          ·
            refine ⟨4934341263167387497929757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6579121684223183330573009 4934341263167387497929757)
            ·
              refine ⟨1850377973687770311723659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4934341263167387497929757 1850377973687770311723659)
              ·
                refine ⟨2775566960531655467585489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850377973687770311723659 2775566960531655467585489)
                ·
                  refine ⟨2081675220398741600689117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2775566960531655467585489 2081675220398741600689117)
                  ·
                    refine ⟨780628207649528100258419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081675220398741600689117 780628207649528100258419)
                    ·
                      rfl

theorem cell22_2280402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2280402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280402 prefixEnd_2280402 := by exact prefixLift 2280402
  have htrace : WordTrace (prefixWord ++ tailWord_2280402) baseStart_2280402 baseEnd_2280402 := by
    simpa [prefixWord, tailWord_2280402, baseEnd_2280402] using wordTrace_append hprefix tailTrace_2280402
  have hstable : (prefixWord ++ tailWord_2280402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280402).length < 2 ^ (prefixWord ++ tailWord_2280402).sum := by decide
  have hdescent : baseEnd_2280402 < baseStart_2280402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280415 : List Nat := [1, 1, 2, 3, 6, 1, 2, 6]
def baseStart_2280415 : Nat := 118140960795 + 2280415 * 2 ^ 59
def prefixEnd_2280415 : Nat := 4983230072969 + 3 ^ 40 * 2280415 * 2
def baseEnd_2280415 : Nat := 86736961979466711075931

theorem tailTrace_2280415 : CollatzResearch.WordTrace tailWord_2280415 prefixEnd_2280415 86736961979466711075931 := by
  unfold tailWord_2280415
  simp only [CollatzResearch.WordTrace]
  refine ⟨83173568033453393720306699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55449045355635595813537799 83173568033453393720306699)
  ·
    refine ⟨124760352050180090580460049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83173568033453393720306699 124760352050180090580460049)
    ·
      refine ⟨93570264037635067935345037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124760352050180090580460049 93570264037635067935345037)
      ·
        refine ⟨35088849014113150475754389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93570264037635067935345037 35088849014113150475754389)
        ·
          refine ⟨1644789797536553928550987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35088849014113150475754389 1644789797536553928550987)
          ·
            refine ⟨2467184696304830892826481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644789797536553928550987 2467184696304830892826481)
            ·
              refine ⟨1850388522228623169619861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467184696304830892826481 1850388522228623169619861)
              ·
                refine ⟨86736961979466711075931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1850388522228623169619861 86736961979466711075931)
                ·
                  rfl

theorem cell22_2280415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 6].length) (baseStart_2280415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280415 prefixEnd_2280415 := by exact prefixLift 2280415
  have htrace : WordTrace (prefixWord ++ tailWord_2280415) baseStart_2280415 baseEnd_2280415 := by
    simpa [prefixWord, tailWord_2280415, baseEnd_2280415] using wordTrace_append hprefix tailTrace_2280415
  have hstable : (prefixWord ++ tailWord_2280415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280415).length < 2 ^ (prefixWord ++ tailWord_2280415).sum := by decide
  have hdescent : baseEnd_2280415 < baseStart_2280415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280426 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_2280426 : Nat := 118140960795 + 2280426 * 2 ^ 59
def prefixEnd_2280426 : Nat := 4983230072969 + 3 ^ 40 * 2280426 * 2
def baseEnd_2280426 : Nat := 260212141113333345886115

theorem tailTrace_2280426 : CollatzResearch.WordTrace tailWord_2280426 prefixEnd_2280426 260212141113333345886115 := by
  unfold tailWord_2280426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20793492309103385649739283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55449312824275695065971421 20793492309103385649739283)
  ·
    refine ⟨31190238463655078474608925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20793492309103385649739283 31190238463655078474608925)
    ·
      refine ⟨11696339423870654427978347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31190238463655078474608925 11696339423870654427978347)
      ·
        refine ⟨17544509135805981641967521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11696339423870654427978347 17544509135805981641967521)
        ·
          refine ⟨13158381851854486231475641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17544509135805981641967521 13158381851854486231475641)
          ·
            refine ⟨9868786388890864673606731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13158381851854486231475641 9868786388890864673606731)
            ·
              refine ⟨14803179583336297010410097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868786388890864673606731 14803179583336297010410097)
              ·
                refine ⟨11102384687502222757807573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14803179583336297010410097 11102384687502222757807573)
                ·
                  refine ⟨260212141113333345886115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11102384687502222757807573 260212141113333345886115)
                  ·
                    rfl

theorem cell22_2280426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_2280426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280426 prefixEnd_2280426 := by exact prefixLift 2280426
  have htrace : WordTrace (prefixWord ++ tailWord_2280426) baseStart_2280426 baseEnd_2280426 := by
    simpa [prefixWord, tailWord_2280426, baseEnd_2280426] using wordTrace_append hprefix tailTrace_2280426
  have hstable : (prefixWord ++ tailWord_2280426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280426).length < 2 ^ (prefixWord ++ tailWord_2280426).sum := by decide
  have hdescent : baseEnd_2280426 < baseStart_2280426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280460 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_2280460 : Nat := 118140960795 + 2280460 * 2 ^ 59
def prefixEnd_2280460 : Nat := 4983230072969 + 3 ^ 40 * 2280460 * 2
def baseEnd_2280460 : Nat := 260216020744945094102747

theorem tailTrace_2280460 : CollatzResearch.WordTrace tailWord_2280460 prefixEnd_2280460 260216020744945094102747 := by
  unfold tailWord_2280460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41587604659145183202847417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55450139545526910937129889 41587604659145183202847417)
  ·
    refine ⟨31190703494358887402135563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41587604659145183202847417 31190703494358887402135563)
    ·
      refine ⟨46786055241538331103203345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31190703494358887402135563 46786055241538331103203345)
      ·
        refine ⟨35089541431153748327402509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46786055241538331103203345 35089541431153748327402509)
        ·
          refine ⟨13158578036682655622775941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35089541431153748327402509 13158578036682655622775941)
          ·
            refine ⟨2467233381877997929270489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13158578036682655622775941 2467233381877997929270489)
            ·
              refine ⟨1850425036408498446952867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467233381877997929270489 1850425036408498446952867)
              ·
                refine ⟨2775637554612747670429301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850425036408498446952867 2775637554612747670429301)
                ·
                  refine ⟨260216020744945094102747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775637554612747670429301 260216020744945094102747)
                  ·
                    rfl

theorem cell22_2280460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_2280460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280460 prefixEnd_2280460 := by exact prefixLift 2280460
  have htrace : WordTrace (prefixWord ++ tailWord_2280460) baseStart_2280460 baseEnd_2280460 := by
    simpa [prefixWord, tailWord_2280460, baseEnd_2280460] using wordTrace_append hprefix tailTrace_2280460
  have hstable : (prefixWord ++ tailWord_2280460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280460).length < 2 ^ (prefixWord ++ tailWord_2280460).sum := by decide
  have hdescent : baseEnd_2280460 < baseStart_2280460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280473 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_2280473 : Nat := 118140960795 + 2280473 * 2 ^ 59
def prefixEnd_2280473 : Nat := 4983230072969 + 3 ^ 40 * 2280473 * 2
def baseEnd_2280473 : Nat := 780652512400507581733201

theorem tailTrace_2280473 : CollatzResearch.WordTrace tailWord_2280473 prefixEnd_2280473 780652512400507581733201 := by
  unfold tailWord_2280473
  simp only [CollatzResearch.WordTrace]
  refine ⟨83175683467243269625918073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55450455644828846417278715 83175683467243269625918073)
  ·
    refine ⟨62381762600432452219438555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83175683467243269625918073 62381762600432452219438555)
    ·
      refine ⟨93572643900648678329157833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62381762600432452219438555 93572643900648678329157833)
      ·
        refine ⟨70179482925486508746868375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93572643900648678329157833 70179482925486508746868375)
        ·
          refine ⟨105269224388229763120302563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70179482925486508746868375 105269224388229763120302563)
          ·
            refine ⟨157903836582344644680453845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105269224388229763120302563 157903836582344644680453845)
            ·
              refine ⟨3700871169898702609698137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157903836582344644680453845 3700871169898702609698137)
              ·
                refine ⟨2775653377424026957273603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700871169898702609698137 2775653377424026957273603)
                ·
                  refine ⟨4163480066136040435910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775653377424026957273603 4163480066136040435910405)
                  ·
                    refine ⟨780652512400507581733201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4163480066136040435910405 780652512400507581733201)
                    ·
                      rfl

theorem cell22_2280473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_2280473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280473 prefixEnd_2280473 := by exact prefixLift 2280473
  have htrace : WordTrace (prefixWord ++ tailWord_2280473) baseStart_2280473 baseEnd_2280473 := by
    simpa [prefixWord, tailWord_2280473, baseEnd_2280473] using wordTrace_append hprefix tailTrace_2280473
  have hstable : (prefixWord ++ tailWord_2280473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280473).length < 2 ^ (prefixWord ++ tailWord_2280473).sum := by decide
  have hdescent : baseEnd_2280473 < baseStart_2280473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280501 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2280501 : Nat := 118140960795 + 2280501 * 2 ^ 59
def prefixEnd_2280501 : Nat := 4983230072969 + 3 ^ 40 * 2280501 * 2
def baseEnd_2280501 : Nat := 780662097372724842033115

theorem tailTrace_2280501 : CollatzResearch.WordTrace tailWord_2280501 prefixEnd_2280501 780662097372724842033115 := by
  unfold tailWord_2280501
  simp only [CollatzResearch.WordTrace]
  refine ⟨83176704711141830407937357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55451136474094553605291571 83176704711141830407937357)
  ·
    refine ⟨31191264266678186402976509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83176704711141830407937357 31191264266678186402976509)
    ·
      refine ⟨11696724100004319901116191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31191264266678186402976509 11696724100004319901116191)
      ·
        refine ⟨17545086150006479851674287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11696724100004319901116191 17545086150006479851674287)
        ·
          refine ⟨26317629225009719777511431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17545086150006479851674287 26317629225009719777511431)
          ·
            refine ⟨39476443837514579666267147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26317629225009719777511431 39476443837514579666267147)
            ·
              refine ⟨59214665756271869499400721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39476443837514579666267147 59214665756271869499400721)
              ·
                refine ⟨44410999317203902124550541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59214665756271869499400721 44410999317203902124550541)
                ·
                  refine ⟨16654124743951463296706453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44410999317203902124550541 16654124743951463296706453)
                  ·
                    refine ⟨780662097372724842033115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16654124743951463296706453 780662097372724842033115)
                    ·
                      rfl

theorem cell22_2280501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2280501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280501 prefixEnd_2280501 := by exact prefixLift 2280501
  have htrace : WordTrace (prefixWord ++ tailWord_2280501) baseStart_2280501 baseEnd_2280501 := by
    simpa [prefixWord, tailWord_2280501, baseEnd_2280501] using wordTrace_append hprefix tailTrace_2280501
  have hstable : (prefixWord ++ tailWord_2280501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280501).length < 2 ^ (prefixWord ++ tailWord_2280501).sum := by decide
  have hdescent : baseEnd_2280501 < baseStart_2280501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280505 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 4]
def baseStart_2280505 : Nat := 118140960795 + 2280505 * 2 ^ 59
def prefixEnd_2280505 : Nat := 4983230072969 + 3 ^ 40 * 2280505 * 2
def baseEnd_2280505 : Nat := 260221155551490054977701

theorem tailTrace_2280505 : CollatzResearch.WordTrace tailWord_2280505 prefixEnd_2280505 260221155551490054977701 := by
  unfold tailWord_2280505
  simp only [CollatzResearch.WordTrace]
  refine ⟨83176850603127339091082969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55451233735418226060721979 83176850603127339091082969)
  ·
    refine ⟨62382637952345504318312227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83176850603127339091082969 62382637952345504318312227)
    ·
      refine ⟨93573956928518256477468341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62382637952345504318312227 93573956928518256477468341)
      ·
        refine ⟨8772558462048586544762657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93573956928518256477468341 8772558462048586544762657)
        ·
          refine ⟨6579418846536439908571993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8772558462048586544762657 6579418846536439908571993)
          ·
            refine ⟨4934564134902329931428995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6579418846536439908571993 4934564134902329931428995)
            ·
              refine ⟨7401846202353494897143493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934564134902329931428995 7401846202353494897143493)
              ·
                refine ⟨1387846162941280293214405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7401846202353494897143493 1387846162941280293214405)
                ·
                  refine ⟨260221155551490054977701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387846162941280293214405 260221155551490054977701)
                  ·
                    rfl

theorem cell22_2280505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_2280505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280505 prefixEnd_2280505 := by exact prefixLift 2280505
  have htrace : WordTrace (prefixWord ++ tailWord_2280505) baseStart_2280505 baseEnd_2280505 := by
    simpa [prefixWord, tailWord_2280505, baseEnd_2280505] using wordTrace_append hprefix tailTrace_2280505
  have hstable : (prefixWord ++ tailWord_2280505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280505).length < 2 ^ (prefixWord ++ tailWord_2280505).sum := by decide
  have hdescent : baseEnd_2280505 < baseStart_2280505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280533 : List Nat := [1, 3, 2, 2, 1, 2, 5, 6]
def baseStart_2280533 : Nat := 118140960795 + 2280533 * 2 ^ 59
def prefixEnd_2280533 : Nat := 4983230072969 + 3 ^ 40 * 2280533 * 2
def baseEnd_2280533 : Nat := 86741450180743047248113

theorem tailTrace_2280533 : CollatzResearch.WordTrace tailWord_2280533 prefixEnd_2280533 86741450180743047248113 := by
  unfold tailWord_2280533
  simp only [CollatzResearch.WordTrace]
  refine ⟨83177871847025899873102253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55451914564683933248734835 83177871847025899873102253)
  ·
    refine ⟨31191701942634712452413345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83177871847025899873102253 31191701942634712452413345)
    ·
      refine ⟨23393776456976034339310009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31191701942634712452413345 23393776456976034339310009)
      ·
        refine ⟨17545332342732025754482507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23393776456976034339310009 17545332342732025754482507)
        ·
          refine ⟨26317998514098038631723761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17545332342732025754482507 26317998514098038631723761)
          ·
            refine ⟨19738498885573528973792821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26317998514098038631723761 19738498885573528973792821)
            ·
              refine ⟨1850484270522518341293077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19738498885573528973792821 1850484270522518341293077)
              ·
                refine ⟨86741450180743047248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1850484270522518341293077 86741450180743047248113)
                ·
                  rfl

theorem cell22_2280533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 6].length) (baseStart_2280533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280533 prefixEnd_2280533 := by exact prefixLift 2280533
  have htrace : WordTrace (prefixWord ++ tailWord_2280533) baseStart_2280533 baseEnd_2280533 := by
    simpa [prefixWord, tailWord_2280533, baseEnd_2280533] using wordTrace_append hprefix tailTrace_2280533
  have hstable : (prefixWord ++ tailWord_2280533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280533).length < 2 ^ (prefixWord ++ tailWord_2280533).sum := by decide
  have hdescent : baseEnd_2280533 < baseStart_2280533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280541 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2280541 : Nat := 118140960795 + 2280541 * 2 ^ 59
def prefixEnd_2280541 : Nat := 4983230072969 + 3 ^ 40 * 2280541 * 2
def baseEnd_2280541 : Nat := 780675790190178071032993

theorem tailTrace_2280541 : CollatzResearch.WordTrace tailWord_2280541 prefixEnd_2280541 780675790190178071032993 := by
  unfold tailWord_2280541
  simp only [CollatzResearch.WordTrace]
  refine ⟨83178163630996917239393477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55452109087331278159595651 83178163630996917239393477)
  ·
    refine ⟨15595905680811921982386277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83178163630996917239393477 15595905680811921982386277)
    ·
      refine ⟨2924232315152235371697427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15595905680811921982386277 2924232315152235371697427)
      ·
        refine ⟨4386348472728353057546141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924232315152235371697427 4386348472728353057546141)
        ·
          refine ⟨1644880677273132396579803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4386348472728353057546141 1644880677273132396579803)
          ·
            refine ⟨2467321015909698594869705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644880677273132396579803 2467321015909698594869705)
            ·
              refine ⟨1850490761932273946152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467321015909698594869705 1850490761932273946152279)
              ·
                refine ⟨2775736142898410919228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850490761932273946152279 2775736142898410919228419)
                ·
                  refine ⟨4163604214347616378842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775736142898410919228419 4163604214347616378842629)
                  ·
                    refine ⟨780675790190178071032993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4163604214347616378842629 780675790190178071032993)
                    ·
                      rfl

theorem cell22_2280541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2280541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280541 prefixEnd_2280541 := by exact prefixLift 2280541
  have htrace : WordTrace (prefixWord ++ tailWord_2280541) baseStart_2280541 baseEnd_2280541 := by
    simpa [prefixWord, tailWord_2280541, baseEnd_2280541] using wordTrace_append hprefix tailTrace_2280541
  have hstable : (prefixWord ++ tailWord_2280541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280541).length < 2 ^ (prefixWord ++ tailWord_2280541).sum := by decide
  have hdescent : baseEnd_2280541 < baseStart_2280541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280548 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2280548 : Nat := 118140960795 + 2280548 * 2 ^ 59
def prefixEnd_2280548 : Nat := 4983230072969 + 3 ^ 40 * 2280548 * 2
def baseEnd_2280548 : Nat := 780678186433232386107971

theorem tailTrace_2280548 : CollatzResearch.WordTrace tailWord_2280548 prefixEnd_2280548 780678186433232386107971 := by
  unfold tailWord_2280548
  simp only [CollatzResearch.WordTrace]
  refine ⟨41589209470985778717449149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55452279294647704956598865 41589209470985778717449149)
  ·
    refine ⟨15595953551619667019043431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41589209470985778717449149 15595953551619667019043431)
    ·
      refine ⟨23393930327429500528565147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15595953551619667019043431 23393930327429500528565147)
      ·
        refine ⟨35090895491144250792847721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23393930327429500528565147 35090895491144250792847721)
        ·
          refine ⟨26318171618358188094635791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35090895491144250792847721 26318171618358188094635791)
          ·
            refine ⟨39477257427537282141953687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26318171618358188094635791 39477257427537282141953687)
            ·
              refine ⟨59215886141305923212930531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39477257427537282141953687 59215886141305923212930531)
              ·
                refine ⟨88823829211958884819395797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59215886141305923212930531 88823829211958884819395797)
                ·
                  refine ⟨2081808497155286362954589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88823829211958884819395797 2081808497155286362954589)
                  ·
                    refine ⟨780678186433232386107971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081808497155286362954589 780678186433232386107971)
                    ·
                      rfl

theorem cell22_2280548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2280548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280548 prefixEnd_2280548 := by exact prefixLift 2280548
  have htrace : WordTrace (prefixWord ++ tailWord_2280548) baseStart_2280548 baseEnd_2280548 := by
    simpa [prefixWord, tailWord_2280548, baseEnd_2280548] using wordTrace_append hprefix tailTrace_2280548
  have hstable : (prefixWord ++ tailWord_2280548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280548).length < 2 ^ (prefixWord ++ tailWord_2280548).sum := by decide
  have hdescent : baseEnd_2280548 < baseStart_2280548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280599 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 1, 3]
def baseStart_2280599 : Nat := 118140960795 + 2280599 * 2 ^ 59
def prefixEnd_2280599 : Nat := 4983230072969 + 3 ^ 40 * 2280599 * 2
def baseEnd_2280599 : Nat := 780695644775485253082815

theorem tailTrace_2280599 : CollatzResearch.WordTrace tailWord_2280599 prefixEnd_2280599 780695644775485253082815 := by
  unfold tailWord_2280599
  simp only [CollatzResearch.WordTrace]
  refine ⟨83180279064786793145004851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55453519376524528763336567 83180279064786793145004851)
  ·
    refine ⟨124770418597180189717507277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83180279064786793145004851 124770418597180189717507277)
    ·
      refine ⟨46788906973942571144065229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124770418597180189717507277 46788906973942571144065229)
      ·
        refine ⟨17545840115228464179024461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46788906973942571144065229 17545840115228464179024461)
        ·
          refine ⟨6579690043210674067134173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17545840115228464179024461 6579690043210674067134173)
          ·
            refine ⟨2467383766204002775175315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6579690043210674067134173 2467383766204002775175315)
            ·
              refine ⟨3701075649306004162762973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467383766204002775175315 3701075649306004162762973)
              ·
                refine ⟨1387903368489751561036115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701075649306004162762973 1387903368489751561036115)
                ·
                  refine ⟨2081855052734627341554173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387903368489751561036115 2081855052734627341554173)
                  ·
                    refine ⟨780695644775485253082815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081855052734627341554173 780695644775485253082815)
                    ·
                      rfl

theorem cell22_2280599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_2280599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280599 prefixEnd_2280599 := by exact prefixLift 2280599
  have htrace : WordTrace (prefixWord ++ tailWord_2280599) baseStart_2280599 baseEnd_2280599 := by
    simpa [prefixWord, tailWord_2280599, baseEnd_2280599] using wordTrace_append hprefix tailTrace_2280599
  have hstable : (prefixWord ++ tailWord_2280599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280599).length < 2 ^ (prefixWord ++ tailWord_2280599).sum := by decide
  have hdescent : baseEnd_2280599 < baseStart_2280599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280623 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 6]
def baseStart_2280623 : Nat := 118140960795 + 2280623 * 2 ^ 59
def prefixEnd_2280623 : Nat := 4983230072969 + 3 ^ 40 * 2280623 * 2
def baseEnd_2280623 : Nat := 260234620155319063494247

theorem tailTrace_2280623 : CollatzResearch.WordTrace tailWord_2280623 prefixEnd_2280623 260234620155319063494247 := by
  unfold tailWord_2280623
  simp only [CollatzResearch.WordTrace]
  refine ⟨83181154416699845243878523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55454102944466563495919015 83181154416699845243878523)
  ·
    refine ⟨124771731625049767865817785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83181154416699845243878523 124771731625049767865817785)
    ·
      refine ⟨93578798718787325899363339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124771731625049767865817785 93578798718787325899363339)
      ·
        refine ⟨140368198078180988849045009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93578798718787325899363339 140368198078180988849045009)
        ·
          refine ⟨105276148558635741636783757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140368198078180988849045009 105276148558635741636783757)
          ·
            refine ⟨39478555709488403113793909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105276148558635741636783757 39478555709488403113793909)
            ·
              refine ⟨3701114597764537791918179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39478555709488403113793909 3701114597764537791918179)
              ·
                refine ⟨5551671896646806687877269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3701114597764537791918179 5551671896646806687877269)
                ·
                  refine ⟨260234620155319063494247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5551671896646806687877269 260234620155319063494247)
                  ·
                    rfl

theorem cell22_2280623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_2280623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280623 prefixEnd_2280623 := by exact prefixLift 2280623
  have htrace : WordTrace (prefixWord ++ tailWord_2280623) baseStart_2280623 baseEnd_2280623 := by
    simpa [prefixWord, tailWord_2280623, baseEnd_2280623] using wordTrace_append hprefix tailTrace_2280623
  have hstable : (prefixWord ++ tailWord_2280623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280623).length < 2 ^ (prefixWord ++ tailWord_2280623).sum := by decide
  have hdescent : baseEnd_2280623 < baseStart_2280623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280668 : List Nat := [2, 2, 5, 13]
def baseStart_2280668 : Nat := 118140960795 + 2280668 * 2 ^ 59
def prefixEnd_2280668 : Nat := 4983230072969 + 3 ^ 40 * 2280668 * 2
def baseEnd_2280668 : Nat := 1070945493670222322507

theorem tailTrace_2280668 : CollatzResearch.WordTrace tailWord_2280668 prefixEnd_2280668 1070945493670222322507 := by
  unfold tailWord_2280668
  simp only [CollatzResearch.WordTrace]
  refine ⟨41591397850768408964633329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55455197134357878619511105 41591397850768408964633329)
  ·
    refine ⟨31193548388076306723474997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41591397850768408964633329 31193548388076306723474997)
    ·
      refine ⟨2924395161382153755325781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31193548388076306723474997 2924395161382153755325781)
      ·
        refine ⟨1070945493670222322507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2924395161382153755325781 1070945493670222322507)
        ·
          rfl

theorem cell22_2280668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 13].length) (baseStart_2280668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280668 prefixEnd_2280668 := by exact prefixLift 2280668
  have htrace : WordTrace (prefixWord ++ tailWord_2280668) baseStart_2280668 baseEnd_2280668 := by
    simpa [prefixWord, tailWord_2280668, baseEnd_2280668] using wordTrace_append hprefix tailTrace_2280668
  have hstable : (prefixWord ++ tailWord_2280668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280668).length < 2 ^ (prefixWord ++ tailWord_2280668).sum := by decide
  have hdescent : baseEnd_2280668 < baseStart_2280668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280672 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_2280672 : Nat := 118140960795 + 2280672 * 2 ^ 59
def prefixEnd_2280672 : Nat := 4983230072969 + 3 ^ 40 * 2280672 * 2
def baseEnd_2280672 : Nat := 780720634167337396007591

theorem tailTrace_2280672 : CollatzResearch.WordTrace tailWord_2280672 prefixEnd_2280672 780720634167337396007591 := by
  unfold tailWord_2280672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41591470796761163306206135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55455294395681551074941513 41591470796761163306206135)
  ·
    refine ⟨62387206195141744959309203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41591470796761163306206135 62387206195141744959309203)
    ·
      refine ⟨93580809292712617438963805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62387206195141744959309203 93580809292712617438963805)
      ·
        refine ⟨35092803484767231539611427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93580809292712617438963805 35092803484767231539611427)
        ·
          refine ⟨52639205227150847309417141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35092803484767231539611427 52639205227150847309417141)
          ·
            refine ⟨4934925490045391935257857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52639205227150847309417141 4934925490045391935257857)
            ·
              refine ⟨3701194117534043951443393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4934925490045391935257857 3701194117534043951443393)
              ·
                refine ⟨2775895588150532963582545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701194117534043951443393 2775895588150532963582545)
                ·
                  refine ⟨2081921691112899722686909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2775895588150532963582545 2081921691112899722686909)
                  ·
                    refine ⟨780720634167337396007591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2081921691112899722686909 780720634167337396007591)
                    ·
                      rfl

theorem cell22_2280672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_2280672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280672 prefixEnd_2280672 := by exact prefixLift 2280672
  have htrace : WordTrace (prefixWord ++ tailWord_2280672) baseStart_2280672 baseEnd_2280672 := by
    simpa [prefixWord, tailWord_2280672, baseEnd_2280672] using wordTrace_append hprefix tailTrace_2280672
  have hstable : (prefixWord ++ tailWord_2280672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280672).length < 2 ^ (prefixWord ++ tailWord_2280672).sum := by decide
  have hdescent : baseEnd_2280672 < baseStart_2280672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280685 : List Nat := [1, 5, 1, 2, 2, 1, 3, 7]
def baseStart_2280685 : Nat := 118140960795 + 2280685 * 2 ^ 59
def prefixEnd_2280685 : Nat := 4983230072969 + 3 ^ 40 * 2280685 * 2
def baseEnd_2280685 : Nat := 86747231592556632825839

theorem tailTrace_2280685 : CollatzResearch.WordTrace tailWord_2280685 prefixEnd_2280685 86747231592556632825839 := by
  unfold tailWord_2280685
  simp only [CollatzResearch.WordTrace]
  refine ⟨83183415742475229832635509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55455610494983486555090339 83183415742475229832635509)
  ·
    refine ⟨7798445225857052796809579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83183415742475229832635509 7798445225857052796809579)
    ·
      refine ⟨11697667838785579195214369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798445225857052796809579 11697667838785579195214369)
      ·
        refine ⟨8773250879089184396410777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697667838785579195214369 8773250879089184396410777)
        ·
          refine ⟨6579938159316888297308083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8773250879089184396410777 6579938159316888297308083)
          ·
            refine ⟨9869907238975332445962125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579938159316888297308083 9869907238975332445962125)
            ·
              refine ⟨3701215214615749667235797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9869907238975332445962125 3701215214615749667235797)
              ·
                refine ⟨86747231592556632825839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3701215214615749667235797 86747231592556632825839)
                ·
                  rfl

theorem cell22_2280685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 7].length) (baseStart_2280685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280685 prefixEnd_2280685 := by exact prefixLift 2280685
  have htrace : WordTrace (prefixWord ++ tailWord_2280685) baseStart_2280685 baseEnd_2280685 := by
    simpa [prefixWord, tailWord_2280685, baseEnd_2280685] using wordTrace_append hprefix tailTrace_2280685
  have hstable : (prefixWord ++ tailWord_2280685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280685).length < 2 ^ (prefixWord ++ tailWord_2280685).sum := by decide
  have hdescent : baseEnd_2280685 < baseStart_2280685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280698 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_2280698 : Nat := 118140960795 + 2280698 * 2 ^ 59
def prefixEnd_2280698 : Nat := 4983230072969 + 3 ^ 40 * 2280698 * 2
def baseEnd_2280698 : Nat := 780729534498681994857511

theorem tailTrace_2280698 : CollatzResearch.WordTrace tailWord_2280698 prefixEnd_2280698 780729534498681994857511 := by
  unfold tailWord_2280698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795972472857033263214687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55455926594285422035239165 20795972472857033263214687)
  ·
    refine ⟨31193958709285549894822031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20795972472857033263214687 31193958709285549894822031)
    ·
      refine ⟨46790938063928324842233047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31193958709285549894822031 46790938063928324842233047)
      ·
        refine ⟨70186407095892487263349571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46790938063928324842233047 70186407095892487263349571)
        ·
          refine ⟨105279610643838730895024357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70186407095892487263349571 105279610643838730895024357)
          ·
            refine ⟨19739926995719762042817067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105279610643838730895024357 19739926995719762042817067)
            ·
              refine ⟨29609890493579643064225601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19739926995719762042817067 29609890493579643064225601)
              ·
                refine ⟨22207417870184732298169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29609890493579643064225601 22207417870184732298169201)
                ·
                  refine ⟨16655563402638549223626901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22207417870184732298169201 16655563402638549223626901)
                  ·
                    refine ⟨780729534498681994857511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16655563402638549223626901 780729534498681994857511)
                    ·
                      rfl

theorem cell22_2280698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_2280698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280698 prefixEnd_2280698 := by exact prefixLift 2280698
  have htrace : WordTrace (prefixWord ++ tailWord_2280698) baseStart_2280698 baseEnd_2280698 := by
    simpa [prefixWord, tailWord_2280698, baseEnd_2280698] using wordTrace_append hprefix tailTrace_2280698
  have hstable : (prefixWord ++ tailWord_2280698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280698).length < 2 ^ (prefixWord ++ tailWord_2280698).sum := by decide
  have hdescent : baseEnd_2280698 < baseStart_2280698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280702 : List Nat := [4, 2, 2, 1, 1, 3, 3, 6]
def baseStart_2280702 : Nat := 118140960795 + 2280702 * 2 ^ 59
def prefixEnd_2280702 : Nat := 4983230072969 + 3 ^ 40 * 2280702 * 2
def baseEnd_2280702 : Nat := 86747878197825257528611

theorem tailTrace_2280702 : CollatzResearch.WordTrace tailWord_2280702 prefixEnd_2280702 86747878197825257528611 := by
  unfold tailWord_2280702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398004472926705217000545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55456023855609094490669573 10398004472926705217000545)
  ·
    refine ⟨7798503354695028912750409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10398004472926705217000545 7798503354695028912750409)
    ·
      refine ⟨5848877516021271684562807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7798503354695028912750409 5848877516021271684562807)
      ·
        refine ⟨8773316274031907526844211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848877516021271684562807 8773316274031907526844211)
        ·
          refine ⟨13159974411047861290266317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8773316274031907526844211 13159974411047861290266317)
          ·
            refine ⟨4934990404142947983849869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13159974411047861290266317 4934990404142947983849869)
            ·
              refine ⟨1850621401553605493943701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4934990404142947983849869 1850621401553605493943701)
              ·
                refine ⟨86747878197825257528611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1850621401553605493943701 86747878197825257528611)
                ·
                  rfl

theorem cell22_2280702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_2280702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280702 prefixEnd_2280702 := by exact prefixLift 2280702
  have htrace : WordTrace (prefixWord ++ tailWord_2280702) baseStart_2280702 baseEnd_2280702 := by
    simpa [prefixWord, tailWord_2280702, baseEnd_2280702] using wordTrace_append hprefix tailTrace_2280702
  have hstable : (prefixWord ++ tailWord_2280702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280702).length < 2 ^ (prefixWord ++ tailWord_2280702).sum := by decide
  have hdescent : baseEnd_2280702 < baseStart_2280702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280713 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 7]
def baseStart_2280713 : Nat := 118140960795 + 2280713 * 2 ^ 59
def prefixEnd_2280713 : Nat := 4983230072969 + 3 ^ 40 * 2280713 * 2
def baseEnd_2280713 : Nat := 260244889768408985244155

theorem tailTrace_2280713 : CollatzResearch.WordTrace tailWord_2280713 prefixEnd_2280713 260244889768408985244155 := by
  unfold tailWord_2280713
  simp only [CollatzResearch.WordTrace]
  refine ⟨83184436986373790614654793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55456291324249193743103195 83184436986373790614654793)
  ·
    refine ⟨62388327739780342960991095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83184436986373790614654793 62388327739780342960991095)
    ·
      refine ⟨93582491609670514441486643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62388327739780342960991095 93582491609670514441486643)
      ·
        refine ⟨140373737414505771662229965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93582491609670514441486643 140373737414505771662229965)
        ·
          refine ⟨52640151530439664373336237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140373737414505771662229965 52640151530439664373336237)
          ·
            refine ⟨19740056823914874140001089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52640151530439664373336237 19740056823914874140001089)
            ·
              refine ⟨14805042617936155605000817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19740056823914874140001089 14805042617936155605000817)
              ·
                refine ⟨11103781963452116703750613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14805042617936155605000817 11103781963452116703750613)
                ·
                  refine ⟨260244889768408985244155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11103781963452116703750613 260244889768408985244155)
                  ·
                    rfl

theorem cell22_2280713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_2280713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280713 prefixEnd_2280713 := by exact prefixLift 2280713
  have htrace : WordTrace (prefixWord ++ tailWord_2280713) baseStart_2280713 baseEnd_2280713 := by
    simpa [prefixWord, tailWord_2280713, baseEnd_2280713] using wordTrace_append hprefix tailTrace_2280713
  have hstable : (prefixWord ++ tailWord_2280713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280713).length < 2 ^ (prefixWord ++ tailWord_2280713).sum := by decide
  have hdescent : baseEnd_2280713 < baseStart_2280713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280730 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_2280730 : Nat := 118140960795 + 2280730 * 2 ^ 59
def prefixEnd_2280730 : Nat := 4983230072969 + 3 ^ 40 * 2280730 * 2
def baseEnd_2280730 : Nat := 260246829584214859352471

theorem tailTrace_2280730 : CollatzResearch.WordTrace tailWord_2280730 prefixEnd_2280730 260246829584214859352471 := by
  unfold tailWord_2280730
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796264256828050629505911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55456704684874801678682429 20796264256828050629505911)
  ·
    refine ⟨31194396385242075944258867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796264256828050629505911 31194396385242075944258867)
    ·
      refine ⟨46791594577863113916388301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31194396385242075944258867 46791594577863113916388301)
      ·
        refine ⟨17546847966698667718645613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46791594577863113916388301 17546847966698667718645613)
        ·
          refine ⟨6580067987512000394492105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17546847966698667718645613 6580067987512000394492105)
          ·
            refine ⟨4935050990634000295869079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580067987512000394492105 4935050990634000295869079)
            ·
              refine ⟨7402576485951000443803619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935050990634000295869079 7402576485951000443803619)
              ·
                refine ⟨11103864728926500665705429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402576485951000443803619 11103864728926500665705429)
                ·
                  refine ⟨260246829584214859352471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11103864728926500665705429 260246829584214859352471)
                  ·
                    rfl

theorem cell22_2280730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_2280730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280730 prefixEnd_2280730 := by exact prefixLift 2280730
  have htrace : WordTrace (prefixWord ++ tailWord_2280730) baseStart_2280730 baseEnd_2280730 := by
    simpa [prefixWord, tailWord_2280730, baseEnd_2280730] using wordTrace_append hprefix tailTrace_2280730
  have hstable : (prefixWord ++ tailWord_2280730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280730).length < 2 ^ (prefixWord ++ tailWord_2280730).sum := by decide
  have hdescent : baseEnd_2280730 < baseStart_2280730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280805 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2280805 : Nat := 118140960795 + 2280805 * 2 ^ 59
def prefixEnd_2280805 : Nat := 4983230072969 + 3 ^ 40 * 2280805 * 2
def baseEnd_2280805 : Nat := 780766162785369382432183

theorem tailTrace_2280805 : CollatzResearch.WordTrace tailWord_2280805 prefixEnd_2280805 780766162785369382432183 := by
  unfold tailWord_2280805
  simp only [CollatzResearch.WordTrace]
  refine ⟨83187792502040490327003869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55458528334693660218002579 83187792502040490327003869)
  ·
    refine ⟨31195422188265183872626451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83187792502040490327003869 31195422188265183872626451)
    ·
      refine ⟨46793133282397775808939677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31195422188265183872626451 46793133282397775808939677)
      ·
        refine ⟨17547424980899165928352379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46793133282397775808939677 17547424980899165928352379)
        ·
          refine ⟨26321137471348748892528569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17547424980899165928352379 26321137471348748892528569)
          ·
            refine ⟨19740853103511561669396427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26321137471348748892528569 19740853103511561669396427)
            ·
              refine ⟨29611279655267342504094641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19740853103511561669396427 29611279655267342504094641)
              ·
                refine ⟨22208459741450506878070981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29611279655267342504094641 22208459741450506878070981)
                ·
                  refine ⟨4164086201521970039638309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22208459741450506878070981 4164086201521970039638309)
                  ·
                    refine ⟨780766162785369382432183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164086201521970039638309 780766162785369382432183)
                    ·
                      rfl

theorem cell22_2280805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2280805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280805 prefixEnd_2280805 := by exact prefixLift 2280805
  have htrace : WordTrace (prefixWord ++ tailWord_2280805) baseStart_2280805 baseEnd_2280805 := by
    simpa [prefixWord, tailWord_2280805, baseEnd_2280805] using wordTrace_append hprefix tailTrace_2280805
  have hstable : (prefixWord ++ tailWord_2280805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280805).length < 2 ^ (prefixWord ++ tailWord_2280805).sum := by decide
  have hdescent : baseEnd_2280805 < baseStart_2280805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280916 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2280916 : Nat := 118140960795 + 2280916 * 2 ^ 59
def prefixEnd_2280916 : Nat := 4983230072969 + 3 ^ 40 * 2280916 * 2
def baseEnd_2280916 : Nat := 260268053451267364302281

theorem tailTrace_2280916 : CollatzResearch.WordTrace tailWord_2280916 prefixEnd_2280916 260268053451267364302281 := by
  unfold tailWord_2280916
  simp only [CollatzResearch.WordTrace]
  refine ⟨41595920502319178142147301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55461227336425570856196401 41595920502319178142147301)
  ·
    refine ⟨7799235094184845901652619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41595920502319178142147301 7799235094184845901652619)
    ·
      refine ⟨11698852641277268852478929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799235094184845901652619 11698852641277268852478929)
      ·
        refine ⟨8774139480957951639359197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11698852641277268852478929 8774139480957951639359197)
        ·
          refine ⟨3290302305359231864759699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8774139480957951639359197 3290302305359231864759699)
          ·
            refine ⟨4935453458038847797139549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290302305359231864759699 4935453458038847797139549)
            ·
              refine ⟨1850795046764567923927331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4935453458038847797139549 1850795046764567923927331)
              ·
                refine ⟨2776192570146851885890997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850795046764567923927331 2776192570146851885890997)
                ·
                  refine ⟨260268053451267364302281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776192570146851885890997 260268053451267364302281)
                  ·
                    rfl

theorem cell22_2280916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2280916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280916 prefixEnd_2280916 := by exact prefixLift 2280916
  have htrace : WordTrace (prefixWord ++ tailWord_2280916) baseStart_2280916 baseEnd_2280916 := by
    simpa [prefixWord, tailWord_2280916, baseEnd_2280916] using wordTrace_append hprefix tailTrace_2280916
  have hstable : (prefixWord ++ tailWord_2280916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280916).length < 2 ^ (prefixWord ++ tailWord_2280916).sum := by decide
  have hdescent : baseEnd_2280916 < baseStart_2280916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280929 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2280929 : Nat := 118140960795 + 2280929 * 2 ^ 59
def prefixEnd_2280929 : Nat := 4983230072969 + 3 ^ 40 * 2280929 * 2
def baseEnd_2280929 : Nat := 780808610519474392331803

theorem tailTrace_2280929 : CollatzResearch.WordTrace tailWord_2280929 prefixEnd_2280929 780808610519474392331803 := by
  unfold tailWord_2280929
  simp only [CollatzResearch.WordTrace]
  refine ⟨83192315153591259504517841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55461543435727506336345227 83192315153591259504517841)
  ·
    refine ⟨62394236365193444628388381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83192315153591259504517841 62394236365193444628388381)
    ·
      refine ⟨23397838636947541735645643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62394236365193444628388381 23397838636947541735645643)
      ·
        refine ⟨35096757955421312603468465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23397838636947541735645643 35096757955421312603468465)
        ·
          refine ⟨26322568466565984452601349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35096757955421312603468465 26322568466565984452601349)
          ·
            refine ⟨4935481587481122084862753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26322568466565984452601349 4935481587481122084862753)
            ·
              refine ⟨3701611190610841563647065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935481587481122084862753 3701611190610841563647065)
              ·
                refine ⟨2776208392958131172735299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701611190610841563647065 2776208392958131172735299)
                ·
                  refine ⟨4164312589437196759102949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776208392958131172735299 4164312589437196759102949)
                  ·
                    refine ⟨780808610519474392331803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164312589437196759102949 780808610519474392331803)
                    ·
                      rfl

theorem cell22_2280929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2280929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280929 prefixEnd_2280929 := by exact prefixLift 2280929
  have htrace : WordTrace (prefixWord ++ tailWord_2280929) baseStart_2280929 baseEnd_2280929 := by
    simpa [prefixWord, tailWord_2280929, baseEnd_2280929] using wordTrace_append hprefix tailTrace_2280929
  have hstable : (prefixWord ++ tailWord_2280929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280929).length < 2 ^ (prefixWord ++ tailWord_2280929).sum := by decide
  have hdescent : baseEnd_2280929 < baseStart_2280929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280942 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2280942 : Nat := 118140960795 + 2280942 * 2 ^ 59
def prefixEnd_2280942 : Nat := 4983230072969 + 3 ^ 40 * 2280942 * 2
def baseEnd_2280942 : Nat := 780813060685146691756763

theorem tailTrace_2280942 : CollatzResearch.WordTrace tailWord_2280942 prefixEnd_2280942 780813060685146691756763 := by
  unfold tailWord_2280942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399098662818020340592635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55461859535029441816494053 10399098662818020340592635)
  ·
    refine ⟨15598647994227030510888953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10399098662818020340592635 15598647994227030510888953)
    ·
      refine ⟨11698985995670272883166715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15598647994227030510888953 11698985995670272883166715)
      ·
        refine ⟨17548478993505409324750073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11698985995670272883166715 17548478993505409324750073)
        ·
          refine ⟨13161359245129056993562555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17548478993505409324750073 13161359245129056993562555)
          ·
            refine ⟨19742038867693585490343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161359245129056993562555 19742038867693585490343833)
            ·
              refine ⟨14806529150770189117757875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19742038867693585490343833 14806529150770189117757875)
              ·
                refine ⟨22209793726155283676636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14806529150770189117757875 22209793726155283676636813)
                ·
                  refine ⟨8328672647308231378738805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22209793726155283676636813 8328672647308231378738805)
                  ·
                    refine ⟨780813060685146691756763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8328672647308231378738805 780813060685146691756763)
                    ·
                      rfl

theorem cell22_2280942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2280942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280942 prefixEnd_2280942 := by exact prefixLift 2280942
  have htrace : WordTrace (prefixWord ++ tailWord_2280942) baseStart_2280942 baseEnd_2280942 := by
    simpa [prefixWord, tailWord_2280942, baseEnd_2280942] using wordTrace_append hprefix tailTrace_2280942
  have hstable : (prefixWord ++ tailWord_2280942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280942).length < 2 ^ (prefixWord ++ tailWord_2280942).sum := by decide
  have hdescent : baseEnd_2280942 < baseStart_2280942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280944 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_2280944 : Nat := 118140960795 + 2280944 * 2 ^ 59
def prefixEnd_2280944 : Nat := 4983230072969 + 3 ^ 40 * 2280944 * 2
def baseEnd_2280944 : Nat := 260271248442006451068919

theorem tailTrace_2280944 : CollatzResearch.WordTrace tailWord_2280944 prefixEnd_2280944 260271248442006451068919 := by
  unfold tailWord_2280944
  simp only [CollatzResearch.WordTrace]
  refine ⟨41596431124268458533156943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55461908165691278044209257 41596431124268458533156943)
  ·
    refine ⟨62394646686402687799735415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41596431124268458533156943 62394646686402687799735415)
    ·
      refine ⟨93591970029604031699603123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62394646686402687799735415 93591970029604031699603123)
      ·
        refine ⟨140387955044406047549404685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93591970029604031699603123 140387955044406047549404685)
        ·
          refine ⟨52645483141652267831026757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140387955044406047549404685 52645483141652267831026757)
          ·
            refine ⟨9871028089059800218317517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52645483141652267831026757 9871028089059800218317517)
            ·
              refine ⟨3701635533397425081869069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9871028089059800218317517 3701635533397425081869069)
              ·
                refine ⟨1388113325024034405700901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701635533397425081869069 1388113325024034405700901)
                ·
                  refine ⟨260271248442006451068919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388113325024034405700901 260271248442006451068919)
                  ·
                    rfl

theorem cell22_2280944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_2280944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280944 prefixEnd_2280944 := by exact prefixLift 2280944
  have htrace : WordTrace (prefixWord ++ tailWord_2280944) baseStart_2280944 baseEnd_2280944 := by
    simpa [prefixWord, tailWord_2280944, baseEnd_2280944] using wordTrace_append hprefix tailTrace_2280944
  have hstable : (prefixWord ++ tailWord_2280944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280944).length < 2 ^ (prefixWord ++ tailWord_2280944).sum := by decide
  have hdescent : baseEnd_2280944 < baseStart_2280944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280957 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2280957 : Nat := 118140960795 + 2280957 * 2 ^ 59
def prefixEnd_2280957 : Nat := 4983230072969 + 3 ^ 40 * 2280957 * 2
def baseEnd_2280957 : Nat := 780818195491691652631717

theorem tailTrace_2280957 : CollatzResearch.WordTrace tailWord_2280957 prefixEnd_2280957 780818195491691652631717 := by
  unfold tailWord_2280957
  simp only [CollatzResearch.WordTrace]
  refine ⟨83193336397489820286537125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55462224264993213524358083 83193336397489820286537125)
  ·
    refine ⟨15598750574529341303725711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83193336397489820286537125 15598750574529341303725711)
    ·
      refine ⟨23398125861794011955588567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15598750574529341303725711 23398125861794011955588567)
      ·
        refine ⟨35097188792691017933382851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23398125861794011955588567 35097188792691017933382851)
        ·
          refine ⟨52645783189036526900074277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35097188792691017933382851 52645783189036526900074277)
          ·
            refine ⟨9871084347944348793763927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52645783189036526900074277 9871084347944348793763927)
            ·
              refine ⟨14806626521916523190645891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9871084347944348793763927 14806626521916523190645891)
              ·
                refine ⟨22209939782874784785968837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14806626521916523190645891 22209939782874784785968837)
                ·
                  refine ⟨4164363709289022147369157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22209939782874784785968837 4164363709289022147369157)
                  ·
                    refine ⟨780818195491691652631717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164363709289022147369157 780818195491691652631717)
                    ·
                      rfl

theorem cell22_2280957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2280957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280957 prefixEnd_2280957 := by exact prefixLift 2280957
  have htrace : WordTrace (prefixWord ++ tailWord_2280957) baseStart_2280957 baseEnd_2280957 := by
    simpa [prefixWord, tailWord_2280957, baseEnd_2280957] using wordTrace_append hprefix tailTrace_2280957
  have hstable : (prefixWord ++ tailWord_2280957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280957).length < 2 ^ (prefixWord ++ tailWord_2280957).sum := by decide
  have hdescent : baseEnd_2280957 < baseStart_2280957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280961 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 6]
def baseStart_2280961 : Nat := 118140960795 + 2280961 * 2 ^ 59
def prefixEnd_2280961 : Nat := 4983230072969 + 3 ^ 40 * 2280961 * 2
def baseEnd_2280961 : Nat := 260273188257812325177235

theorem tailTrace_2280961 : CollatzResearch.WordTrace tailWord_2280961 prefixEnd_2280961 260273188257812325177235 := by
  unfold tailWord_2280961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83193482289475328969682737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55462321526316885979788491 83193482289475328969682737)
  ·
    refine ⟨62395111717106496727262053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83193482289475328969682737 62395111717106496727262053)
    ·
      refine ⟨11699083446957468136361635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62395111717106496727262053 11699083446957468136361635)
      ·
        refine ⟨17548625170436202204542453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699083446957468136361635 17548625170436202204542453)
        ·
          refine ⟨1645183609728393956675855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17548625170436202204542453 1645183609728393956675855)
          ·
            refine ⟨2467775414592590935013783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645183609728393956675855 2467775414592590935013783)
            ·
              refine ⟨3701663121888886402520675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467775414592590935013783 3701663121888886402520675)
              ·
                refine ⟨5552494682833329603781013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3701663121888886402520675 5552494682833329603781013)
                ·
                  refine ⟨260273188257812325177235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5552494682833329603781013 260273188257812325177235)
                  ·
                    rfl

theorem cell22_2280961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_2280961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280961 prefixEnd_2280961 := by exact prefixLift 2280961
  have htrace : WordTrace (prefixWord ++ tailWord_2280961) baseStart_2280961 baseEnd_2280961 := by
    simpa [prefixWord, tailWord_2280961, baseEnd_2280961] using wordTrace_append hprefix tailTrace_2280961
  have hstable : (prefixWord ++ tailWord_2280961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280961).length < 2 ^ (prefixWord ++ tailWord_2280961).sum := by decide
  have hdescent : baseEnd_2280961 < baseStart_2280961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280980 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2280980 : Nat := 118140960795 + 2280980 * 2 ^ 59
def prefixEnd_2280980 : Nat := 4983230072969 + 3 ^ 40 * 2280980 * 2
def baseEnd_2280980 : Nat := 780826068861727259306647

theorem tailTrace_2280980 : CollatzResearch.WordTrace tailWord_2280980 prefixEnd_2280980 780826068861727259306647 := by
  unfold tailWord_2280980
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597087638203247607312197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55462783517604330143082929 41597087638203247607312197)
  ·
    refine ⟨7799453932163108926371037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41597087638203247607312197 7799453932163108926371037)
    ·
      refine ⟨2924795224561165847389139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7799453932163108926371037 2924795224561165847389139)
      ·
        refine ⟨4387192836841748771083709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924795224561165847389139 4387192836841748771083709)
        ·
          refine ⟨1645197313815655789156391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387192836841748771083709 1645197313815655789156391)
          ·
            refine ⟨2467795970723483683734587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645197313815655789156391 2467795970723483683734587)
            ·
              refine ⟨3701693956085225525601881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467795970723483683734587 3701693956085225525601881)
              ·
                refine ⟨2776270467063919144201411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701693956085225525601881 2776270467063919144201411)
                ·
                  refine ⟨4164405700595878716302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776270467063919144201411 4164405700595878716302117)
                  ·
                    refine ⟨780826068861727259306647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164405700595878716302117 780826068861727259306647)
                    ·
                      rfl

theorem cell22_2280980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2280980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2280980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2280980 prefixEnd_2280980 := by exact prefixLift 2280980
  have htrace : WordTrace (prefixWord ++ tailWord_2280980) baseStart_2280980 baseEnd_2280980 := by
    simpa [prefixWord, tailWord_2280980, baseEnd_2280980] using wordTrace_append hprefix tailTrace_2280980
  have hstable : (prefixWord ++ tailWord_2280980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280980).length < 2 ^ (prefixWord ++ tailWord_2280980).sum := by decide
  have hdescent : baseEnd_2280980 < baseStart_2280980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281124 : List Nat := [2, 3, 1, 2, 2, 4, 8]
def baseStart_2281124 : Nat := 118140960795 + 2281124 * 2 ^ 59
def prefixEnd_2281124 : Nat := 4983230072969 + 3 ^ 40 * 2281124 * 2
def baseEnd_2281124 : Nat := 28921309740909588285415

theorem tailTrace_2281124 : CollatzResearch.WordTrace tailWord_2281124 prefixEnd_2281124 28921309740909588285415 := by
  unfold tailWord_2281124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41599713693942403903933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55466284925256538538577617 41599713693942403903933213)
  ·
    refine ⟨15599892635228401463974955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41599713693942403903933213 15599892635228401463974955)
    ·
      refine ⟨23399838952842602195962433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15599892635228401463974955 23399838952842602195962433)
      ·
        refine ⟨17549879214631951646971825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23399838952842602195962433 17549879214631951646971825)
        ·
          refine ⟨13162409410973963735228869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17549879214631951646971825 13162409410973963735228869)
          ·
            refine ⟨2467951764557618200355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13162409410973963735228869 2467951764557618200355413)
            ·
              refine ⟨28921309740909588285415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2467951764557618200355413 28921309740909588285415)
              ·
                rfl

theorem cell22_2281124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 8].length) (baseStart_2281124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281124 prefixEnd_2281124 := by exact prefixLift 2281124
  have htrace : WordTrace (prefixWord ++ tailWord_2281124) baseStart_2281124 baseEnd_2281124 := by
    simpa [prefixWord, tailWord_2281124, baseEnd_2281124] using wordTrace_append hprefix tailTrace_2281124
  have hstable : (prefixWord ++ tailWord_2281124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281124).length < 2 ^ (prefixWord ++ tailWord_2281124).sum := by decide
  have hdescent : baseEnd_2281124 < baseStart_2281124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281141 : List Nat := [1, 3, 3, 3, 2, 1, 2, 7]
def baseStart_2281141 : Nat := 118140960795 + 2281141 * 2 ^ 59
def prefixEnd_2281141 : Nat := 4983230072969 + 3 ^ 40 * 2281141 * 2
def baseEnd_2281141 : Nat := 86764575827997389559017

theorem tailTrace_2281141 : CollatzResearch.WordTrace tailWord_2281141 prefixEnd_2281141 86764575827997389559017 := by
  unfold tailWord_2281141
  simp only [CollatzResearch.WordTrace]
  refine ⟨83200047428823219711235277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55466698285882146474156851 83200047428823219711235277)
  ·
    refine ⟨31200017785808707391713229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83200047428823219711235277 31200017785808707391713229)
    ·
      refine ⟨11700006669678265271892461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31200017785808707391713229 11700006669678265271892461)
      ·
        refine ⟨4387502501129349476959673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11700006669678265271892461 4387502501129349476959673)
        ·
          refine ⟨3290626875847012107719755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387502501129349476959673 3290626875847012107719755)
          ·
            refine ⟨4935940313770518161579633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290626875847012107719755 4935940313770518161579633)
            ·
              refine ⟨3701955235327888621184725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935940313770518161579633 3701955235327888621184725)
              ·
                refine ⟨86764575827997389559017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3701955235327888621184725 86764575827997389559017)
                ·
                  rfl

theorem cell22_2281141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 7].length) (baseStart_2281141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281141 prefixEnd_2281141 := by exact prefixLift 2281141
  have htrace : WordTrace (prefixWord ++ tailWord_2281141) baseStart_2281141 baseEnd_2281141 := by
    simpa [prefixWord, tailWord_2281141, baseEnd_2281141] using wordTrace_append hprefix tailTrace_2281141
  have hstable : (prefixWord ++ tailWord_2281141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281141).length < 2 ^ (prefixWord ++ tailWord_2281141).sum := by decide
  have hdescent : baseEnd_2281141 < baseStart_2281141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281156 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2281156 : Nat := 118140960795 + 2281156 * 2 ^ 59
def prefixEnd_2281156 : Nat := 4983230072969 + 3 ^ 40 * 2281156 * 2
def baseEnd_2281156 : Nat := 780886317258521466906107

theorem tailTrace_2281156 : CollatzResearch.WordTrace tailWord_2281156 prefixEnd_2281156 780886317258521466906107 := by
  unfold tailWord_2281156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41600297261884438636515661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55467063015845918182020881 41600297261884438636515661)
  ·
    refine ⟨15600111473206664488693373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41600297261884438636515661 15600111473206664488693373)
    ·
      refine ⟨5850041802452499183260015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15600111473206664488693373 5850041802452499183260015)
      ·
        refine ⟨8775062703678748774890023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850041802452499183260015 8775062703678748774890023)
        ·
          refine ⟨13162594055518123162335035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8775062703678748774890023 13162594055518123162335035)
          ·
            refine ⟨19743891083277184743502553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13162594055518123162335035 19743891083277184743502553)
            ·
              refine ⟨14807918312457888557626915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19743891083277184743502553 14807918312457888557626915)
              ·
                refine ⟨22211877468686832836440373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14807918312457888557626915 22211877468686832836440373)
                ·
                  refine ⟨2082363512689390578416285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22211877468686832836440373 2082363512689390578416285)
                  ·
                    refine ⟨780886317258521466906107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2082363512689390578416285 780886317258521466906107)
                    ·
                      rfl

theorem cell22_2281156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2281156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281156 prefixEnd_2281156 := by exact prefixLift 2281156
  have htrace : WordTrace (prefixWord ++ tailWord_2281156) baseStart_2281156 baseEnd_2281156 := by
    simpa [prefixWord, tailWord_2281156, baseEnd_2281156] using wordTrace_append hprefix tailTrace_2281156
  have hstable : (prefixWord ++ tailWord_2281156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281156).length < 2 ^ (prefixWord ++ tailWord_2281156).sum := by decide
  have hdescent : baseEnd_2281156 < baseStart_2281156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281158 : List Nat := [6, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2281158 : Nat := 118140960795 + 2281158 * 2 ^ 59
def prefixEnd_2281158 : Nat := 4983230072969 + 3 ^ 40 * 2281158 * 2
def baseEnd_2281158 : Nat := 86765222433266014261789

theorem tailTrace_2281158 : CollatzResearch.WordTrace tailWord_2281158 prefixEnd_2281158 86765222433266014261789 := by
  unfold tailWord_2281158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600020858430050987956379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55467111646507754409736085 2600020858430050987956379)
  ·
    refine ⟨3900031287645076481934569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600020858430050987956379 3900031287645076481934569)
    ·
      refine ⟨2925023465733807361450927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3900031287645076481934569 2925023465733807361450927)
      ·
        refine ⟨4387535198600711042176391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2925023465733807361450927 4387535198600711042176391)
        ·
          refine ⟨6581302797901066563264587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387535198600711042176391 6581302797901066563264587)
          ·
            refine ⟨9871954196851599844896881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581302797901066563264587 9871954196851599844896881)
            ·
              refine ⟨7403965647638699883672661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9871954196851599844896881 7403965647638699883672661)
              ·
                refine ⟨86765222433266014261789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7403965647638699883672661 86765222433266014261789)
                ·
                  rfl

theorem cell22_2281158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2281158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281158 prefixEnd_2281158 := by exact prefixLift 2281158
  have htrace : WordTrace (prefixWord ++ tailWord_2281158) baseStart_2281158 baseEnd_2281158 := by
    simpa [prefixWord, tailWord_2281158, baseEnd_2281158] using wordTrace_append hprefix tailTrace_2281158
  have hstable : (prefixWord ++ tailWord_2281158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281158).length < 2 ^ (prefixWord ++ tailWord_2281158).sum := by decide
  have hdescent : baseEnd_2281158 < baseStart_2281158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281199 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_2281199 : Nat := 118140960795 + 2281199 * 2 ^ 59
def prefixEnd_2281199 : Nat := 4983230072969 + 3 ^ 40 * 2281199 * 2
def baseEnd_2281199 : Nat := 780901037037283688080975

theorem tailTrace_2281199 : CollatzResearch.WordTrace tailWord_2281199 prefixEnd_2281199 780901037037283688080975 := by
  unfold tailWord_2281199
  simp only [CollatzResearch.WordTrace]
  refine ⟨83202162862613095616846651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55468108575075397077897767 83202162862613095616846651)
  ·
    refine ⟨124803244293919643425269977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83202162862613095616846651 124803244293919643425269977)
    ·
      refine ⟨93602433220439732568952483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124803244293919643425269977 93602433220439732568952483)
      ·
        refine ⟨140403649830659598853428725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93602433220439732568952483 140403649830659598853428725)
        ·
          refine ⟨13162842171624337392508943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140403649830659598853428725 13162842171624337392508943)
          ·
            refine ⟨19744263257436506088763415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13162842171624337392508943 19744263257436506088763415)
            ·
              refine ⟨29616394886154759133145123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19744263257436506088763415 29616394886154759133145123)
              ·
                refine ⟨44424592329232138699717685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29616394886154759133145123 44424592329232138699717685)
                ·
                  refine ⟨4164805530865513003098533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44424592329232138699717685 4164805530865513003098533)
                  ·
                    refine ⟨780901037037283688080975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164805530865513003098533 780901037037283688080975)
                    ·
                      rfl

theorem cell22_2281199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_2281199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281199 prefixEnd_2281199 := by exact prefixLift 2281199
  have htrace : WordTrace (prefixWord ++ tailWord_2281199) baseStart_2281199 baseEnd_2281199 := by
    simpa [prefixWord, tailWord_2281199, baseEnd_2281199] using wordTrace_append hprefix tailTrace_2281199
  have hstable : (prefixWord ++ tailWord_2281199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281199).length < 2 ^ (prefixWord ++ tailWord_2281199).sum := by decide
  have hdescent : baseEnd_2281199 < baseStart_2281199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281276 : List Nat := [2, 2, 2, 2, 1, 1, 6, 6]
def baseStart_2281276 : Nat := 118140960795 + 2281276 * 2 ^ 59
def prefixEnd_2281276 : Nat := 4983230072969 + 3 ^ 40 * 2281276 * 2
def baseEnd_2281276 : Nat := 86769710634542350433971

theorem tailTrace_2281276 : CollatzResearch.WordTrace tailWord_2281276 prefixEnd_2281276 86769710634542350433971 := by
  unfold tailWord_2281276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41602485641667068883699841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55469980855556091844933121 41602485641667068883699841)
  ·
    refine ⟨31201864231250301662774881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41602485641667068883699841 31201864231250301662774881)
    ·
      refine ⟨23401398173437726247081161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31201864231250301662774881 23401398173437726247081161)
      ·
        refine ⟨17551048630078294685310871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23401398173437726247081161 17551048630078294685310871)
        ·
          refine ⟨26326572945117442027966307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17551048630078294685310871 26326572945117442027966307)
          ·
            refine ⟨39489859417676163041949461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26326572945117442027966307 39489859417676163041949461)
            ·
              refine ⟨1851087160203570142591381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39489859417676163041949461 1851087160203570142591381)
              ·
                refine ⟨86769710634542350433971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1851087160203570142591381 86769710634542350433971)
                ·
                  rfl

theorem cell22_2281276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_2281276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281276 prefixEnd_2281276 := by exact prefixLift 2281276
  have htrace : WordTrace (prefixWord ++ tailWord_2281276) baseStart_2281276 baseEnd_2281276 := by
    simpa [prefixWord, tailWord_2281276, baseEnd_2281276] using wordTrace_append hprefix tailTrace_2281276
  have hstable : (prefixWord ++ tailWord_2281276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281276).length < 2 ^ (prefixWord ++ tailWord_2281276).sum := by decide
  have hdescent : baseEnd_2281276 < baseStart_2281276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281293 : List Nat := [1, 6, 1, 2, 1, 3, 8]
def baseStart_2281293 : Nat := 118140960795 + 2281293 * 2 ^ 59
def prefixEnd_2281293 : Nat := 4983230072969 + 3 ^ 40 * 2281293 * 2
def baseEnd_2281293 : Nat := 28923452413270325045581

theorem tailTrace_2281293 : CollatzResearch.WordTrace tailWord_2281293 prefixEnd_2281293 28923452413270325045581 := by
  unfold tailWord_2281293
  simp only [CollatzResearch.WordTrace]
  refine ⟨83205591324272549670768533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55470394216181699780512355 83205591324272549670768533)
  ·
    refine ⟨3900262093325275765817275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83205591324272549670768533 3900262093325275765817275)
    ·
      refine ⟨5850393139987913648725913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900262093325275765817275 5850393139987913648725913)
      ·
        refine ⟨4387794854990935236544435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850393139987913648725913 4387794854990935236544435)
        ·
          refine ⟨6581692282486402854816653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387794854990935236544435 6581692282486402854816653)
          ·
            refine ⟨2468134605932401070556245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6581692282486402854816653 2468134605932401070556245)
            ·
              refine ⟨28923452413270325045581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2468134605932401070556245 28923452413270325045581)
              ·
                rfl

theorem cell22_2281293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 8].length) (baseStart_2281293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281293 prefixEnd_2281293 := by exact prefixLift 2281293
  have htrace : WordTrace (prefixWord ++ tailWord_2281293) baseStart_2281293 baseEnd_2281293 := by
    simpa [prefixWord, tailWord_2281293, baseEnd_2281293] using wordTrace_append hprefix tailTrace_2281293
  have hstable : (prefixWord ++ tailWord_2281293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281293).length < 2 ^ (prefixWord ++ tailWord_2281293).sum := by decide
  have hdescent : baseEnd_2281293 < baseStart_2281293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281383 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 6]
def baseStart_2281383 : Nat := 118140960795 + 2281383 * 2 ^ 59
def prefixEnd_2281383 : Nat := 4983230072969 + 3 ^ 40 * 2281383 * 2
def baseEnd_2281383 : Nat := 260321341332522847160137

theorem tailTrace_2281383 : CollatzResearch.WordTrace tailWord_2281383 prefixEnd_2281383 260321341332522847160137 := by
  unfold tailWord_2281383
  simp only [CollatzResearch.WordTrace]
  refine ⟨83208873893946495041544803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55472582595964330027696535 83208873893946495041544803)
  ·
    refine ⟨124813310840919742562317205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83208873893946495041544803 124813310840919742562317205)
    ·
      refine ⟨5850623945668112932608619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124813310840919742562317205 5850623945668112932608619)
      ·
        refine ⟨8775935918502169398912929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850623945668112932608619 8775935918502169398912929)
        ·
          refine ⟨6581951938876627049184697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8775935918502169398912929 6581951938876627049184697)
          ·
            refine ⟨4936463954157470286888523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6581951938876627049184697 4936463954157470286888523)
            ·
              refine ⟨7404695931236205430332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4936463954157470286888523 7404695931236205430332785)
              ·
                refine ⟨5553521948427154072749589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7404695931236205430332785 5553521948427154072749589)
                ·
                  refine ⟨260321341332522847160137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5553521948427154072749589 260321341332522847160137)
                  ·
                    rfl

theorem cell22_2281383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_2281383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281383 prefixEnd_2281383 := by exact prefixLift 2281383
  have htrace : WordTrace (prefixWord ++ tailWord_2281383) baseStart_2281383 baseEnd_2281383 := by
    simpa [prefixWord, tailWord_2281383, baseEnd_2281383] using wordTrace_append hprefix tailTrace_2281383
  have hstable : (prefixWord ++ tailWord_2281383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281383).length < 2 ^ (prefixWord ++ tailWord_2281383).sum := by decide
  have hdescent : baseEnd_2281383 < baseStart_2281383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281441 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2281441 : Nat := 118140960795 + 2281441 * 2 ^ 59
def prefixEnd_2281441 : Nat := 4983230072969 + 3 ^ 40 * 2281441 * 2
def baseEnd_2281441 : Nat := 780983878582875723530233

theorem tailTrace_2281441 : CollatzResearch.WordTrace tailWord_2281441 prefixEnd_2281441 780983878582875723530233 := by
  unfold tailWord_2281441
  simp only [CollatzResearch.WordTrace]
  refine ⟨83210989327736370947156177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55473992885157580631437451 83210989327736370947156177)
  ·
    refine ⟨62408241995802278210367133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83210989327736370947156177 62408241995802278210367133)
    ·
      refine ⟨23403090748425854328887675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62408241995802278210367133 23403090748425854328887675)
      ·
        refine ⟨35104636122638781493331513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23403090748425854328887675 35104636122638781493331513)
        ·
          refine ⟨26328477091979086119998635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35104636122638781493331513 26328477091979086119998635)
          ·
            refine ⟨39492715637968629179997953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26328477091979086119998635 39492715637968629179997953)
            ·
              refine ⟨29619536728476471884998465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39492715637968629179997953 29619536728476471884998465)
              ·
                refine ⟨22214652546357353913748849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29619536728476471884998465 22214652546357353913748849)
                ·
                  refine ⟨16660989409768015435311637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22214652546357353913748849 16660989409768015435311637)
                  ·
                    refine ⟨780983878582875723530233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16660989409768015435311637 780983878582875723530233)
                    ·
                      rfl

theorem cell22_2281441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2281441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281441 prefixEnd_2281441 := by exact prefixLift 2281441
  have htrace : WordTrace (prefixWord ++ tailWord_2281441) baseStart_2281441 baseEnd_2281441 := by
    simpa [prefixWord, tailWord_2281441, baseEnd_2281441] using wordTrace_append hprefix tailTrace_2281441
  have hstable : (prefixWord ++ tailWord_2281441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281441).length < 2 ^ (prefixWord ++ tailWord_2281441).sum := by decide
  have hdescent : baseEnd_2281441 < baseStart_2281441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281456 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_2281456 : Nat := 118140960795 + 2281456 * 2 ^ 59
def prefixEnd_2281456 : Nat := 4983230072969 + 3 ^ 40 * 2281456 * 2
def baseEnd_2281456 : Nat := 260329671129806894801729

theorem tailTrace_2281456 : CollatzResearch.WordTrace tailWord_2281456 prefixEnd_2281456 260329671129806894801729 := by
  unfold tailWord_2281456
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605768211341014254476111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55474357615121352339301481 41605768211341014254476111)
  ·
    refine ⟨62408652317011521381714167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41605768211341014254476111 62408652317011521381714167)
    ·
      refine ⟨93612978475517282072571251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62408652317011521381714167 93612978475517282072571251)
      ·
        refine ⟨140419467713275923108856877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93612978475517282072571251 140419467713275923108856877)
        ·
          refine ⟨52657300392478471165821329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140419467713275923108856877 52657300392478471165821329)
          ·
            refine ⟨39492975294358853374365997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52657300392478471165821329 39492975294358853374365997)
            ·
              refine ⟨14809865735384570015387249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39492975294358853374365997 14809865735384570015387249)
              ·
                refine ⟨11107399301538427511540437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14809865735384570015387249 11107399301538427511540437)
                ·
                  refine ⟨260329671129806894801729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11107399301538427511540437 260329671129806894801729)
                  ·
                    rfl

theorem cell22_2281456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_2281456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281456 prefixEnd_2281456 := by exact prefixLift 2281456
  have htrace : WordTrace (prefixWord ++ tailWord_2281456) baseStart_2281456 baseEnd_2281456 := by
    simpa [prefixWord, tailWord_2281456, baseEnd_2281456] using wordTrace_append hprefix tailTrace_2281456
  have hstable : (prefixWord ++ tailWord_2281456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281456).length < 2 ^ (prefixWord ++ tailWord_2281456).sum := by decide
  have hdescent : baseEnd_2281456 < baseStart_2281456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281471 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_2281471 : Nat := 118140960795 + 2281471 * 2 ^ 59
def prefixEnd_2281471 : Nat := 4983230072969 + 3 ^ 40 * 2281471 * 2
def baseEnd_2281471 : Nat := 780994148195965645280141

theorem tailTrace_2281471 : CollatzResearch.WordTrace tailWord_2281471 prefixEnd_2281471 780994148195965645280141 := by
  unfold tailWord_2281471
  simp only [CollatzResearch.WordTrace]
  refine ⟨83212083517627686070748267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55474722345085124047165511 83212083517627686070748267)
  ·
    refine ⟨124818125276441529106122401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83212083517627686070748267 124818125276441529106122401)
    ·
      refine ⟨93613593957331146829591801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124818125276441529106122401 93613593957331146829591801)
      ·
        refine ⟨70210195467998360122193851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93613593957331146829591801 70210195467998360122193851)
        ·
          refine ⟨105315293201997540183290777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70210195467998360122193851 105315293201997540183290777)
          ·
            refine ⟨78986469901498155137468083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105315293201997540183290777 78986469901498155137468083)
            ·
              refine ⟨118479704852247232706202125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78986469901498155137468083 118479704852247232706202125)
              ·
                refine ⟨44429889319592712264825797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118479704852247232706202125 44429889319592712264825797)
                ·
                  refine ⟨8330604247423633549654837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44429889319592712264825797 8330604247423633549654837)
                  ·
                    refine ⟨780994148195965645280141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330604247423633549654837 780994148195965645280141)
                    ·
                      rfl

theorem cell22_2281471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_2281471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281471 prefixEnd_2281471 := by exact prefixLift 2281471
  have htrace : WordTrace (prefixWord ++ tailWord_2281471) baseStart_2281471 baseEnd_2281471 := by
    simpa [prefixWord, tailWord_2281471, baseEnd_2281471] using wordTrace_append hprefix tailTrace_2281471
  have hstable : (prefixWord ++ tailWord_2281471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281471).length < 2 ^ (prefixWord ++ tailWord_2281471).sum := by decide
  have hdescent : baseEnd_2281471 < baseStart_2281471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281473 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 5]
def baseStart_2281473 : Nat := 118140960795 + 2281473 * 2 ^ 59
def prefixEnd_2281473 : Nat := 4983230072969 + 3 ^ 40 * 2281473 * 2
def baseEnd_2281473 : Nat := 260331610945612768910045

theorem tailTrace_2281473 : CollatzResearch.WordTrace tailWord_2281473 prefixEnd_2281473 260331610945612768910045 := by
  unfold tailWord_2281473
  simp only [CollatzResearch.WordTrace]
  refine ⟨83212156463620440412321073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55474770975746960274880715 83212156463620440412321073)
  ·
    refine ⟨62409117347715330309240805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83212156463620440412321073 62409117347715330309240805)
    ·
      refine ⟨11701709502696624432982651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62409117347715330309240805 11701709502696624432982651)
      ·
        refine ⟨17552564254044936649473977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11701709502696624432982651 17552564254044936649473977)
        ·
          refine ⟨13164423190533702487105483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17552564254044936649473977 13164423190533702487105483)
          ·
            refine ⟨19746634785800553730658225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13164423190533702487105483 19746634785800553730658225)
            ·
              refine ⟨14809976089350415297993669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19746634785800553730658225 14809976089350415297993669)
              ·
                refine ⟨2776870516753202868373813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14809976089350415297993669 2776870516753202868373813)
                ·
                  refine ⟨260331610945612768910045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776870516753202868373813 260331610945612768910045)
                  ·
                    rfl

theorem cell22_2281473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_2281473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281473 prefixEnd_2281473 := by exact prefixLift 2281473
  have htrace : WordTrace (prefixWord ++ tailWord_2281473) baseStart_2281473 baseEnd_2281473 := by
    simpa [prefixWord, tailWord_2281473, baseEnd_2281473] using wordTrace_append hprefix tailTrace_2281473
  have hstable : (prefixWord ++ tailWord_2281473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281473).length < 2 ^ (prefixWord ++ tailWord_2281473).sum := by decide
  have hdescent : baseEnd_2281473 < baseStart_2281473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281503 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_2281503 : Nat := 118140960795 + 2281503 * 2 ^ 59
def prefixEnd_2281503 : Nat := 4983230072969 + 3 ^ 40 * 2281503 * 2
def baseEnd_2281503 : Nat := 781005102449928228480043

theorem tailTrace_2281503 : CollatzResearch.WordTrace tailWord_2281503 prefixEnd_2281503 781005102449928228480043 := by
  unfold tailWord_2281503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83213250653511755535913163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55475500435674503690608775 83213250653511755535913163)
  ·
    refine ⟨124819875980267633303869745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83213250653511755535913163 124819875980267633303869745)
    ·
      refine ⟨93614906985200724977902309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124819875980267633303869745 93614906985200724977902309)
      ·
        refine ⟨17552795059725135933356683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93614906985200724977902309 17552795059725135933356683)
        ·
          refine ⟨26329192589587703900035025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17552795059725135933356683 26329192589587703900035025)
          ·
            refine ⟨19746894442190777925026269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26329192589587703900035025 19746894442190777925026269)
            ·
              refine ⟨7405085415821541721884851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19746894442190777925026269 7405085415821541721884851)
              ·
                refine ⟨11107628123732312582827277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405085415821541721884851 11107628123732312582827277)
                ·
                  refine ⟨4165360546399617218560229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11107628123732312582827277 4165360546399617218560229)
                  ·
                    refine ⟨781005102449928228480043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165360546399617218560229 781005102449928228480043)
                    ·
                      rfl

theorem cell22_2281503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_2281503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281503 prefixEnd_2281503 := by exact prefixLift 2281503
  have htrace : WordTrace (prefixWord ++ tailWord_2281503) baseStart_2281503 baseEnd_2281503 := by
    simpa [prefixWord, tailWord_2281503, baseEnd_2281503] using wordTrace_append hprefix tailTrace_2281503
  have hstable : (prefixWord ++ tailWord_2281503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281503).length < 2 ^ (prefixWord ++ tailWord_2281503).sum := by decide
  have hdescent : baseEnd_2281503 < baseStart_2281503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281533 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2281533 : Nat := 118140960795 + 2281533 * 2 ^ 59
def prefixEnd_2281533 : Nat := 4983230072969 + 3 ^ 40 * 2281533 * 2
def baseEnd_2281533 : Nat := 781015372063018150229951

theorem tailTrace_2281533 : CollatzResearch.WordTrace tailWord_2281533 prefixEnd_2281533 781015372063018150229951 := by
  unfold tailWord_2281533
  simp only [CollatzResearch.WordTrace]
  refine ⟨83214344843403070659505253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55476229895602047106336835 83214344843403070659505253)
  ·
    refine ⟨15602689658138075748657235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83214344843403070659505253 15602689658138075748657235)
    ·
      refine ⟨23404034487207113622985853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602689658138075748657235 23404034487207113622985853)
      ·
        refine ⟨8776512932702667608619695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23404034487207113622985853 8776512932702667608619695)
        ·
          refine ⟨13164769399054001412929543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776512932702667608619695 13164769399054001412929543)
          ·
            refine ⟨19747154098581002119394315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13164769399054001412929543 19747154098581002119394315)
            ·
              refine ⟨29620731147871503179091473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19747154098581002119394315 29620731147871503179091473)
              ·
                refine ⟨22215548360903627384318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29620731147871503179091473 22215548360903627384318605)
                ·
                  refine ⟨8330830635338860269119477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22215548360903627384318605 8330830635338860269119477)
                  ·
                    refine ⟨781015372063018150229951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330830635338860269119477 781015372063018150229951)
                    ·
                      rfl

theorem cell22_2281533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2281533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281533 prefixEnd_2281533 := by exact prefixLift 2281533
  have htrace : WordTrace (prefixWord ++ tailWord_2281533) baseStart_2281533 baseEnd_2281533 := by
    simpa [prefixWord, tailWord_2281533, baseEnd_2281533] using wordTrace_append hprefix tailTrace_2281533
  have hstable : (prefixWord ++ tailWord_2281533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281533).length < 2 ^ (prefixWord ++ tailWord_2281533).sum := by decide
  have hdescent : baseEnd_2281533 < baseStart_2281533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281548 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_2281548 : Nat := 118140960795 + 2281548 * 2 ^ 59
def prefixEnd_2281548 : Nat := 4983230072969 + 3 ^ 40 * 2281548 * 2
def baseEnd_2281548 : Nat := 781020506869563111104905

theorem tailTrace_2281548 : CollatzResearch.WordTrace tailWord_2281548 prefixEnd_2281548 781020506869563111104905 := by
  unfold tailWord_2281548
  simp only [CollatzResearch.WordTrace]
  refine ⟨41607445969174364110650649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55476594625565818814200865 41607445969174364110650649)
  ·
    refine ⟨31205584476880773082987987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41607445969174364110650649 31205584476880773082987987)
    ·
      refine ⟨46808376715321159624481981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31205584476880773082987987 46808376715321159624481981)
      ·
        refine ⟨17553141268245434859180743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46808376715321159624481981 17553141268245434859180743)
        ·
          refine ⟨26329711902368152288771115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17553141268245434859180743 26329711902368152288771115)
          ·
            refine ⟨39494567853552228433156673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26329711902368152288771115 39494567853552228433156673)
            ·
              refine ⟨29620925890164171324867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39494567853552228433156673 29620925890164171324867505)
              ·
                refine ⟨22215694417623128493650629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29620925890164171324867505 22215694417623128493650629)
                ·
                  refine ⟨4165442703304336592559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22215694417623128493650629 4165442703304336592559493)
                  ·
                    refine ⟨781020506869563111104905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165442703304336592559493 781020506869563111104905)
                    ·
                      rfl

theorem cell22_2281548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_2281548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281548 prefixEnd_2281548 := by exact prefixLift 2281548
  have htrace : WordTrace (prefixWord ++ tailWord_2281548) baseStart_2281548 baseEnd_2281548 := by
    simpa [prefixWord, tailWord_2281548, baseEnd_2281548] using wordTrace_append hprefix tailTrace_2281548
  have hstable : (prefixWord ++ tailWord_2281548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281548).length < 2 ^ (prefixWord ++ tailWord_2281548).sum := by decide
  have hdescent : baseEnd_2281548 < baseStart_2281548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281550 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2281550 : Nat := 118140960795 + 2281550 * 2 ^ 59
def prefixEnd_2281550 : Nat := 4983230072969 + 3 ^ 40 * 2281550 * 2
def baseEnd_2281550 : Nat := 781021191510435772554899

theorem tailTrace_2281550 : CollatzResearch.WordTrace tailWord_2281550 prefixEnd_2281550 781021191510435772554899 := by
  unfold tailWord_2281550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401870610542685320359263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55476643256227655041916069 10401870610542685320359263)
  ·
    refine ⟨15602805915814027980538895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10401870610542685320359263 15602805915814027980538895)
    ·
      refine ⟨23404208873721041970808343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602805915814027980538895 23404208873721041970808343)
      ·
        refine ⟨35106313310581562956212515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23404208873721041970808343 35106313310581562956212515)
        ·
          refine ⟨52659469965872344434318773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35106313310581562956212515 52659469965872344434318773)
          ·
            refine ⟨4936825309300532290717385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52659469965872344434318773 4936825309300532290717385)
            ·
              refine ⟨3702618981975399218038039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4936825309300532290717385 3702618981975399218038039)
              ·
                refine ⟨5553928472963098827057059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702618981975399218038039 5553928472963098827057059)
                ·
                  refine ⟨8330892709444648240585589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5553928472963098827057059 8330892709444648240585589)
                  ·
                    refine ⟨781021191510435772554899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330892709444648240585589 781021191510435772554899)
                    ·
                      rfl

theorem cell22_2281550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2281550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281550 prefixEnd_2281550 := by exact prefixLift 2281550
  have htrace : WordTrace (prefixWord ++ tailWord_2281550) baseStart_2281550 baseEnd_2281550 := by
    simpa [prefixWord, tailWord_2281550, baseEnd_2281550] using wordTrace_append hprefix tailTrace_2281550
  have hstable : (prefixWord ++ tailWord_2281550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281550).length < 2 ^ (prefixWord ++ tailWord_2281550).sum := by decide
  have hdescent : baseEnd_2281550 < baseStart_2281550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281614 : List Nat := [4, 1, 1, 3, 4, 1, 2, 6]
def baseStart_2281614 : Nat := 118140960795 + 2281614 * 2 ^ 59
def prefixEnd_2281614 : Nat := 4983230072969 + 3 ^ 40 * 2281614 * 2
def baseEnd_2281614 : Nat := 86782566668706770994967

theorem tailTrace_2281614 : CollatzResearch.WordTrace tailWord_2281614 prefixEnd_2281614 86782566668706770994967 := by
  unfold tailWord_2281614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10402162394513702686650487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55478199437406414328802597 10402162394513702686650487)
  ·
    refine ⟨15603243591770554029975731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10402162394513702686650487 15603243591770554029975731)
    ·
      refine ⟨23404865387655831044963597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15603243591770554029975731 23404865387655831044963597)
      ·
        refine ⟨8776824520370936641861349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23404865387655831044963597 8776824520370936641861349)
        ·
          refine ⟨1645654597569550620349003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8776824520370936641861349 1645654597569550620349003)
          ·
            refine ⟨2468481896354325930523505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645654597569550620349003 2468481896354325930523505)
            ·
              refine ⟨1851361422265744447892629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468481896354325930523505 1851361422265744447892629)
              ·
                refine ⟨86782566668706770994967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1851361422265744447892629 86782566668706770994967)
                ·
                  rfl

theorem cell22_2281614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_2281614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281614 prefixEnd_2281614 := by exact prefixLift 2281614
  have htrace : WordTrace (prefixWord ++ tailWord_2281614) baseStart_2281614 baseEnd_2281614 := by
    simpa [prefixWord, tailWord_2281614, baseEnd_2281614] using wordTrace_append hprefix tailTrace_2281614
  have hstable : (prefixWord ++ tailWord_2281614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281614).length < 2 ^ (prefixWord ++ tailWord_2281614).sum := by decide
  have hdescent : baseEnd_2281614 < baseStart_2281614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281629 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2281629 : Nat := 118140960795 + 2281629 * 2 ^ 59
def prefixEnd_2281629 : Nat := 4983230072969 + 3 ^ 40 * 2281629 * 2
def baseEnd_2281629 : Nat := 781048234824905899829657

theorem tailTrace_2281629 : CollatzResearch.WordTrace tailWord_2281629 prefixEnd_2281629 781048234824905899829657 := by
  unfold tailWord_2281629
  simp only [CollatzResearch.WordTrace]
  refine ⟨83217846251055279054999941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55478564167370186036666627 83217846251055279054999941)
  ·
    refine ⟨15603346172072864822812489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83217846251055279054999941 15603346172072864822812489)
    ·
      refine ⟨11702509629054648617109367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15603346172072864822812489 11702509629054648617109367)
      ·
        refine ⟨17553764443581972925664051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702509629054648617109367 17553764443581972925664051)
        ·
          refine ⟨26330646665372959388496077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17553764443581972925664051 26330646665372959388496077)
          ·
            refine ⟨9873992499514859770686029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26330646665372959388496077 9873992499514859770686029)
            ·
              refine ⟨3702747187318072414007261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9873992499514859770686029 3702747187318072414007261)
              ·
                refine ⟨1388530195244277155252723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3702747187318072414007261 1388530195244277155252723)
                ·
                  refine ⟨2082795292866415732879085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388530195244277155252723 2082795292866415732879085)
                  ·
                    refine ⟨781048234824905899829657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2082795292866415732879085 781048234824905899829657)
                    ·
                      rfl

theorem cell22_2281629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2281629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281629 prefixEnd_2281629 := by exact prefixLift 2281629
  have htrace : WordTrace (prefixWord ++ tailWord_2281629) baseStart_2281629 baseEnd_2281629 := by
    simpa [prefixWord, tailWord_2281629, baseEnd_2281629] using wordTrace_append hprefix tailTrace_2281629
  have hstable : (prefixWord ++ tailWord_2281629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281629).length < 2 ^ (prefixWord ++ tailWord_2281629).sum := by decide
  have hdescent : baseEnd_2281629 < baseStart_2281629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281652 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2281652 : Nat := 118140960795 + 2281652 * 2 ^ 59
def prefixEnd_2281652 : Nat := 4983230072969 + 3 ^ 40 * 2281652 * 2
def baseEnd_2281652 : Nat := 781056108194941506504587

theorem tailTrace_2281652 : CollatzResearch.WordTrace tailWord_2281652 prefixEnd_2281652 781056108194941506504587 := by
  unfold tailWord_2281652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41609342564985976991543605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55479123419981302655391473 41609342564985976991543605)
  ·
    refine ⟨3900875865467435342957213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41609342564985976991543605 3900875865467435342957213)
    ·
      refine ⟨1462828449550288253608955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3900875865467435342957213 1462828449550288253608955)
      ·
        refine ⟨2194242674325432380413433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462828449550288253608955 2194242674325432380413433)
        ·
          refine ⟨1645682005744074285310075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2194242674325432380413433 1645682005744074285310075)
          ·
            refine ⟨2468523008616111427965113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645682005744074285310075 2468523008616111427965113)
            ·
              refine ⟨1851392256462083570973835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468523008616111427965113 1851392256462083570973835)
              ·
                refine ⟨2777088384693125356460753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851392256462083570973835 2777088384693125356460753)
                ·
                  refine ⟨2082816288519844017345565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777088384693125356460753 2082816288519844017345565)
                  ·
                    refine ⟨781056108194941506504587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2082816288519844017345565 781056108194941506504587)
                    ·
                      rfl

theorem cell22_2281652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2281652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281652 prefixEnd_2281652 := by exact prefixLift 2281652
  have htrace : WordTrace (prefixWord ++ tailWord_2281652) baseStart_2281652 baseEnd_2281652 := by
    simpa [prefixWord, tailWord_2281652, baseEnd_2281652] using wordTrace_append hprefix tailTrace_2281652
  have hstable : (prefixWord ++ tailWord_2281652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281652).length < 2 ^ (prefixWord ++ tailWord_2281652).sum := by decide
  have hdescent : baseEnd_2281652 < baseStart_2281652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281704 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_2281704 : Nat := 118140960795 + 2281704 * 2 ^ 59
def prefixEnd_2281704 : Nat := 4983230072969 + 3 ^ 40 * 2281704 * 2
def baseEnd_2281704 : Nat := 260357969619210234734809

theorem tailTrace_2281704 : CollatzResearch.WordTrace tailWord_2281704 prefixEnd_2281704 260357969619210234734809 := by
  unfold tailWord_2281704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41610290862891783431990083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55480387817189044575986777 41610290862891783431990083)
  ·
    refine ⟨62415436294337675147985125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41610290862891783431990083 62415436294337675147985125)
    ·
      refine ⟨11702894305188314090247211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62415436294337675147985125 11702894305188314090247211)
      ·
        refine ⟨17554341457782471135370817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702894305188314090247211 17554341457782471135370817)
        ·
          refine ⟨13165756093336853351528113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17554341457782471135370817 13165756093336853351528113)
          ·
            refine ⟨9874317070002640013646085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13165756093336853351528113 9874317070002640013646085)
            ·
              refine ⟨1851434450625495002558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9874317070002640013646085 1851434450625495002558641)
              ·
                refine ⟨1388575837969121251918981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851434450625495002558641 1388575837969121251918981)
                ·
                  refine ⟨260357969619210234734809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388575837969121251918981 260357969619210234734809)
                  ·
                    rfl

theorem cell22_2281704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_2281704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281704 prefixEnd_2281704 := by exact prefixLift 2281704
  have htrace : WordTrace (prefixWord ++ tailWord_2281704) baseStart_2281704 baseEnd_2281704 := by
    simpa [prefixWord, tailWord_2281704, baseEnd_2281704] using wordTrace_append hprefix tailTrace_2281704
  have hstable : (prefixWord ++ tailWord_2281704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281704).length < 2 ^ (prefixWord ++ tailWord_2281704).sum := by decide
  have hdescent : baseEnd_2281704 < baseStart_2281704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281764 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2281764 : Nat := 118140960795 + 2281764 * 2 ^ 59
def prefixEnd_2281764 : Nat := 4983230072969 + 3 ^ 40 * 2281764 * 2
def baseEnd_2281764 : Nat := 781094448083810547704243

theorem tailTrace_2281764 : CollatzResearch.WordTrace tailWord_2281764 prefixEnd_2281764 781094448083810547704243 := by
  unfold tailWord_2281764
  simp only [CollatzResearch.WordTrace]
  refine ⟨41611385052783098555582173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55481846737044131407442897 41611385052783098555582173)
  ·
    refine ⟨15604269394793661958343315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41611385052783098555582173 15604269394793661958343315)
    ·
      refine ⟨23406404092190492937514973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15604269394793661958343315 23406404092190492937514973)
      ·
        refine ⟨8777401534571434851568115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23406404092190492937514973 8777401534571434851568115)
        ·
          refine ⟨13166102301857152277352173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8777401534571434851568115 13166102301857152277352173)
          ·
            refine ⟨4937288363196432104007065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13166102301857152277352173 4937288363196432104007065)
            ·
              refine ⟨3702966272397324078005299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937288363196432104007065 3702966272397324078005299)
              ·
                refine ⟨5554449408595986117007949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702966272397324078005299 5554449408595986117007949)
                ·
                  refine ⟨2082918528223494793877981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5554449408595986117007949 2082918528223494793877981)
                  ·
                    refine ⟨781094448083810547704243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2082918528223494793877981 781094448083810547704243)
                    ·
                      rfl

theorem cell22_2281764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2281764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281764 prefixEnd_2281764 := by exact prefixLift 2281764
  have htrace : WordTrace (prefixWord ++ tailWord_2281764) baseStart_2281764 baseEnd_2281764 := by
    simpa [prefixWord, tailWord_2281764, baseEnd_2281764] using wordTrace_append hprefix tailTrace_2281764
  have hstable : (prefixWord ++ tailWord_2281764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281764).length < 2 ^ (prefixWord ++ tailWord_2281764).sum := by decide
  have hdescent : baseEnd_2281764 < baseStart_2281764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281775 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_2281775 : Nat := 118140960795 + 2281775 * 2 ^ 59
def prefixEnd_2281775 : Nat := 4983230072969 + 3 ^ 40 * 2281775 * 2
def baseEnd_2281775 : Nat := 781098213608610185679209

theorem tailTrace_2281775 : CollatzResearch.WordTrace tailWord_2281775 prefixEnd_2281775 781098213608610185679209 := by
  unfold tailWord_2281775
  simp only [CollatzResearch.WordTrace]
  refine ⟨83223171308526345989814779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55482114205684230659876519 83223171308526345989814779)
  ·
    refine ⟨124834756962789518984722169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83223171308526345989814779 124834756962789518984722169)
    ·
      refine ⟨93626067722092139238541627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124834756962789518984722169 93626067722092139238541627)
      ·
        refine ⟨140439101583138208857812441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93626067722092139238541627 140439101583138208857812441)
        ·
          refine ⟨105329326187353656643359331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140439101583138208857812441 105329326187353656643359331)
          ·
            refine ⟨157993989281030484965038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105329326187353656643359331 157993989281030484965038997)
            ·
              refine ⟨7405968247548303982736203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157993989281030484965038997 7405968247548303982736203)
              ·
                refine ⟨11108952371322455974104305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405968247548303982736203 11108952371322455974104305)
                ·
                  refine ⟨8331714278491841980578229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11108952371322455974104305 8331714278491841980578229)
                  ·
                    refine ⟨781098213608610185679209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8331714278491841980578229 781098213608610185679209)
                    ·
                      rfl

theorem cell22_2281775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_2281775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281775 prefixEnd_2281775 := by exact prefixLift 2281775
  have htrace : WordTrace (prefixWord ++ tailWord_2281775) baseStart_2281775 baseEnd_2281775 := by
    simpa [prefixWord, tailWord_2281775, baseEnd_2281775] using wordTrace_append hprefix tailTrace_2281775
  have hstable : (prefixWord ++ tailWord_2281775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281775).length < 2 ^ (prefixWord ++ tailWord_2281775).sum := by decide
  have hdescent : baseEnd_2281775 < baseStart_2281775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281837 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2281837 : Nat := 118140960795 + 2281837 * 2 ^ 59
def prefixEnd_2281837 : Nat := 4983230072969 + 3 ^ 40 * 2281837 * 2
def baseEnd_2281837 : Nat := 781119437475662690629019

theorem tailTrace_2281837 : CollatzResearch.WordTrace tailWord_2281837 prefixEnd_2281837 781119437475662690629019 := by
  unfold tailWord_2281837
  simp only [CollatzResearch.WordTrace]
  refine ⟨83225432634301730578571765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55483621756201153719047843 83225432634301730578571765)
  ·
    refine ⟨7802384309465787241741103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83225432634301730578571765 7802384309465787241741103)
    ·
      refine ⟨11703576464198680862611655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802384309465787241741103 11703576464198680862611655)
      ·
        refine ⟨17555364696298021293917483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703576464198680862611655 17555364696298021293917483)
        ·
          refine ⟨26333047044447031940876225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17555364696298021293917483 26333047044447031940876225)
          ·
            refine ⟨19749785283335273955657169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26333047044447031940876225 19749785283335273955657169)
            ·
              refine ⟨14812338962501455466742877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19749785283335273955657169 14812338962501455466742877)
              ·
                refine ⟨5554627110938045800028579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14812338962501455466742877 5554627110938045800028579)
                ·
                  refine ⟨8331940666407068700042869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554627110938045800028579 8331940666407068700042869)
                  ·
                    refine ⟨781119437475662690629019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8331940666407068700042869 781119437475662690629019)
                    ·
                      rfl

theorem cell22_2281837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2281837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281837 prefixEnd_2281837 := by exact prefixLift 2281837
  have htrace : WordTrace (prefixWord ++ tailWord_2281837) baseStart_2281837 baseEnd_2281837 := by
    simpa [prefixWord, tailWord_2281837, baseEnd_2281837] using wordTrace_append hprefix tailTrace_2281837
  have hstable : (prefixWord ++ tailWord_2281837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281837).length < 2 ^ (prefixWord ++ tailWord_2281837).sum := by decide
  have hdescent : baseEnd_2281837 < baseStart_2281837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281901 : List Nat := [1, 5, 2, 2, 2, 1, 3, 6]
def baseStart_2281901 : Nat := 118140960795 + 2281901 * 2 ^ 59
def prefixEnd_2281901 : Nat := 4983230072969 + 3 ^ 40 * 2281901 * 2
def baseEnd_2281901 : Nat := 86793482887065317447647

theorem tailTrace_2281901 : CollatzResearch.WordTrace tailWord_2281901 prefixEnd_2281901 86793482887065317447647 := by
  unfold tailWord_2281901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83227766906069869508901557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55485177937379913005934371 83227766906069869508901557)
  ·
    refine ⟨7802603147444050266459521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83227766906069869508901557 7802603147444050266459521)
    ·
      refine ⟨5851952360583037699844641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7802603147444050266459521 5851952360583037699844641)
      ·
        refine ⟨4388964270437278274883481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5851952360583037699844641 4388964270437278274883481)
        ·
          refine ⟨3291723202827958706162611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388964270437278274883481 3291723202827958706162611)
          ·
            refine ⟨4937584804241938059243917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291723202827958706162611 4937584804241938059243917)
            ·
              refine ⟨1851594301590726772216469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4937584804241938059243917 1851594301590726772216469)
              ·
                refine ⟨86793482887065317447647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1851594301590726772216469 86793482887065317447647)
                ·
                  rfl

theorem cell22_2281901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 6].length) (baseStart_2281901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281901 prefixEnd_2281901 := by exact prefixLift 2281901
  have htrace : WordTrace (prefixWord ++ tailWord_2281901) baseStart_2281901 baseEnd_2281901 := by
    simpa [prefixWord, tailWord_2281901, baseEnd_2281901] using wordTrace_append hprefix tailTrace_2281901
  have hstable : (prefixWord ++ tailWord_2281901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281901).length < 2 ^ (prefixWord ++ tailWord_2281901).sum := by decide
  have hdescent : baseEnd_2281901 < baseStart_2281901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281927 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2281927 : Nat := 118140960795 + 2281927 * 2 ^ 59
def prefixEnd_2281927 : Nat := 4983230072969 + 3 ^ 40 * 2281927 * 2
def baseEnd_2281927 : Nat := 781150246314932455878743

theorem tailTrace_2281927 : CollatzResearch.WordTrace tailWord_2281927 prefixEnd_2281927 781150246314932455878743 := by
  unfold tailWord_2281927
  simp only [CollatzResearch.WordTrace]
  refine ⟨83228715203975675949348035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55485810135983783966232023 83228715203975675949348035)
  ·
    refine ⟨124843072805963513924022053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83228715203975675949348035 124843072805963513924022053)
    ·
      refine ⟨23408076151118158860754135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124843072805963513924022053 23408076151118158860754135)
      ·
        refine ⟨35112114226677238291131203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23408076151118158860754135 35112114226677238291131203)
        ·
          refine ⟨52668171340015857436696805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35112114226677238291131203 52668171340015857436696805)
          ·
            refine ⟨9875282126252973269380651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52668171340015857436696805 9875282126252973269380651)
            ·
              refine ⟨14812923189379459904070977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875282126252973269380651 14812923189379459904070977)
              ·
                refine ⟨11109692392034594928053233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14812923189379459904070977 11109692392034594928053233)
                ·
                  refine ⟨8332269294025946196039925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11109692392034594928053233 8332269294025946196039925)
                  ·
                    refine ⟨781150246314932455878743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8332269294025946196039925 781150246314932455878743)
                    ·
                      rfl

theorem cell22_2281927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2281927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281927 prefixEnd_2281927 := by exact prefixLift 2281927
  have htrace : WordTrace (prefixWord ++ tailWord_2281927) baseStart_2281927 baseEnd_2281927 := by
    simpa [prefixWord, tailWord_2281927, baseEnd_2281927] using wordTrace_append hprefix tailTrace_2281927
  have hstable : (prefixWord ++ tailWord_2281927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281927).length < 2 ^ (prefixWord ++ tailWord_2281927).sum := by decide
  have hdescent : baseEnd_2281927 < baseStart_2281927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281989 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_2281989 : Nat := 118140960795 + 2281989 * 2 ^ 59
def prefixEnd_2281989 : Nat := 4983230072969 + 3 ^ 40 * 2281989 * 2
def baseEnd_2281989 : Nat := 781171470181984960828553

theorem tailTrace_2281989 : CollatzResearch.WordTrace tailWord_2281989 prefixEnd_2281989 781171470181984960828553 := by
  unfold tailWord_2281989
  simp only [CollatzResearch.WordTrace]
  refine ⟨83230976529751060538105021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55487317686500707025403347 83230976529751060538105021)
  ·
    refine ⟨31211616198656647701789383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83230976529751060538105021 31211616198656647701789383)
    ·
      refine ⟨46817424297984971552684075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31211616198656647701789383 46817424297984971552684075)
      ·
        refine ⟨70226136446977457329026113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46817424297984971552684075 70226136446977457329026113)
        ·
          refine ⟨52669602335233092996769585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70226136446977457329026113 52669602335233092996769585)
          ·
            refine ⟨39502201751424819747577189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52669602335233092996769585 39502201751424819747577189)
            ·
              refine ⟨7406662828392153702670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39502201751424819747577189 7406662828392153702670723)
              ·
                refine ⟨11109994242588230554006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406662828392153702670723 11109994242588230554006085)
                ·
                  refine ⟨2083123920485293228876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11109994242588230554006085 2083123920485293228876141)
                  ·
                    refine ⟨781171470181984960828553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083123920485293228876141 781171470181984960828553)
                    ·
                      rfl

theorem cell22_2281989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_2281989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281989 prefixEnd_2281989 := by exact prefixLift 2281989
  have htrace : WordTrace (prefixWord ++ tailWord_2281989) baseStart_2281989 baseEnd_2281989 := by
    simpa [prefixWord, tailWord_2281989, baseEnd_2281989] using wordTrace_append hprefix tailTrace_2281989
  have hstable : (prefixWord ++ tailWord_2281989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281989).length < 2 ^ (prefixWord ++ tailWord_2281989).sum := by decide
  have hdescent : baseEnd_2281989 < baseStart_2281989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281991 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 6]
def baseStart_2281991 : Nat := 118140960795 + 2281991 * 2 ^ 59
def prefixEnd_2281991 : Nat := 4983230072969 + 3 ^ 40 * 2281991 * 2
def baseEnd_2281991 : Nat := 260390718274285874092849

theorem tailTrace_2281991 : CollatzResearch.WordTrace tailWord_2281991 prefixEnd_2281991 260390718274285874092849 := by
  unfold tailWord_2281991
  simp only [CollatzResearch.WordTrace]
  refine ⟨83231049475743814879677827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55487366317162543253118551 83231049475743814879677827)
  ·
    refine ⟨124846574213615722319516741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83231049475743814879677827 124846574213615722319516741)
    ·
      refine ⟨23408732665052947934909389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124846574213615722319516741 23408732665052947934909389)
      ·
        refine ⟨8778274749394855475591021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23408732665052947934909389 8778274749394855475591021)
        ·
          refine ⟨3291853031023070803346633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8778274749394855475591021 3291853031023070803346633)
          ·
            refine ⟨2468889773267303102509975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291853031023070803346633 2468889773267303102509975)
            ·
              refine ⟨3703334659900954653764963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468889773267303102509975 3703334659900954653764963)
              ·
                refine ⟨5555001989851431980647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703334659900954653764963 5555001989851431980647445)
                ·
                  refine ⟨260390718274285874092849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5555001989851431980647445 260390718274285874092849)
                  ·
                    rfl

theorem cell22_2281991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].length) (baseStart_2281991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2281991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2281991 prefixEnd_2281991 := by exact prefixLift 2281991
  have htrace : WordTrace (prefixWord ++ tailWord_2281991) baseStart_2281991 baseEnd_2281991 := by
    simpa [prefixWord, tailWord_2281991, baseEnd_2281991] using wordTrace_append hprefix tailTrace_2281991
  have hstable : (prefixWord ++ tailWord_2281991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281991).length < 2 ^ (prefixWord ++ tailWord_2281991).sum := by decide
  have hdescent : baseEnd_2281991 < baseStart_2281991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282023 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2282023 : Nat := 118140960795 + 2282023 * 2 ^ 59
def prefixEnd_2282023 : Nat := 4983230072969 + 3 ^ 40 * 2282023 * 2
def baseEnd_2282023 : Nat := 781183109076820205478449

theorem tailTrace_2282023 : CollatzResearch.WordTrace tailWord_2282023 prefixEnd_2282023 781183109076820205478449 := by
  unfold tailWord_2282023
  simp only [CollatzResearch.WordTrace]
  refine ⟨83232216611627884344842723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55488144407751922896561815 83232216611627884344842723)
  ·
    refine ⟨124848324917441826517264085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83232216611627884344842723 124848324917441826517264085)
    ·
      refine ⟨2926132615252542808998377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 124848324917441826517264085 2926132615252542808998377)
      ·
        refine ⟨2194599461439407106748783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2926132615252542808998377 2194599461439407106748783)
        ·
          refine ⟨3291899192159110660123175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194599461439407106748783 3291899192159110660123175)
          ·
            refine ⟨4937848788238665990184763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291899192159110660123175 4937848788238665990184763)
            ·
              refine ⟨7406773182357998985277145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937848788238665990184763 7406773182357998985277145)
              ·
                refine ⟨5555079886768499238957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7406773182357998985277145 5555079886768499238957859)
                ·
                  refine ⟨8332619830152748858436789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5555079886768499238957859 8332619830152748858436789)
                  ·
                    refine ⟨781183109076820205478449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8332619830152748858436789 781183109076820205478449)
                    ·
                      rfl

theorem cell22_2282023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2282023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282023 prefixEnd_2282023 := by exact prefixLift 2282023
  have htrace : WordTrace (prefixWord ++ tailWord_2282023) baseStart_2282023 baseEnd_2282023 := by
    simpa [prefixWord, tailWord_2282023, baseEnd_2282023] using wordTrace_append hprefix tailTrace_2282023
  have hstable : (prefixWord ++ tailWord_2282023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282023).length < 2 ^ (prefixWord ++ tailWord_2282023).sum := by decide
  have hdescent : baseEnd_2282023 < baseStart_2282023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282036 : List Nat := [2, 5, 1, 3, 1, 10]
def baseStart_2282036 : Nat := 118140960795 + 2282036 * 2 ^ 59
def prefixEnd_2282036 : Nat := 4983230072969 + 3 ^ 40 * 2282036 * 2
def baseEnd_2282036 : Nat := 9644290854845586480289

theorem tailTrace_2282036 : CollatzResearch.WordTrace tailWord_2282036 prefixEnd_2282036 9644290854845586480289 := by
  unfold tailWord_2282036
  simp only [CollatzResearch.WordTrace]
  refine ⟨41616345380290393782532981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55488460507053858376710641 41616345380290393782532981)
  ·
    refine ⟨3901532379402224417112467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41616345380290393782532981 3901532379402224417112467)
    ·
      refine ⟨5852298569103336625668701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901532379402224417112467 5852298569103336625668701)
      ·
        refine ⟨2194611963413751234625763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5852298569103336625668701 2194611963413751234625763)
        ·
          refine ⟨3291917945120626851938645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194611963413751234625763 3291917945120626851938645)
          ·
            refine ⟨9644290854845586480289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3291917945120626851938645 9644290854845586480289)
            ·
              rfl

theorem cell22_2282036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 10].length) (baseStart_2282036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282036 prefixEnd_2282036 := by exact prefixLift 2282036
  have htrace : WordTrace (prefixWord ++ tailWord_2282036) baseStart_2282036 baseEnd_2282036 := by
    simpa [prefixWord, tailWord_2282036, baseEnd_2282036] using wordTrace_append hprefix tailTrace_2282036
  have hstable : (prefixWord ++ tailWord_2282036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282036).length < 2 ^ (prefixWord ++ tailWord_2282036).sum := by decide
  have hdescent : baseEnd_2282036 < baseStart_2282036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282049 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2282049 : Nat := 118140960795 + 2282049 * 2 ^ 59
def prefixEnd_2282049 : Nat := 4983230072969 + 3 ^ 40 * 2282049 * 2
def baseEnd_2282049 : Nat := 781192009408164804328369

theorem tailTrace_2282049 : CollatzResearch.WordTrace tailWord_2282049 prefixEnd_2282049 781192009408164804328369 := by
  unfold tailWord_2282049
  simp only [CollatzResearch.WordTrace]
  refine ⟨83233164909533690785289201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55488776606355793856859467 83233164909533690785289201)
  ·
    refine ⟨62424873682150268088966901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83233164909533690785289201 62424873682150268088966901)
    ·
      refine ⟨5852331907701587633340647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62424873682150268088966901 5852331907701587633340647)
      ·
        refine ⟨8778497861552381450010971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852331907701587633340647 8778497861552381450010971)
        ·
          refine ⟨13167746792328572175016457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8778497861552381450010971 13167746792328572175016457)
          ·
            refine ⟨9875810094246429131262343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13167746792328572175016457 9875810094246429131262343)
            ·
              refine ⟨14813715141369643696893515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875810094246429131262343 14813715141369643696893515)
              ·
                refine ⟨22220572712054465545340273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14813715141369643696893515 22220572712054465545340273)
                ·
                  refine ⟨16665429534040849159005205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22220572712054465545340273 16665429534040849159005205)
                  ·
                    refine ⟨781192009408164804328369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16665429534040849159005205 781192009408164804328369)
                    ·
                      rfl

theorem cell22_2282049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2282049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282049 prefixEnd_2282049 := by exact prefixLift 2282049
  have htrace : WordTrace (prefixWord ++ tailWord_2282049) baseStart_2282049 baseEnd_2282049 := by
    simpa [prefixWord, tailWord_2282049, baseEnd_2282049] using wordTrace_append hprefix tailTrace_2282049
  have hstable : (prefixWord ++ tailWord_2282049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282049).length < 2 ^ (prefixWord ++ tailWord_2282049).sum := by decide
  have hdescent : baseEnd_2282049 < baseStart_2282049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282085 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_2282085 : Nat := 118140960795 + 2282085 * 2 ^ 59
def prefixEnd_2282085 : Nat := 4983230072969 + 3 ^ 40 * 2282085 * 2
def baseEnd_2282085 : Nat := 781204332943872710428259

theorem tailTrace_2282085 : CollatzResearch.WordTrace tailWord_2282085 prefixEnd_2282085 781204332943872710428259 := by
  unfold tailWord_2282085
  simp only [CollatzResearch.WordTrace]
  refine ⟨83234477937403268933599709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55489651958268845955733139 83234477937403268933599709)
  ·
    refine ⟨31212929226526225850099891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83234477937403268933599709 31212929226526225850099891)
    ·
      refine ⟨46819393839789338775149837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31212929226526225850099891 46819393839789338775149837)
      ·
        refine ⟨17557272689921002040681189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46819393839789338775149837 17557272689921002040681189)
        ·
          refine ⟨3291988629360187882627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17557272689921002040681189 3291988629360187882627723)
          ·
            refine ⟨4937982944040281823941585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291988629360187882627723 4937982944040281823941585)
            ·
              refine ⟨3703487208030211367956189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937982944040281823941585 3703487208030211367956189)
              ·
                refine ⟨1388807703011329262983571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3703487208030211367956189 1388807703011329262983571)
                ·
                  refine ⟨2083211554516993894475357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388807703011329262983571 2083211554516993894475357)
                  ·
                    refine ⟨781204332943872710428259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083211554516993894475357 781204332943872710428259)
                    ·
                      rfl

theorem cell22_2282085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_2282085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282085 prefixEnd_2282085 := by exact prefixLift 2282085
  have htrace : WordTrace (prefixWord ++ tailWord_2282085) baseStart_2282085 baseEnd_2282085 := by
    simpa [prefixWord, tailWord_2282085, baseEnd_2282085] using wordTrace_append hprefix tailTrace_2282085
  have hstable : (prefixWord ++ tailWord_2282085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282085).length < 2 ^ (prefixWord ++ tailWord_2282085).sum := by decide
  have hdescent : baseEnd_2282085 < baseStart_2282085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282098 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_2282098 : Nat := 118140960795 + 2282098 * 2 ^ 59
def prefixEnd_2282098 : Nat := 4983230072969 + 3 ^ 40 * 2282098 * 2
def baseEnd_2282098 : Nat := 260402927703181669951073

theorem tailTrace_2282098 : CollatzResearch.WordTrace tailWord_2282098 prefixEnd_2282098 260402927703181669951073 := by
  unfold tailWord_2282098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20808738021589043038455737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55489968057570781435881965 20808738021589043038455737)
  ·
    refine ⟨15606553516191782278841803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20808738021589043038455737 15606553516191782278841803)
    ·
      refine ⟨23409830274287673418262705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15606553516191782278841803 23409830274287673418262705)
      ·
        refine ⟨17557372705715755063697029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23409830274287673418262705 17557372705715755063697029)
        ·
          refine ⟨3292007382321704074443193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17557372705715755063697029 3292007382321704074443193)
          ·
            refine ⟨2469005536741278055832395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292007382321704074443193 2469005536741278055832395)
            ·
              refine ⟨3703508305111917083748593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469005536741278055832395 3703508305111917083748593)
              ·
                refine ⟨2777631228833937812811445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703508305111917083748593 2777631228833937812811445)
                ·
                  refine ⟨260402927703181669951073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2777631228833937812811445 260402927703181669951073)
                  ·
                    rfl

theorem cell22_2282098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_2282098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282098 prefixEnd_2282098 := by exact prefixLift 2282098
  have htrace : WordTrace (prefixWord ++ tailWord_2282098) baseStart_2282098 baseEnd_2282098 := by
    simpa [prefixWord, tailWord_2282098, baseEnd_2282098] using wordTrace_append hprefix tailTrace_2282098
  have hstable : (prefixWord ++ tailWord_2282098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282098).length < 2 ^ (prefixWord ++ tailWord_2282098).sum := by decide
  have hdescent : baseEnd_2282098 < baseStart_2282098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282124 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_2282124 : Nat := 118140960795 + 2282124 * 2 ^ 59
def prefixEnd_2282124 : Nat := 4983230072969 + 3 ^ 40 * 2282124 * 2
def baseEnd_2282124 : Nat := 781217683440889608703139

theorem tailTrace_2282124 : CollatzResearch.WordTrace tailWord_2282124 prefixEnd_2282124 781217683440889608703139 := by
  unfold tailWord_2282124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41617950192130989297134713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55490600256174652396179617 41617950192130989297134713)
  ·
    refine ⟨31213462644098241972851035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41617950192130989297134713 31213462644098241972851035)
    ·
      refine ⟨46820193966147362959276553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31213462644098241972851035 46820193966147362959276553)
      ·
        refine ⟨35115145474610522219457415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46820193966147362959276553 35115145474610522219457415)
        ·
          refine ⟨52672718211915783329186123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35115145474610522219457415 52672718211915783329186123)
          ·
            refine ⟨79009077317873674993779185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52672718211915783329186123 79009077317873674993779185)
            ·
              refine ⟨59256807988405256245334389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79009077317873674993779185 59256807988405256245334389)
              ·
                refine ⟨5555325748912992773000099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59256807988405256245334389 5555325748912992773000099)
                ·
                  refine ⟨8332988623369489159500149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5555325748912992773000099 8332988623369489159500149)
                  ·
                    refine ⟨781217683440889608703139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8332988623369489159500149 781217683440889608703139)
                    ·
                      rfl

theorem cell22_2282124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_2282124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282124 prefixEnd_2282124 := by exact prefixLift 2282124
  have htrace : WordTrace (prefixWord ++ tailWord_2282124) baseStart_2282124 baseEnd_2282124 := by
    simpa [prefixWord, tailWord_2282124, baseEnd_2282124] using wordTrace_append hprefix tailTrace_2282124
  have hstable : (prefixWord ++ tailWord_2282124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282124).length < 2 ^ (prefixWord ++ tailWord_2282124).sum := by decide
  have hdescent : baseEnd_2282124 < baseStart_2282124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282141 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2282141 : Nat := 118140960795 + 2282141 * 2 ^ 59
def prefixEnd_2282141 : Nat := 4983230072969 + 3 ^ 40 * 2282141 * 2
def baseEnd_2282141 : Nat := 781223502888307231028087

theorem tailTrace_2282141 : CollatzResearch.WordTrace tailWord_2282141 prefixEnd_2282141 781223502888307231028087 := by
  unfold tailWord_2282141
  simp only [CollatzResearch.WordTrace]
  refine ⟨83236520425200390497638277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55491013616800260331758851 83236520425200390497638277)
  ·
    refine ⟨15606847579725073218307177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83236520425200390497638277 15606847579725073218307177)
    ·
      refine ⟨11705135684793804913730383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15606847579725073218307177 11705135684793804913730383)
      ·
        refine ⟨17557703527190707370595575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705135684793804913730383 17557703527190707370595575)
        ·
          refine ⟨26336555290786061055893363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17557703527190707370595575 26336555290786061055893363)
          ·
            refine ⟨39504832936179091583840045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26336555290786061055893363 39504832936179091583840045)
            ·
              refine ⟨14814312351067159343940017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39504832936179091583840045 14814312351067159343940017)
              ·
                refine ⟨11110734263300369507955013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14814312351067159343940017 11110734263300369507955013)
                ·
                  refine ⟨2083262674368819282741565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11110734263300369507955013 2083262674368819282741565)
                  ·
                    refine ⟨781223502888307231028087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083262674368819282741565 781223502888307231028087)
                    ·
                      rfl

theorem cell22_2282141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2282141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282141 prefixEnd_2282141 := by exact prefixLift 2282141
  have htrace : WordTrace (prefixWord ++ tailWord_2282141) baseStart_2282141 baseEnd_2282141 := by
    simpa [prefixWord, tailWord_2282141, baseEnd_2282141] using wordTrace_append hprefix tailTrace_2282141
  have hstable : (prefixWord ++ tailWord_2282141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282141).length < 2 ^ (prefixWord ++ tailWord_2282141).sum := by decide
  have hdescent : baseEnd_2282141 < baseStart_2282141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282175 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 2, 3]
def baseStart_2282175 : Nat := 118140960795 + 2282175 * 2 ^ 59
def prefixEnd_2282175 : Nat := 4983230072969 + 3 ^ 40 * 2282175 * 2
def baseEnd_2282175 : Nat := 781235141783142475677983

theorem tailTrace_2282175 : CollatzResearch.WordTrace tailWord_2282175 prefixEnd_2282175 781235141783142475677983 := by
  unfold tailWord_2282175
  simp only [CollatzResearch.WordTrace]
  refine ⟨83237760507077214304375979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55491840338051476202917319 83237760507077214304375979)
  ·
    refine ⟨124856640760615821456563969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83237760507077214304375979 124856640760615821456563969)
    ·
      refine ⟨93642480570461866092422977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124856640760615821456563969 93642480570461866092422977)
      ·
        refine ⟨70231860427846399569317233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93642480570461866092422977 70231860427846399569317233)
        ·
          refine ⟨52673895320884799676987925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70231860427846399569317233 52673895320884799676987925)
          ·
            refine ⟨2469088843166474984858809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52673895320884799676987925 2469088843166474984858809)
            ·
              refine ⟨1851816632374856238644107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469088843166474984858809 1851816632374856238644107)
              ·
                refine ⟨2777724948562284357966161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851816632374856238644107 2777724948562284357966161)
                ·
                  refine ⟨2083293711421713268474621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777724948562284357966161 2083293711421713268474621)
                  ·
                    refine ⟨781235141783142475677983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083293711421713268474621 781235141783142475677983)
                    ·
                      rfl

theorem cell22_2282175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_2282175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282175 prefixEnd_2282175 := by exact prefixLift 2282175
  have htrace : WordTrace (prefixWord ++ tailWord_2282175) baseStart_2282175 baseEnd_2282175 := by
    simpa [prefixWord, tailWord_2282175, baseEnd_2282175] using wordTrace_append hprefix tailTrace_2282175
  have hstable : (prefixWord ++ tailWord_2282175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282175).length < 2 ^ (prefixWord ++ tailWord_2282175).sum := by decide
  have hdescent : baseEnd_2282175 < baseStart_2282175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282291 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_2282291 : Nat := 118140960795 + 2282291 * 2 ^ 59
def prefixEnd_2282291 : Nat := 4983230072969 + 3 ^ 40 * 2282291 * 2
def baseEnd_2282291 : Nat := 781274850953756839777627

theorem tailTrace_2282291 : CollatzResearch.WordTrace tailWord_2282291 prefixEnd_2282291 781274850953756839777627 := by
  unfold tailWord_2282291
  simp only [CollatzResearch.WordTrace]
  refine ⟨83241991374656966115598727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55494660916437977410399151 83241991374656966115598727)
  ·
    refine ⟨124862987061985449173398091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83241991374656966115598727 124862987061985449173398091)
    ·
      refine ⟨187294480592978173760097137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124862987061985449173398091 187294480592978173760097137)
      ·
        refine ⟨140470860444733630320072853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187294480592978173760097137 140470860444733630320072853)
        ·
          refine ⟨6584571583346888921253415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140470860444733630320072853 6584571583346888921253415)
          ·
            refine ⟨9876857375020333381880123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584571583346888921253415 9876857375020333381880123)
            ·
              refine ⟨14815286062530500072820185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9876857375020333381880123 14815286062530500072820185)
              ·
                refine ⟨11111464546897875054615139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14815286062530500072820185 11111464546897875054615139)
                ·
                  refine ⟨16667196820346812581922709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11111464546897875054615139 16667196820346812581922709)
                  ·
                    refine ⟨781274850953756839777627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16667196820346812581922709 781274850953756839777627)
                    ·
                      rfl

theorem cell22_2282291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_2282291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282291 prefixEnd_2282291 := by exact prefixLift 2282291
  have htrace : WordTrace (prefixWord ++ tailWord_2282291) baseStart_2282291 baseEnd_2282291 := by
    simpa [prefixWord, tailWord_2282291, baseEnd_2282291] using wordTrace_append hprefix tailTrace_2282291
  have hstable : (prefixWord ++ tailWord_2282291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282291).length < 2 ^ (prefixWord ++ tailWord_2282291).sum := by decide
  have hdescent : baseEnd_2282291 < baseStart_2282291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282293 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2282293 : Nat := 118140960795 + 2282293 * 2 ^ 59
def prefixEnd_2282293 : Nat := 4983230072969 + 3 ^ 40 * 2282293 * 2
def baseEnd_2282293 : Nat := 781275535594629501227621

theorem tailTrace_2282293 : CollatzResearch.WordTrace tailWord_2282293 prefixEnd_2282293 781275535594629501227621 := by
  unfold tailWord_2282293
  simp only [CollatzResearch.WordTrace]
  refine ⟨83242064320649720457171533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55494709547099813638114355 83242064320649720457171533)
  ·
    refine ⟨31215774120243645171439325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83242064320649720457171533 31215774120243645171439325)
    ·
      refine ⟨11705915295091366939289747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31215774120243645171439325 11705915295091366939289747)
      ·
        refine ⟨17558872942637050408934621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705915295091366939289747 17558872942637050408934621)
        ·
          refine ⟨6584577353488893903350483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17558872942637050408934621 6584577353488893903350483)
          ·
            refine ⟨9876866030233340855025725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584577353488893903350483 9876866030233340855025725)
            ·
              refine ⟨3703824761337502820634647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9876866030233340855025725 3703824761337502820634647)
              ·
                refine ⟨5555737142006254230951971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703824761337502820634647 5555737142006254230951971)
                ·
                  refine ⟨8333605713009381346427957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5555737142006254230951971 8333605713009381346427957)
                  ·
                    refine ⟨781275535594629501227621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8333605713009381346427957 781275535594629501227621)
                    ·
                      rfl

theorem cell22_2282293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2282293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282293 prefixEnd_2282293 := by exact prefixLift 2282293
  have htrace : WordTrace (prefixWord ++ tailWord_2282293) baseStart_2282293 baseEnd_2282293 := by
    simpa [prefixWord, tailWord_2282293, baseEnd_2282293] using wordTrace_append hprefix tailTrace_2282293
  have hstable : (prefixWord ++ tailWord_2282293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282293).length < 2 ^ (prefixWord ++ tailWord_2282293).sum := by decide
  have hdescent : baseEnd_2282293 < baseStart_2282293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282336 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_2282336 : Nat := 118140960795 + 2282336 * 2 ^ 59
def prefixEnd_2282336 : Nat := 4983230072969 + 3 ^ 40 * 2282336 * 2
def baseEnd_2282336 : Nat := 781290255373391722402489

theorem tailTrace_2282336 : CollatzResearch.WordTrace tailWord_2282336 prefixEnd_2282336 781290255373391722402489 := by
  unfold tailWord_2282336
  simp only [CollatzResearch.WordTrace]
  refine ⟨41621816329746969400493431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55495755106329292533991241 41621816329746969400493431)
  ·
    refine ⟨62432724494620454100740147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41621816329746969400493431 62432724494620454100740147)
    ·
      refine ⟨93649086741930681151110221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62432724494620454100740147 93649086741930681151110221)
      ·
        refine ⟨35118407528224005431666333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93649086741930681151110221 35118407528224005431666333)
        ·
          refine ⟨13169402823084002036874875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35118407528224005431666333 13169402823084002036874875)
          ·
            refine ⟨19754104234626003055312313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13169402823084002036874875 19754104234626003055312313)
            ·
              refine ⟨14815578175969502291484235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19754104234626003055312313 14815578175969502291484235)
              ·
                refine ⟨22223367263954253437226353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14815578175969502291484235 22223367263954253437226353)
                ·
                  refine ⟨16667525447965690077919765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22223367263954253437226353 16667525447965690077919765)
                  ·
                    refine ⟨781290255373391722402489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16667525447965690077919765 781290255373391722402489)
                    ·
                      rfl

theorem cell22_2282336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_2282336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282336 prefixEnd_2282336 := by exact prefixLift 2282336
  have htrace : WordTrace (prefixWord ++ tailWord_2282336) baseStart_2282336 baseEnd_2282336 := by
    simpa [prefixWord, tailWord_2282336, baseEnd_2282336] using wordTrace_append hprefix tailTrace_2282336
  have hstable : (prefixWord ++ tailWord_2282336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282336).length < 2 ^ (prefixWord ++ tailWord_2282336).sum := by decide
  have hdescent : baseEnd_2282336 < baseStart_2282336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282389 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2282389 : Nat := 118140960795 + 2282389 * 2 ^ 59
def prefixEnd_2282389 : Nat := 4983230072969 + 3 ^ 40 * 2282389 * 2
def baseEnd_2282389 : Nat := 781308398356517250827327

theorem tailTrace_2282389 : CollatzResearch.WordTrace tailWord_2282389 prefixEnd_2282389 781308398356517250827327 := by
  unfold tailWord_2282389
  simp only [CollatzResearch.WordTrace]
  refine ⟨83245565728301928852666221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55497043818867952568444147 83245565728301928852666221)
  ·
    refine ⟨31217087148113223319749833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83245565728301928852666221 31217087148113223319749833)
    ·
      refine ⟨23412815361084917489812375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31217087148113223319749833 23412815361084917489812375)
      ·
        refine ⟨35119223041627376234718563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23412815361084917489812375 35119223041627376234718563)
        ·
          refine ⟨52678834562441064352077845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35119223041627376234718563 52678834562441064352077845)
          ·
            refine ⟨2469320370114424891503649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52678834562441064352077845 2469320370114424891503649)
            ·
              refine ⟨1851990277585818668627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469320370114424891503649 1851990277585818668627737)
              ·
                refine ⟨1388992708189364001470803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851990277585818668627737 1388992708189364001470803)
                ·
                  refine ⟨2083489062284046002206205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388992708189364001470803 2083489062284046002206205)
                  ·
                    refine ⟨781308398356517250827327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083489062284046002206205 781308398356517250827327)
                    ·
                      rfl

theorem cell22_2282389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2282389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282389 prefixEnd_2282389 := by exact prefixLift 2282389
  have htrace : WordTrace (prefixWord ++ tailWord_2282389) baseStart_2282389 baseEnd_2282389 := by
    simpa [prefixWord, tailWord_2282389, baseEnd_2282389] using wordTrace_append hprefix tailTrace_2282389
  have hstable : (prefixWord ++ tailWord_2282389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282389).length < 2 ^ (prefixWord ++ tailWord_2282389).sum := by decide
  have hdescent : baseEnd_2282389 < baseStart_2282389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282411 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_2282411 : Nat := 118140960795 + 2282411 * 2 ^ 59
def prefixEnd_2282411 : Nat := 4983230072969 + 3 ^ 40 * 2282411 * 2
def baseEnd_2282411 : Nat := 781315929406116526777259

theorem tailTrace_2282411 : CollatzResearch.WordTrace tailWord_2282411 prefixEnd_2282411 781315929406116526777259 := by
  unfold tailWord_2282411
  simp only [CollatzResearch.WordTrace]
  refine ⟨83246368134222226609967087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55497578756148151073311391 83246368134222226609967087)
  ·
    refine ⟨124869552201333339914950631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83246368134222226609967087 124869552201333339914950631)
    ·
      refine ⟨187304328302000009872425947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124869552201333339914950631 187304328302000009872425947)
      ·
        refine ⟨280956492453000014808638921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187304328302000009872425947 280956492453000014808638921)
        ·
          refine ⟨210717369339750011106479191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280956492453000014808638921 210717369339750011106479191)
          ·
            refine ⟨316076054009625016659718787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210717369339750011106479191 316076054009625016659718787)
            ·
              refine ⟨474114081014437524989578181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316076054009625016659718787 474114081014437524989578181)
              ·
                refine ⟨88896390190207035935545909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474114081014437524989578181 88896390190207035935545909)
                ·
                  refine ⟨8334036580331909618957429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88896390190207035935545909 8334036580331909618957429)
                  ·
                    refine ⟨781315929406116526777259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8334036580331909618957429 781315929406116526777259)
                    ·
                      rfl

theorem cell22_2282411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_2282411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282411 prefixEnd_2282411 := by exact prefixLift 2282411
  have htrace : WordTrace (prefixWord ++ tailWord_2282411) baseStart_2282411 baseEnd_2282411 := by
    simpa [prefixWord, tailWord_2282411, baseEnd_2282411] using wordTrace_append hprefix tailTrace_2282411
  have hstable : (prefixWord ++ tailWord_2282411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282411).length < 2 ^ (prefixWord ++ tailWord_2282411).sum := by decide
  have hdescent : baseEnd_2282411 < baseStart_2282411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282432 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_2282432 : Nat := 118140960795 + 2282432 * 2 ^ 59
def prefixEnd_2282432 : Nat := 4983230072969 + 3 ^ 40 * 2282432 * 2
def baseEnd_2282432 : Nat := 781323118135279472002195

theorem tailTrace_2282432 : CollatzResearch.WordTrace tailWord_2282432 prefixEnd_2282432 781323118135279472002195 := by
  unfold tailWord_2282432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41623567033573073598240775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55498089378097431464321033 41623567033573073598240775)
  ·
    refine ⟨62435350550359610397361163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41623567033573073598240775 62435350550359610397361163)
    ·
      refine ⟨93653025825539415596041745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62435350550359610397361163 93653025825539415596041745)
      ·
        refine ⟨70239769369154561697031309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93653025825539415596041745 70239769369154561697031309)
        ·
          refine ⟨26339913513432960636386741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70239769369154561697031309 26339913513432960636386741)
          ·
            refine ⟨2469366891884340059661257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26339913513432960636386741 2469366891884340059661257)
            ·
              refine ⟨1852025168913255044745943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469366891884340059661257 1852025168913255044745943)
              ·
                refine ⟨2778037753369882567118915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852025168913255044745943 2778037753369882567118915)
                ·
                  refine ⟨4167056630054823850678373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778037753369882567118915 4167056630054823850678373)
                  ·
                    refine ⟨781323118135279472002195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167056630054823850678373 781323118135279472002195)
                    ·
                      rfl

theorem cell22_2282432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_2282432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282432 prefixEnd_2282432 := by exact prefixLift 2282432
  have htrace : WordTrace (prefixWord ++ tailWord_2282432) baseStart_2282432 baseEnd_2282432 := by
    simpa [prefixWord, tailWord_2282432, baseEnd_2282432] using wordTrace_append hprefix tailTrace_2282432
  have hstable : (prefixWord ++ tailWord_2282432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282432).length < 2 ^ (prefixWord ++ tailWord_2282432).sum := by decide
  have hdescent : baseEnd_2282432 < baseStart_2282432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282503 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 7]
def baseStart_2282503 : Nat := 118140960795 + 2282503 * 2 ^ 59
def prefixEnd_2282503 : Nat := 4983230072969 + 3 ^ 40 * 2282503 * 2
def baseEnd_2282503 : Nat := 260449140962086317825659

theorem tailTrace_2282503 : CollatzResearch.WordTrace tailWord_2282503 prefixEnd_2282503 260449140962086317825659 := by
  unfold tailWord_2282503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83249723649888926322316163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55499815766592617548210775 83249723649888926322316163)
  ·
    refine ⟨124874585474833389483474245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83249723649888926322316163 124874585474833389483474245)
    ·
      refine ⟨23413984776531260528151421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124874585474833389483474245 23413984776531260528151421)
      ·
        refine ⟨8780244291199222698056783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23413984776531260528151421 8780244291199222698056783)
        ·
          refine ⟨13170366436798834047085175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8780244291199222698056783 13170366436798834047085175)
          ·
            refine ⟨19755549655198251070627763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13170366436798834047085175 19755549655198251070627763)
            ·
              refine ⟨29633324482797376605941645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19755549655198251070627763 29633324482797376605941645)
              ·
                refine ⟨11112496681049016227228117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29633324482797376605941645 11112496681049016227228117)
                ·
                  refine ⟨260449140962086317825659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11112496681049016227228117 260449140962086317825659)
                  ·
                    rfl

theorem cell22_2282503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_2282503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282503 prefixEnd_2282503 := by exact prefixLift 2282503
  have htrace : WordTrace (prefixWord ++ tailWord_2282503) baseStart_2282503 baseEnd_2282503 := by
    simpa [prefixWord, tailWord_2282503, baseEnd_2282503] using wordTrace_append hprefix tailTrace_2282503
  have hstable : (prefixWord ++ tailWord_2282503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282503).length < 2 ^ (prefixWord ++ tailWord_2282503).sum := by decide
  have hdescent : baseEnd_2282503 < baseStart_2282503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282507 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 3, 3]
def baseStart_2282507 : Nat := 118140960795 + 2282507 * 2 ^ 59
def prefixEnd_2282507 : Nat := 4983230072969 + 3 ^ 40 * 2282507 * 2
def baseEnd_2282507 : Nat := 781348792168004276376965

theorem tailTrace_2282507 : CollatzResearch.WordTrace tailWord_2282507 prefixEnd_2282507 781348792168004276376965 := by
  unfold tailWord_2282507
  simp only [CollatzResearch.WordTrace]
  refine ⟨83249869541874435005461775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55499913027916290003641183 83249869541874435005461775)
  ·
    refine ⟨124874804312811652508192663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83249869541874435005461775 124874804312811652508192663)
    ·
      refine ⟨187312206469217478762288995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124874804312811652508192663 187312206469217478762288995)
      ·
        refine ⟨280968309703826218143433493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187312206469217478762288995 280968309703826218143433493)
        ·
          refine ⟨13170389517366853975473445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 280968309703826218143433493 13170389517366853975473445)
          ·
            refine ⟨2469448034506285120401271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13170389517366853975473445 2469448034506285120401271)
            ·
              refine ⟨3704172051759427680601907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469448034506285120401271 3704172051759427680601907)
              ·
                refine ⟨5556258077639141520902861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704172051759427680601907 5556258077639141520902861)
                ·
                  refine ⟨2083596779114678070338573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5556258077639141520902861 2083596779114678070338573)
                  ·
                    refine ⟨781348792168004276376965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083596779114678070338573 781348792168004276376965)
                    ·
                      rfl

theorem cell22_2282507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].length) (baseStart_2282507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282507 prefixEnd_2282507 := by exact prefixLift 2282507
  have htrace : WordTrace (prefixWord ++ tailWord_2282507) baseStart_2282507 baseEnd_2282507 := by
    simpa [prefixWord, tailWord_2282507, baseEnd_2282507] using wordTrace_append hprefix tailTrace_2282507
  have hstable : (prefixWord ++ tailWord_2282507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282507).length < 2 ^ (prefixWord ++ tailWord_2282507).sum := by decide
  have hdescent : baseEnd_2282507 < baseStart_2282507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282520 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_2282520 : Nat := 118140960795 + 2282520 * 2 ^ 59
def prefixEnd_2282520 : Nat := 4983230072969 + 3 ^ 40 * 2282520 * 2
def baseEnd_2282520 : Nat := 260451080777892191933975

theorem tailTrace_2282520 : CollatzResearch.WordTrace tailWord_2282520 prefixEnd_2282520 260451080777892191933975 := by
  unfold tailWord_2282520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41625171845413669112842507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55500229127218225483790009 41625171845413669112842507)
  ·
    refine ⟨62437757768120503669263761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41625171845413669112842507 62437757768120503669263761)
    ·
      refine ⟨46828318326090377751947821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62437757768120503669263761 46828318326090377751947821)
      ·
        refine ⟨17560619372283891656980433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46828318326090377751947821 17560619372283891656980433)
        ·
          refine ⟨13170464529212918742735325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17560619372283891656980433 13170464529212918742735325)
          ·
            refine ⟨4938924198454844528525747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13170464529212918742735325 4938924198454844528525747)
            ·
              refine ⟨7408386297682266792788621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938924198454844528525747 7408386297682266792788621)
              ·
                refine ⟨2778144861630850047295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7408386297682266792788621 2778144861630850047295733)
                ·
                  refine ⟨260451080777892191933975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778144861630850047295733 260451080777892191933975)
                  ·
                    rfl

theorem cell22_2282520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_2282520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282520 prefixEnd_2282520 := by exact prefixLift 2282520
  have htrace : WordTrace (prefixWord ++ tailWord_2282520) baseStart_2282520 baseEnd_2282520 := by
    simpa [prefixWord, tailWord_2282520, baseEnd_2282520] using wordTrace_append hprefix tailTrace_2282520
  have hstable : (prefixWord ++ tailWord_2282520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282520).length < 2 ^ (prefixWord ++ tailWord_2282520).sum := by decide
  have hdescent : baseEnd_2282520 < baseStart_2282520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282558 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2282558 : Nat := 118140960795 + 2282558 * 2 ^ 59
def prefixEnd_2282558 : Nat := 4983230072969 + 3 ^ 40 * 2282558 * 2
def baseEnd_2282558 : Nat := 781366250510257143351809

theorem tailTrace_2282558 : CollatzResearch.WordTrace tailWord_2282558 prefixEnd_2282558 781366250510257143351809 := by
  unfold tailWord_2282558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10406466208086208839446041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55501153109793113810378885 10406466208086208839446041)
  ·
    refine ⟨7804849656064656629584531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10406466208086208839446041 7804849656064656629584531)
    ·
      refine ⟨11707274484096984944376797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804849656064656629584531 11707274484096984944376797)
      ·
        refine ⟨4390227931536369354141299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11707274484096984944376797 4390227931536369354141299)
        ·
          refine ⟨6585341897304554031211949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390227931536369354141299 6585341897304554031211949)
          ·
            refine ⟨2469503211489207761704481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6585341897304554031211949 2469503211489207761704481)
            ·
              refine ⟨1852127408616905821278361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469503211489207761704481 1852127408616905821278361)
              ·
                refine ⟨1389095556462679365958771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852127408616905821278361 1389095556462679365958771)
                ·
                  refine ⟨2083643334694019048938157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389095556462679365958771 2083643334694019048938157)
                  ·
                    refine ⟨781366250510257143351809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083643334694019048938157 781366250510257143351809)
                    ·
                      rfl

theorem cell22_2282558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2282558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282558 prefixEnd_2282558 := by exact prefixLift 2282558
  have htrace : WordTrace (prefixWord ++ tailWord_2282558) baseStart_2282558 baseEnd_2282558 := by
    simpa [prefixWord, tailWord_2282558, baseEnd_2282558] using wordTrace_append hprefix tailTrace_2282558
  have hstable : (prefixWord ++ tailWord_2282558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282558).length < 2 ^ (prefixWord ++ tailWord_2282558).sum := by decide
  have hdescent : baseEnd_2282558 < baseStart_2282558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282563 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_2282563 : Nat := 118140960795 + 2282563 * 2 ^ 59
def prefixEnd_2282563 : Nat := 4983230072969 + 3 ^ 40 * 2282563 * 2
def baseEnd_2282563 : Nat := 781367962112438796976793

theorem tailTrace_2282563 : CollatzResearch.WordTrace tailWord_2282563 prefixEnd_2282563 781367962112438796976793 := by
  unfold tailWord_2282563
  simp only [CollatzResearch.WordTrace]
  refine ⟨83251912029671556569500343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55501274686447704379666895 83251912029671556569500343)
  ·
    refine ⟨124877868044507334854250515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83251912029671556569500343 124877868044507334854250515)
    ·
      refine ⟨187316802066761002281375773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124877868044507334854250515 187316802066761002281375773)
      ·
        refine ⟨70243800775035375855515915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187316802066761002281375773 70243800775035375855515915)
        ·
          refine ⟨105365701162553063783273873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70243800775035375855515915 105365701162553063783273873)
          ·
            refine ⟨79024275871914797837455405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105365701162553063783273873 79024275871914797837455405)
            ·
              refine ⟨29634103451968049189045777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79024275871914797837455405 29634103451968049189045777)
              ·
                refine ⟨22225577588976036891784333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29634103451968049189045777 22225577588976036891784333)
                ·
                  refine ⟨8334591595866013834419125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22225577588976036891784333 8334591595866013834419125)
                  ·
                    refine ⟨781367962112438796976793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8334591595866013834419125 781367962112438796976793)
                    ·
                      rfl

theorem cell22_2282563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_2282563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282563 prefixEnd_2282563 := by exact prefixLift 2282563
  have htrace : WordTrace (prefixWord ++ tailWord_2282563) baseStart_2282563 baseEnd_2282563 := by
    simpa [prefixWord, tailWord_2282563, baseEnd_2282563] using wordTrace_append hprefix tailTrace_2282563
  have hstable : (prefixWord ++ tailWord_2282563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282563).length < 2 ^ (prefixWord ++ tailWord_2282563).sum := by decide
  have hdescent : baseEnd_2282563 < baseStart_2282563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
