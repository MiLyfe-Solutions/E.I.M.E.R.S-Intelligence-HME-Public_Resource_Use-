import V185TrunkScan21Chunk140

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1719322 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1719322 : Nat := 118140960795 + 1719322 * 2 ^ 59
def prefixEnd_1719322 : Nat := 4983230072969 + 3 ^ 40 * 1719322 * 2
def baseEnd_1719322 : Nat := 392372704822056612652439

theorem tailTrace_1719322 : CollatzResearch.WordTrace tailWord_1719322 prefixEnd_1719322 392372704822056612652439 := by
  unfold tailWord_1719322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677206269299376416272055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41805883384798337110058813 15677206269299376416272055)
  ·
    refine ⟨23515809403949064624408083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677206269299376416272055 23515809403949064624408083)
    ·
      refine ⟨35273714105923596936612125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23515809403949064624408083 35273714105923596936612125)
      ·
        refine ⟨13227642789721348851229547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35273714105923596936612125 13227642789721348851229547)
        ·
          refine ⟨19841464184582023276844321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227642789721348851229547 19841464184582023276844321)
          ·
            refine ⟨14881098138436517457633241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19841464184582023276844321 14881098138436517457633241)
            ·
              refine ⟨11160823603827388093224931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14881098138436517457633241 11160823603827388093224931)
              ·
                refine ⟨16741235405741082139837397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11160823603827388093224931 16741235405741082139837397)
                ·
                  refine ⟨392372704822056612652439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16741235405741082139837397 392372704822056612652439)
                  ·
                    rfl

theorem cell21_1719322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1719322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719322 prefixEnd_1719322 := by exact prefixLift 1719322
  have htrace : WordTrace (prefixWord ++ tailWord_1719322) baseStart_1719322 baseEnd_1719322 := by
    simpa [prefixWord, tailWord_1719322, baseEnd_1719322] using wordTrace_append hprefix tailTrace_1719322
  have hstable : (prefixWord ++ tailWord_1719322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719322).length < 2 ^ (prefixWord ++ tailWord_1719322).sum := by decide
  have hdescent : baseEnd_1719322 < baseStart_1719322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719339 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 3]
def baseStart_1719339 : Nat := 118140960795 + 1719339 * 2 ^ 59
def prefixEnd_1719339 : Nat := 4983230072969 + 3 ^ 40 * 1719339 * 2
def baseEnd_1719339 : Nat := 392376584453668360869071

theorem tailTrace_1719339 : CollatzResearch.WordTrace tailWord_1719339 prefixEnd_1719339 392376584453668360869071 := by
  unfold tailWord_1719339
  simp only [CollatzResearch.WordTrace]
  refine ⟨62709445118135917568457071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41806296745423945045638047 62709445118135917568457071)
  ·
    refine ⟨94064167677203876352685607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62709445118135917568457071 94064167677203876352685607)
    ·
      refine ⟨141096251515805814529028411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94064167677203876352685607 141096251515805814529028411)
      ·
        refine ⟨211644377273708721793542617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141096251515805814529028411 211644377273708721793542617)
        ·
          refine ⟨158733282955281541345156963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211644377273708721793542617 158733282955281541345156963)
          ·
            refine ⟨238099924432922312017735445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158733282955281541345156963 238099924432922312017735445)
            ·
              refine ⟨11160933957793233375831349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238099924432922312017735445 11160933957793233375831349)
              ·
                refine ⟨1046337558543115628984189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11160933957793233375831349 1046337558543115628984189)
                ·
                  refine ⟨392376584453668360869071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046337558543115628984189 392376584453668360869071)
                  ·
                    rfl

theorem cell21_1719339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].length) (baseStart_1719339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719339 prefixEnd_1719339 := by exact prefixLift 1719339
  have htrace : WordTrace (prefixWord ++ tailWord_1719339) baseStart_1719339 baseEnd_1719339 := by
    simpa [prefixWord, tailWord_1719339, baseEnd_1719339] using wordTrace_append hprefix tailTrace_1719339
  have hstable : (prefixWord ++ tailWord_1719339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719339).length < 2 ^ (prefixWord ++ tailWord_1719339).sum := by decide
  have hdescent : baseEnd_1719339 < baseStart_1719339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719356 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_1719356 : Nat := 118140960795 + 1719356 * 2 ^ 59
def prefixEnd_1719356 : Nat := 4983230072969 + 3 ^ 40 * 1719356 * 2
def baseEnd_1719356 : Nat := 392380464085280109085703

theorem tailTrace_1719356 : CollatzResearch.WordTrace tailWord_1719356 prefixEnd_1719356 392380464085280109085703 := by
  unfold tailWord_1719356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355032579537164735912961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41806710106049552981217281 31355032579537164735912961)
  ·
    refine ⟨23516274434652873551934721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31355032579537164735912961 23516274434652873551934721)
    ·
      refine ⟨17637205825989655163951041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23516274434652873551934721 17637205825989655163951041)
      ·
        refine ⟨13227904369492241372963281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17637205825989655163951041 13227904369492241372963281)
        ·
          refine ⟨9920928277119181029722461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13227904369492241372963281 9920928277119181029722461)
          ·
            refine ⟨3720348103919692886145923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9920928277119181029722461 3720348103919692886145923)
            ·
              refine ⟨5580522155879539329218885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720348103919692886145923 5580522155879539329218885)
              ·
                refine ⟨1046347904227413624228541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5580522155879539329218885 1046347904227413624228541)
                ·
                  refine ⟨392380464085280109085703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046347904227413624228541 392380464085280109085703)
                  ·
                    rfl

theorem cell21_1719356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_1719356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719356 prefixEnd_1719356 := by exact prefixLift 1719356
  have htrace : WordTrace (prefixWord ++ tailWord_1719356) baseStart_1719356 baseEnd_1719356 := by
    simpa [prefixWord, tailWord_1719356, baseEnd_1719356] using wordTrace_append hprefix tailTrace_1719356
  have hstable : (prefixWord ++ tailWord_1719356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719356).length < 2 ^ (prefixWord ++ tailWord_1719356).sum := by decide
  have hdescent : baseEnd_1719356 < baseStart_1719356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719384 : List Nat := [2, 1, 2, 2, 1, 3, 5, 5]
def baseStart_1719384 : Nat := 118140960795 + 1719384 * 2 ^ 59
def prefixEnd_1719384 : Nat := 4983230072969 + 3 ^ 40 * 1719384 * 2
def baseEnd_1719384 : Nat := 130795618022252760872993

theorem tailTrace_1719384 : CollatzResearch.WordTrace tailWord_1719384 prefixEnd_1719384 130795618022252760872993 := by
  unfold tailWord_1719384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355543201486445126922603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41807390935315260169230137 31355543201486445126922603)
  ·
    refine ⟨47033314802229667690383905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31355543201486445126922603 47033314802229667690383905)
    ·
      refine ⟨35274986101672250767787929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47033314802229667690383905 35274986101672250767787929)
      ·
        refine ⟨26456239576254188075840947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35274986101672250767787929 26456239576254188075840947)
        ·
          refine ⟨39684359364381282113761421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26456239576254188075840947 39684359364381282113761421)
          ·
            refine ⟨14881634761642980792660533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39684359364381282113761421 14881634761642980792660533)
            ·
              refine ⟨1395153258904029449311925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14881634761642980792660533 1395153258904029449311925)
              ·
                refine ⟨130795618022252760872993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395153258904029449311925 130795618022252760872993)
                ·
                  rfl

theorem cell21_1719384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_1719384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719384 prefixEnd_1719384 := by exact prefixLift 1719384
  have htrace : WordTrace (prefixWord ++ tailWord_1719384) baseStart_1719384 baseEnd_1719384 := by
    simpa [prefixWord, tailWord_1719384, baseEnd_1719384] using wordTrace_append hprefix tailTrace_1719384
  have hstable : (prefixWord ++ tailWord_1719384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719384).length < 2 ^ (prefixWord ++ tailWord_1719384).sum := by decide
  have hdescent : baseEnd_1719384 < baseStart_1719384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719390 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1719390 : Nat := 118140960795 + 1719390 * 2 ^ 59
def prefixEnd_1719390 : Nat := 4983230072969 + 3 ^ 40 * 1719390 * 2
def baseEnd_1719390 : Nat := 392388223348503605518967

theorem tailTrace_1719390 : CollatzResearch.WordTrace tailWord_1719390 prefixEnd_1719390 392388223348503605518967 := by
  unfold tailWord_1719390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838913155118894159820453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41807536827300768852375749 7838913155118894159820453)
  ·
    refine ⟨1469796216584792654966335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7838913155118894159820453 1469796216584792654966335)
    ·
      refine ⟨2204694324877188982449503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469796216584792654966335 2204694324877188982449503)
      ·
        refine ⟨3307041487315783473674255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204694324877188982449503 3307041487315783473674255)
        ·
          refine ⟨4960562230973675210511383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307041487315783473674255 4960562230973675210511383)
          ·
            refine ⟨7440843346460512815767075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960562230973675210511383 7440843346460512815767075)
            ·
              refine ⟨11161265019690769223650613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440843346460512815767075 11161265019690769223650613)
              ·
                refine ⟨1046368595596009614717245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11161265019690769223650613 1046368595596009614717245)
                ·
                  refine ⟨392388223348503605518967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046368595596009614717245 392388223348503605518967)
                  ·
                    rfl

theorem cell21_1719390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1719390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719390 prefixEnd_1719390 := by exact prefixLift 1719390
  have htrace : WordTrace (prefixWord ++ tailWord_1719390) baseStart_1719390 baseEnd_1719390 := by
    simpa [prefixWord, tailWord_1719390, baseEnd_1719390] using wordTrace_append hprefix tailTrace_1719390
  have hstable : (prefixWord ++ tailWord_1719390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719390).length < 2 ^ (prefixWord ++ tailWord_1719390).sum := by decide
  have hdescent : baseEnd_1719390 < baseStart_1719390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719415 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 3]
def baseStart_1719415 : Nat := 118140960795 + 1719415 * 2 ^ 59
def prefixEnd_1719415 : Nat := 4983230072969 + 3 ^ 40 * 1719415 * 2
def baseEnd_1719415 : Nat := 392393928689109117602249

theorem tailTrace_1719415 : CollatzResearch.WordTrace tailWord_1719415 prefixEnd_1719415 392393928689109117602249 := by
  unfold tailWord_1719415
  simp only [CollatzResearch.WordTrace]
  refine ⟨62712217065860582548223699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41808144710573721698815799 62712217065860582548223699)
  ·
    refine ⟨94068325598790873822335549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62712217065860582548223699 94068325598790873822335549)
    ·
      refine ⟨35275622099546577683375831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94068325598790873822335549 35275622099546577683375831)
      ·
        refine ⟨52913433149319866525063747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35275622099546577683375831 52913433149319866525063747)
        ·
          refine ⟨79370149723979799787595621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52913433149319866525063747 79370149723979799787595621)
          ·
            refine ⟨14881903073246212460174179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79370149723979799787595621 14881903073246212460174179)
            ·
              refine ⟨22322854609869318690261269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881903073246212460174179 22322854609869318690261269)
              ·
                refine ⟨1046383809837624313605997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22322854609869318690261269 1046383809837624313605997)
                ·
                  refine ⟨392393928689109117602249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046383809837624313605997 392393928689109117602249)
                  ·
                    rfl

theorem cell21_1719415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].length) (baseStart_1719415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719415 prefixEnd_1719415 := by exact prefixLift 1719415
  have htrace : WordTrace (prefixWord ++ tailWord_1719415) baseStart_1719415 baseEnd_1719415 := by
    simpa [prefixWord, tailWord_1719415, baseEnd_1719415] using wordTrace_append hprefix tailTrace_1719415
  have hstable : (prefixWord ++ tailWord_1719415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719415).length < 2 ^ (prefixWord ++ tailWord_1719415).sum := by decide
  have hdescent : baseEnd_1719415 < baseStart_1719415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719460 : List Nat := [2, 3, 1, 2, 3, 3, 7]
def baseStart_1719460 : Nat := 118140960795 + 1719460 * 2 ^ 59
def prefixEnd_1719460 : Nat := 4983230072969 + 3 ^ 40 * 1719460 * 2
def baseEnd_1719460 : Nat := 43600466478022115483573

theorem tailTrace_1719460 : CollatzResearch.WordTrace tailWord_1719460 prefixEnd_1719460 43600466478022115483573 := by
  unfold tailWord_1719460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356929175348777616805917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41809238900465036822407889 31356929175348777616805917)
  ·
    refine ⟨11758848440755791606302219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31356929175348777616805917 11758848440755791606302219)
    ·
      refine ⟨17638272661133687409453329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11758848440755791606302219 17638272661133687409453329)
      ·
        refine ⟨13228704495850265557089997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17638272661133687409453329 13228704495850265557089997)
        ·
          refine ⟨4960764185943849583908749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13228704495850265557089997 4960764185943849583908749)
          ·
            refine ⟨1860286569728943593965781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4960764185943849583908749 1860286569728943593965781)
            ·
              refine ⟨43600466478022115483573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1860286569728943593965781 43600466478022115483573)
              ·
                rfl

theorem cell21_1719460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 7].length) (baseStart_1719460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719460 prefixEnd_1719460 := by exact prefixLift 1719460
  have htrace : WordTrace (prefixWord ++ tailWord_1719460) baseStart_1719460 baseEnd_1719460 := by
    simpa [prefixWord, tailWord_1719460, baseEnd_1719460] using wordTrace_append hprefix tailTrace_1719460
  have hstable : (prefixWord ++ tailWord_1719460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719460).length < 2 ^ (prefixWord ++ tailWord_1719460).sum := by decide
  have hdescent : baseEnd_1719460 < baseStart_1719460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719466 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1719466 : Nat := 118140960795 + 1719466 * 2 ^ 59
def prefixEnd_1719466 : Nat := 4983230072969 + 3 ^ 40 * 1719466 * 2
def baseEnd_1719466 : Nat := 392405567583944362252145

theorem tailTrace_1719466 : CollatzResearch.WordTrace tailWord_1719466 prefixEnd_1719466 392405567583944362252145 := by
  unfold tailWord_1719466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678519297168954564582563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41809384792450545505553501 15678519297168954564582563)
  ·
    refine ⟨23517778945753431846873845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15678519297168954564582563 23517778945753431846873845)
    ·
      refine ⟨2204791776164384235644423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23517778945753431846873845 2204791776164384235644423)
      ·
        refine ⟨3307187664246576353466635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204791776164384235644423 3307187664246576353466635)
        ·
          refine ⟨4960781496369864530199953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307187664246576353466635 4960781496369864530199953)
          ·
            refine ⟨3720586122277398397649965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960781496369864530199953 3720586122277398397649965)
            ·
              refine ⟨1395219795854024399118737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720586122277398397649965 1395219795854024399118737)
              ·
                refine ⟨1046414846890518299339053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395219795854024399118737 1046414846890518299339053)
                ·
                  refine ⟨392405567583944362252145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046414846890518299339053 392405567583944362252145)
                  ·
                    rfl

theorem cell21_1719466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1719466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719466 prefixEnd_1719466 := by exact prefixLift 1719466
  have htrace : WordTrace (prefixWord ++ tailWord_1719466) baseStart_1719466 baseEnd_1719466 := by
    simpa [prefixWord, tailWord_1719466, baseEnd_1719466] using wordTrace_append hprefix tailTrace_1719466
  have hstable : (prefixWord ++ tailWord_1719466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719466).length < 2 ^ (prefixWord ++ tailWord_1719466).sum := by decide
  have hdescent : baseEnd_1719466 < baseStart_1719466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719612 : List Nat := [2, 2, 2, 2, 1, 3, 4, 5]
def baseStart_1719612 : Nat := 118140960795 + 1719612 * 2 ^ 59
def prefixEnd_1719612 : Nat := 4983230072969 + 3 ^ 40 * 1719612 * 2
def baseEnd_1719612 : Nat := 130812962257693517606171

theorem tailTrace_1719612 : CollatzResearch.WordTrace tailWord_1719612 prefixEnd_1719612 130812962257693517606171 := by
  unfold tailWord_1719612
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359701123073442596572545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41812934830764590128763393 31359701123073442596572545)
  ·
    refine ⟨23519775842305081947429409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31359701123073442596572545 23519775842305081947429409)
    ·
      refine ⟨17639831881728811460572057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23519775842305081947429409 17639831881728811460572057)
      ·
        refine ⟨13229873911296608595429043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17639831881728811460572057 13229873911296608595429043)
        ·
          refine ⟨19844810866944912893143565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229873911296608595429043 19844810866944912893143565)
          ·
            refine ⟨7441804075104342334928837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19844810866944912893143565 7441804075104342334928837)
            ·
              refine ⟨1395338264082064187799157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7441804075104342334928837 1395338264082064187799157)
              ·
                refine ⟨130812962257693517606171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395338264082064187799157 130812962257693517606171)
                ·
                  rfl

theorem cell21_1719612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_1719612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719612 prefixEnd_1719612 := by exact prefixLift 1719612
  have htrace : WordTrace (prefixWord ++ tailWord_1719612) baseStart_1719612 baseEnd_1719612 := by
    simpa [prefixWord, tailWord_1719612, baseEnd_1719612] using wordTrace_append hprefix tailTrace_1719612
  have hstable : (prefixWord ++ tailWord_1719612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719612).length < 2 ^ (prefixWord ++ tailWord_1719612).sum := by decide
  have hdescent : baseEnd_1719612 < baseStart_1719612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719640 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_1719640 : Nat := 118140960795 + 1719640 * 2 ^ 59
def prefixEnd_1719640 : Nat := 4983230072969 + 3 ^ 40 * 1719640 * 2
def baseEnd_1719640 : Nat := 392445276754558726351789

theorem tailTrace_1719640 : CollatzResearch.WordTrace tailWord_1719640 prefixEnd_1719640 392445276754558726351789 := by
  unfold tailWord_1719640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360211745022722987582187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41813615660030297316776249 31360211745022722987582187)
  ·
    refine ⟨47040317617534084481373281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31360211745022722987582187 47040317617534084481373281)
    ·
      refine ⟨35280238213150563361029961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47040317617534084481373281 35280238213150563361029961)
      ·
        refine ⟨26460178659862922520772471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35280238213150563361029961 26460178659862922520772471)
        ·
          refine ⟨39690267989794383781158707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26460178659862922520772471 39690267989794383781158707)
          ·
            refine ⟨59535401984691575671738061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39690267989794383781158707 59535401984691575671738061)
            ·
              refine ⟨22325775744259340876901773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59535401984691575671738061 22325775744259340876901773)
              ·
                refine ⟨8372165904097252828838165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22325775744259340876901773 8372165904097252828838165)
                ·
                  refine ⟨392445276754558726351789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8372165904097252828838165 392445276754558726351789)
                  ·
                    rfl

theorem cell21_1719640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1719640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719640 prefixEnd_1719640 := by exact prefixLift 1719640
  have htrace : WordTrace (prefixWord ++ tailWord_1719640) baseStart_1719640 baseEnd_1719640 := by
    simpa [prefixWord, tailWord_1719640, baseEnd_1719640] using wordTrace_append hprefix tailTrace_1719640
  have hstable : (prefixWord ++ tailWord_1719640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719640).length < 2 ^ (prefixWord ++ tailWord_1719640).sum := by decide
  have hdescent : baseEnd_1719640 < baseStart_1719640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719694 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1719694 : Nat := 118140960795 + 1719694 * 2 ^ 59
def prefixEnd_1719694 : Nat := 4983230072969 + 3 ^ 40 * 1719694 * 2
def baseEnd_1719694 : Nat := 392457600290266632451679

theorem tailTrace_1719694 : CollatzResearch.WordTrace tailWord_1719694 prefixEnd_1719694 392457600290266632451679 := by
  unfold tailWord_1719694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840299128981226649703767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41814928687899875465086757 7840299128981226649703767)
  ·
    refine ⟨11760448693471839974555651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7840299128981226649703767 11760448693471839974555651)
    ·
      refine ⟨17640673040207759961833477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760448693471839974555651 17640673040207759961833477)
      ·
        refine ⟨3307626195038954992843777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17640673040207759961833477 3307626195038954992843777)
        ·
          refine ⟨2480719646279216244632833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307626195038954992843777 2480719646279216244632833)
          ·
            refine ⟨1860539734709412183474625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2480719646279216244632833 1860539734709412183474625)
            ·
              refine ⟨1395404801032059137605969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860539734709412183474625 1395404801032059137605969)
              ·
                refine ⟨1046553600774044353204477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395404801032059137605969 1046553600774044353204477)
                ·
                  refine ⟨392457600290266632451679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046553600774044353204477 392457600290266632451679)
                  ·
                    rfl

theorem cell21_1719694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1719694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719694 prefixEnd_1719694 := by exact prefixLift 1719694
  have htrace : WordTrace (prefixWord ++ tailWord_1719694) baseStart_1719694 baseEnd_1719694 := by
    simpa [prefixWord, tailWord_1719694, baseEnd_1719694] using wordTrace_append hprefix tailTrace_1719694
  have hstable : (prefixWord ++ tailWord_1719694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719694).length < 2 ^ (prefixWord ++ tailWord_1719694).sum := by decide
  have hdescent : baseEnd_1719694 < baseStart_1719694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719716 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1719716 : Nat := 118140960795 + 1719716 * 2 ^ 59
def prefixEnd_1719716 : Nat := 4983230072969 + 3 ^ 40 * 1719716 * 2
def baseEnd_1719716 : Nat := 392462620989999483084967

theorem tailTrace_1719716 : CollatzResearch.WordTrace tailWord_1719716 prefixEnd_1719716 392462620989999483084967 := by
  unfold tailWord_1719716
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361597718885055477465501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41815463625180073969954001 31361597718885055477465501)
  ·
    refine ⟨11760599144581895804049563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31361597718885055477465501 11760599144581895804049563)
    ·
      refine ⟨17640898716872843706074345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760599144581895804049563 17640898716872843706074345)
      ·
        refine ⟨13230674037654632779555759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17640898716872843706074345 13230674037654632779555759)
        ·
          refine ⟨19846011056481949169333639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13230674037654632779555759 19846011056481949169333639)
          ·
            refine ⟨29769016584722923754000459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846011056481949169333639 29769016584722923754000459)
            ·
              refine ⟨44653524877084385631000689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29769016584722923754000459 44653524877084385631000689)
              ·
                refine ⟨33490143657813289223250517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44653524877084385631000689 33490143657813289223250517)
                ·
                  refine ⟨392462620989999483084967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33490143657813289223250517 392462620989999483084967)
                  ·
                    rfl

theorem cell21_1719716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1719716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719716 prefixEnd_1719716 := by exact prefixLift 1719716
  have htrace : WordTrace (prefixWord ++ tailWord_1719716) baseStart_1719716 baseEnd_1719716 := by
    simpa [prefixWord, tailWord_1719716, baseEnd_1719716] using wordTrace_append hprefix tailTrace_1719716
  have hstable : (prefixWord ++ tailWord_1719716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719716).length < 2 ^ (prefixWord ++ tailWord_1719716).sum := by decide
  have hdescent : baseEnd_1719716 < baseStart_1719716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719781 : List Nat := [1, 3, 1, 5, 1, 3, 2, 5]
def baseStart_1719781 : Nat := 118140960795 + 1719781 * 2 ^ 59
def prefixEnd_1719781 : Nat := 4983230072969 + 3 ^ 40 * 1719781 * 2
def baseEnd_1719781 : Nat := 130825818291857938167167

theorem tailTrace_1719781 : CollatzResearch.WordTrace tailWord_1719781 prefixEnd_1719781 130825818291857938167167 := by
  unfold tailWord_1719781
  simp only [CollatzResearch.WordTrace]
  refine ⟨62725566182534627056047197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41817044121689751370698131 62725566182534627056047197)
  ·
    refine ⟨23522087318450485146017699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62725566182534627056047197 23522087318450485146017699)
    ·
      refine ⟨35283130977675727719026549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23522087318450485146017699 35283130977675727719026549)
      ·
        refine ⟨3307793529157099473658739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35283130977675727719026549 3307793529157099473658739)
        ·
          refine ⟨4961690293735649210488109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307793529157099473658739 4961690293735649210488109)
          ·
            refine ⟨1860633860150868453933041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961690293735649210488109 1860633860150868453933041)
            ·
              refine ⟨1395475395113151340449781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860633860150868453933041 1395475395113151340449781)
              ·
                refine ⟨130825818291857938167167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395475395113151340449781 130825818291857938167167)
                ·
                  rfl

theorem cell21_1719781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].length) (baseStart_1719781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719781 prefixEnd_1719781 := by exact prefixLift 1719781
  have htrace : WordTrace (prefixWord ++ tailWord_1719781) baseStart_1719781 baseEnd_1719781 := by
    simpa [prefixWord, tailWord_1719781, baseEnd_1719781] using wordTrace_append hprefix tailTrace_1719781
  have hstable : (prefixWord ++ tailWord_1719781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719781).length < 2 ^ (prefixWord ++ tailWord_1719781).sum := by decide
  have hdescent : baseEnd_1719781 < baseStart_1719781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719792 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1719792 : Nat := 118140960795 + 1719792 * 2 ^ 59
def prefixEnd_1719792 : Nat := 4983230072969 + 3 ^ 40 * 1719792 * 2
def baseEnd_1719792 : Nat := 392479965225440239818145

theorem tailTrace_1719792 : CollatzResearch.WordTrace tailWord_1719792 prefixEnd_1719792 392479965225440239818145 := by
  unfold tailWord_1719792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362983692747387967348815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41817311590329850623131753 31362983692747387967348815)
  ·
    refine ⟨47044475539121081951023223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362983692747387967348815 47044475539121081951023223)
    ·
      refine ⟨70566713308681622926534835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47044475539121081951023223 70566713308681622926534835)
      ·
        refine ⟨105850069963022434389802253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70566713308681622926534835 105850069963022434389802253)
        ·
          refine ⟨39693776236133412896175845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105850069963022434389802253 39693776236133412896175845)
          ·
            refine ⟨7442583044275014918032971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39693776236133412896175845 7442583044275014918032971)
            ·
              refine ⟨11163874566412522377049457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442583044275014918032971 11163874566412522377049457)
              ·
                refine ⟨8372905924809391782787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11163874566412522377049457 8372905924809391782787093)
                ·
                  refine ⟨392479965225440239818145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8372905924809391782787093 392479965225440239818145)
                  ·
                    rfl

theorem cell21_1719792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1719792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719792 prefixEnd_1719792 := by exact prefixLift 1719792
  have htrace : WordTrace (prefixWord ++ tailWord_1719792) baseStart_1719792 baseEnd_1719792 := by
    simpa [prefixWord, tailWord_1719792, baseEnd_1719792] using wordTrace_append hprefix tailTrace_1719792
  have hstable : (prefixWord ++ tailWord_1719792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719792).length < 2 ^ (prefixWord ++ tailWord_1719792).sum := by decide
  have hdescent : baseEnd_1719792 < baseStart_1719792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719812 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1719812 : Nat := 118140960795 + 1719812 * 2 ^ 59
def prefixEnd_1719812 : Nat := 4983230072969 + 3 ^ 40 * 1719812 * 2
def baseEnd_1719812 : Nat := 392484529497924649484771

theorem tailTrace_1719812 : CollatzResearch.WordTrace tailWord_1719812 prefixEnd_1719812 392484529497924649484771 := by
  unfold tailWord_1719812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31363348422711159675212845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41817797896948212900283793 31363348422711159675212845)
  ·
    refine ⟨11761255658516684878204817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31363348422711159675212845 11761255658516684878204817)
    ·
      refine ⟨8820941743887513658653613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761255658516684878204817 8820941743887513658653613)
      ·
        refine ⟨3307853153957817621995105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8820941743887513658653613 3307853153957817621995105)
        ·
          refine ⟨2480889865468363216496329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307853153957817621995105 2480889865468363216496329)
          ·
            refine ⟨1860667399101272412372247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2480889865468363216496329 1860667399101272412372247)
            ·
              refine ⟨2791001098651908618558371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860667399101272412372247 2791001098651908618558371)
              ·
                refine ⟨4186501647977862927837557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791001098651908618558371 4186501647977862927837557)
                ·
                  refine ⟨392484529497924649484771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186501647977862927837557 392484529497924649484771)
                  ·
                    rfl

theorem cell21_1719812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1719812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719812 prefixEnd_1719812 := by exact prefixLift 1719812
  have htrace : WordTrace (prefixWord ++ tailWord_1719812) baseStart_1719812 baseEnd_1719812 := by
    simpa [prefixWord, tailWord_1719812, baseEnd_1719812] using wordTrace_append hprefix tailTrace_1719812
  have hstable : (prefixWord ++ tailWord_1719812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719812).length < 2 ^ (prefixWord ++ tailWord_1719812).sum := by decide
  have hdescent : baseEnd_1719812 < baseStart_1719812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719871 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 3]
def baseStart_1719871 : Nat := 118140960795 + 1719871 * 2 ^ 59
def prefixEnd_1719871 : Nat := 4983230072969 + 3 ^ 40 * 1719871 * 2
def baseEnd_1719871 : Nat := 392497994101753658001317

theorem tailTrace_1719871 : CollatzResearch.WordTrace tailWord_1719871 prefixEnd_1719871 392497994101753658001317 := by
  unfold tailWord_1719871
  simp only [CollatzResearch.WordTrace]
  refine ⟨62728848752208572426823467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41819232501472381617882311 62728848752208572426823467)
  ·
    refine ⟨94093273128312858640235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62728848752208572426823467 94093273128312858640235201)
    ·
      refine ⟨70569954846234643980176401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94093273128312858640235201 70569954846234643980176401)
      ·
        refine ⟨52927466134675982985132301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70569954846234643980176401 52927466134675982985132301)
        ·
          refine ⟨19847799800503493619424613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52927466134675982985132301 19847799800503493619424613)
          ·
            refine ⟨3721462462594405053642115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19847799800503493619424613 3721462462594405053642115)
            ·
              refine ⟨5582193693891607580463173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721462462594405053642115 5582193693891607580463173)
              ·
                refine ⟨1046661317604676421336845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5582193693891607580463173 1046661317604676421336845)
                ·
                  refine ⟨392497994101753658001317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046661317604676421336845 392497994101753658001317)
                  ·
                    rfl

theorem cell21_1719871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].length) (baseStart_1719871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719871 prefixEnd_1719871 := by exact prefixLift 1719871
  have htrace : WordTrace (prefixWord ++ tailWord_1719871) baseStart_1719871 baseEnd_1719871 := by
    simpa [prefixWord, tailWord_1719871, baseEnd_1719871] using wordTrace_append hprefix tailTrace_1719871
  have hstable : (prefixWord ++ tailWord_1719871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719871).length < 2 ^ (prefixWord ++ tailWord_1719871).sum := by decide
  have hdescent : baseEnd_1719871 < baseStart_1719871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720034 : List Nat := [3, 3, 15]
def baseStart_1720034 : Nat := 118140960795 + 1720034 * 2 ^ 59
def prefixEnd_1720034 : Nat := 4983230072969 + 3 ^ 40 * 1720034 * 2
def baseEnd_1720034 : Nat := 538457054763376675973

theorem tailTrace_1720034 : CollatzResearch.WordTrace tailWord_1720034 prefixEnd_1720034 538457054763376675973 := by
  unfold tailWord_1720034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683698462654512816251789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41823195900412034176671437 15683698462654512816251789)
  ·
    refine ⟨5881386923495442306094421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15683698462654512816251789 5881386923495442306094421)
    ·
      refine ⟨538457054763376675973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 5881386923495442306094421 538457054763376675973)
      ·
        rfl

theorem cell21_1720034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 15].length) (baseStart_1720034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720034 prefixEnd_1720034 := by exact prefixLift 1720034
  have htrace : WordTrace (prefixWord ++ tailWord_1720034) baseStart_1720034 baseEnd_1720034 := by
    simpa [prefixWord, tailWord_1720034, baseEnd_1720034] using wordTrace_append hprefix tailTrace_1720034
  have hstable : (prefixWord ++ tailWord_1720034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720034).length < 2 ^ (prefixWord ++ tailWord_1720034).sum := by decide
  have hdescent : baseEnd_1720034 < baseStart_1720034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720037 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1720037 : Nat := 118140960795 + 1720037 * 2 ^ 59
def prefixEnd_1720037 : Nat := 4983230072969 + 3 ^ 40 * 1720037 * 2
def baseEnd_1720037 : Nat := 392535877563374258234311

theorem tailTrace_1720037 : CollatzResearch.WordTrace tailWord_1720037 prefixEnd_1720037 392535877563374258234311 := by
  unfold tailWord_1720037
  simp only [CollatzResearch.WordTrace]
  refine ⟨62734903269607182777366365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41823268846404788518244243 62734903269607182777366365)
  ·
    refine ⟨23525588726102693541512387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62734903269607182777366365 23525588726102693541512387)
    ·
      refine ⟨35288383089154040312268581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23525588726102693541512387 35288383089154040312268581)
      ·
        refine ⟨6616571829216382558550359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35288383089154040312268581 6616571829216382558550359)
        ·
          refine ⟨9924857743824573837825539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616571829216382558550359 9924857743824573837825539)
          ·
            refine ⟨14887286615736860756738309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9924857743824573837825539 14887286615736860756738309)
            ·
              refine ⟨2791366240450661391888433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14887286615736860756738309 2791366240450661391888433)
              ·
                refine ⟨2093524680337996043916325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791366240450661391888433 2093524680337996043916325)
                ·
                  refine ⟨392535877563374258234311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093524680337996043916325 392535877563374258234311)
                  ·
                    rfl

theorem cell21_1720037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1720037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720037 prefixEnd_1720037 := by exact prefixLift 1720037
  have htrace : WordTrace (prefixWord ++ tailWord_1720037) baseStart_1720037 baseEnd_1720037 := by
    simpa [prefixWord, tailWord_1720037, baseEnd_1720037] using wordTrace_append hprefix tailTrace_1720037
  have hstable : (prefixWord ++ tailWord_1720037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720037).length < 2 ^ (prefixWord ++ tailWord_1720037).sum := by decide
  have hdescent : baseEnd_1720037 < baseStart_1720037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720040 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_1720040 : Nat := 118140960795 + 1720040 * 2 ^ 59
def prefixEnd_1720040 : Nat := 4983230072969 + 3 ^ 40 * 1720040 * 2
def baseEnd_1720040 : Nat := 392536562204246919684305

theorem tailTrace_1720040 : CollatzResearch.WordTrace tailWord_1720040 prefixEnd_1720040 392536562204246919684305 := by
  unfold tailWord_1720040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31367506344298157144862787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41823341792397542859817049 31367506344298157144862787)
  ·
    refine ⟨47051259516447235717294181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31367506344298157144862787 47051259516447235717294181)
    ·
      refine ⟨8822111159333856696992659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47051259516447235717294181 8822111159333856696992659)
      ·
        refine ⟨13233166739000785045488989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822111159333856696992659 13233166739000785045488989)
        ·
          refine ⟨4962437527125294392058371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13233166739000785045488989 4962437527125294392058371)
          ·
            refine ⟨7443656290687941588087557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962437527125294392058371 7443656290687941588087557)
            ·
              refine ⟨1395685554503989047766417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7443656290687941588087557 1395685554503989047766417)
              ·
                refine ⟨1046764165877991785824813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395685554503989047766417 1046764165877991785824813)
                ·
                  refine ⟨392536562204246919684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046764165877991785824813 392536562204246919684305)
                  ·
                    rfl

theorem cell21_1720040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_1720040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720040 prefixEnd_1720040 := by exact prefixLift 1720040
  have htrace : WordTrace (prefixWord ++ tailWord_1720040) baseStart_1720040 baseEnd_1720040 := by
    simpa [prefixWord, tailWord_1720040, baseEnd_1720040] using wordTrace_append hprefix tailTrace_1720040
  have hstable : (prefixWord ++ tailWord_1720040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720040).length < 2 ^ (prefixWord ++ tailWord_1720040).sum := by decide
  have hdescent : baseEnd_1720040 < baseStart_1720040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720065 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1720065 : Nat := 118140960795 + 1720065 * 2 ^ 59
def prefixEnd_1720065 : Nat := 4983230072969 + 3 ^ 40 * 1720065 * 2
def baseEnd_1720065 : Nat := 392542267544852431767587

theorem tailTrace_1720065 : CollatzResearch.WordTrace tailWord_1720065 prefixEnd_1720065 392542267544852431767587 := by
  unfold tailWord_1720065
  simp only [CollatzResearch.WordTrace]
  refine ⟨62735924513505743559385649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41823949675670495706257099 62735924513505743559385649)
  ·
    refine ⟨47051943385129307669539237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62735924513505743559385649 47051943385129307669539237)
    ·
      refine ⟨8822239384711745188038607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47051943385129307669539237 8822239384711745188038607)
      ·
        refine ⟨13233359077067617782057911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822239384711745188038607 13233359077067617782057911)
        ·
          refine ⟨19850038615601426673086867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233359077067617782057911 19850038615601426673086867)
          ·
            refine ⟨29775057923402140009630301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19850038615601426673086867 29775057923402140009630301)
            ·
              refine ⟨11165646721275802503611363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29775057923402140009630301 11165646721275802503611363)
              ·
                refine ⟨16748470081913703755417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165646721275802503611363 16748470081913703755417045)
                ·
                  refine ⟨392542267544852431767587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16748470081913703755417045 392542267544852431767587)
                  ·
                    rfl

theorem cell21_1720065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1720065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720065 prefixEnd_1720065 := by exact prefixLift 1720065
  have htrace : WordTrace (prefixWord ++ tailWord_1720065) baseStart_1720065 baseEnd_1720065 := by
    simpa [prefixWord, tailWord_1720065, baseEnd_1720065] using wordTrace_append hprefix tailTrace_1720065
  have hstable : (prefixWord ++ tailWord_1720065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720065).length < 2 ^ (prefixWord ++ tailWord_1720065).sum := by decide
  have hdescent : baseEnd_1720065 < baseStart_1720065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720068 : List Nat := [2, 3, 2, 2, 1, 3, 3, 5]
def baseStart_1720068 : Nat := 118140960795 + 1720068 * 2 ^ 59
def prefixEnd_1720068 : Nat := 4983230072969 + 3 ^ 40 * 1720068 * 2
def baseEnd_1720068 : Nat := 130847650728575031072527

theorem tailTrace_1720068 : CollatzResearch.WordTrace tailWord_1720068 prefixEnd_1720068 130847650728575031072527 := by
  unfold tailWord_1720068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31368016966247437535872429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41824022621663250047829905 31368016966247437535872429)
  ·
    refine ⟨11763006362342789075952161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31368016966247437535872429 11763006362342789075952161)
    ·
      refine ⟨8822254771757091806964121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11763006362342789075952161 8822254771757091806964121)
      ·
        refine ⟨6616691078817818855223091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8822254771757091806964121 6616691078817818855223091)
        ·
          refine ⟨9925036618226728282834637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616691078817818855223091 9925036618226728282834637)
          ·
            refine ⟨3721888731835023106062989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9925036618226728282834637 3721888731835023106062989)
            ·
              refine ⟨1395708274438133664773621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3721888731835023106062989 1395708274438133664773621)
              ·
                refine ⟨130847650728575031072527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395708274438133664773621 130847650728575031072527)
                ·
                  rfl

theorem cell21_1720068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_1720068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720068 prefixEnd_1720068 := by exact prefixLift 1720068
  have htrace : WordTrace (prefixWord ++ tailWord_1720068) baseStart_1720068 baseEnd_1720068 := by
    simpa [prefixWord, tailWord_1720068, baseEnd_1720068] using wordTrace_append hprefix tailTrace_1720068
  have hstable : (prefixWord ++ tailWord_1720068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720068).length < 2 ^ (prefixWord ++ tailWord_1720068).sum := by decide
  have hdescent : baseEnd_1720068 < baseStart_1720068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720096 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_1720096 : Nat := 118140960795 + 1720096 * 2 ^ 59
def prefixEnd_1720096 : Nat := 4983230072969 + 3 ^ 40 * 1720096 * 2
def baseEnd_1720096 : Nat := 392549342167203266750857

theorem tailTrace_1720096 : CollatzResearch.WordTrace tailWord_1720096 prefixEnd_1720096 392549342167203266750857 := by
  unfold tailWord_1720096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31368527588196717926882071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41824703450928957235842761 31368527588196717926882071)
  ·
    refine ⟨47052791382295076890323107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31368527588196717926882071 47052791382295076890323107)
    ·
      refine ⟨70579187073442615335484661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47052791382295076890323107 70579187073442615335484661)
      ·
        refine ⟨6616798788135245187701687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70579187073442615335484661 6616798788135245187701687)
        ·
          refine ⟨9925198182202867781552531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616798788135245187701687 9925198182202867781552531)
          ·
            refine ⟨14887797273304301672328797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9925198182202867781552531 14887797273304301672328797)
            ·
              refine ⟨5582923977489113127123299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14887797273304301672328797 5582923977489113127123299)
              ·
                refine ⟨8374385966233669690684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582923977489113127123299 8374385966233669690684949)
                ·
                  refine ⟨392549342167203266750857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8374385966233669690684949 392549342167203266750857)
                  ·
                    rfl

theorem cell21_1720096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_1720096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720096 prefixEnd_1720096 := by exact prefixLift 1720096
  have htrace : WordTrace (prefixWord ++ tailWord_1720096) baseStart_1720096 baseEnd_1720096 := by
    simpa [prefixWord, tailWord_1720096, baseEnd_1720096] using wordTrace_append hprefix tailTrace_1720096
  have hstable : (prefixWord ++ tailWord_1720096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720096).length < 2 ^ (prefixWord ++ tailWord_1720096).sum := by decide
  have hdescent : baseEnd_1720096 < baseStart_1720096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720127 : List Nat := [1, 1, 2, 2, 6, 1, 1, 7]
def baseStart_1720127 : Nat := 118140960795 + 1720127 * 2 ^ 59
def prefixEnd_1720127 : Nat := 4983230072969 + 3 ^ 40 * 1720127 * 2
def baseEnd_1720127 : Nat := 130852138929851367244709

theorem tailTrace_1720127 : CollatzResearch.WordTrace tailWord_1720127 prefixEnd_1720127 130852138929851367244709 := by
  unfold tailWord_1720127
  simp only [CollatzResearch.WordTrace]
  refine ⟨62738185839281128148142635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41825457226187418765428423 62738185839281128148142635)
  ·
    refine ⟨94107278758921692222213953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62738185839281128148142635 94107278758921692222213953)
    ·
      refine ⟨70580459069191269166660465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94107278758921692222213953 70580459069191269166660465)
      ·
        refine ⟨52935344301893451874995349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70580459069191269166660465 52935344301893451874995349)
        ·
          refine ⟨2481344264151255556640407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52935344301893451874995349 2481344264151255556640407)
          ·
            refine ⟨3722016396226883334960611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481344264151255556640407 3722016396226883334960611)
            ·
              refine ⟨5583024594340325002440917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722016396226883334960611 5583024594340325002440917)
              ·
                refine ⟨130852138929851367244709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5583024594340325002440917 130852138929851367244709)
                ·
                  rfl

theorem cell21_1720127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_1720127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720127 prefixEnd_1720127 := by exact prefixLift 1720127
  have htrace : WordTrace (prefixWord ++ tailWord_1720127) baseStart_1720127 baseEnd_1720127 := by
    simpa [prefixWord, tailWord_1720127, baseEnd_1720127] using wordTrace_append hprefix tailTrace_1720127
  have hstable : (prefixWord ++ tailWord_1720127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720127).length < 2 ^ (prefixWord ++ tailWord_1720127).sum := by decide
  have hdescent : baseEnd_1720127 < baseStart_1720127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720186 : List Nat := [3, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1720186 : Nat := 118140960795 + 1720186 * 2 ^ 59
def prefixEnd_1720186 : Nat := 4983230072969 + 3 ^ 40 * 1720186 * 2
def baseEnd_1720186 : Nat := 130856627131127703416891

theorem tailTrace_1720186 : CollatzResearch.WordTrace tailWord_1720186 prefixEnd_1720186 130856627131127703416891 := by
  unfold tailWord_1720186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685084436516845306135103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41826891830711587483026941 15685084436516845306135103)
  ·
    refine ⟨23527626654775267959202655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685084436516845306135103 23527626654775267959202655)
    ·
      refine ⟨35291439982162901938803983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23527626654775267959202655 35291439982162901938803983)
      ·
        refine ⟨52937159973244352908205975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35291439982162901938803983 52937159973244352908205975)
        ·
          refine ⟨79405739959866529362308963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52937159973244352908205975 79405739959866529362308963)
          ·
            refine ⟨119108609939799794043463445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79405739959866529362308963 119108609939799794043463445)
            ·
              refine ⟨5583216090928115345787349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119108609939799794043463445 5583216090928115345787349)
              ·
                refine ⟨130856627131127703416891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5583216090928115345787349 130856627131127703416891)
                ·
                  rfl

theorem cell21_1720186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1720186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720186 prefixEnd_1720186 := by exact prefixLift 1720186
  have htrace : WordTrace (prefixWord ++ tailWord_1720186) baseStart_1720186 baseEnd_1720186 := by
    simpa [prefixWord, tailWord_1720186, baseEnd_1720186] using wordTrace_append hprefix tailTrace_1720186
  have hstable : (prefixWord ++ tailWord_1720186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720186).length < 2 ^ (prefixWord ++ tailWord_1720186).sum := by decide
  have hdescent : baseEnd_1720186 < baseStart_1720186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720220 : List Nat := [2, 2, 3, 3, 1, 3, 1, 6]
def baseStart_1720220 : Nat := 118140960795 + 1720220 * 2 ^ 59
def prefixEnd_1720220 : Nat := 4983230072969 + 3 ^ 40 * 1720220 * 2
def baseEnd_1720220 : Nat := 130859213552202202227979

theorem tailTrace_1720220 : CollatzResearch.WordTrace tailWord_1720220 prefixEnd_1720220 130859213552202202227979 := by
  unfold tailWord_1720220
  simp only [CollatzResearch.WordTrace]
  refine ⟨31370788913972102515639057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41827718551962803354185409 31370788913972102515639057)
  ·
    refine ⟨23528091685479076886729293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31370788913972102515639057 23528091685479076886729293)
    ·
      refine ⟨8823034382054653832523485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23528091685479076886729293 8823034382054653832523485)
      ·
        refine ⟨3308637893270495187196307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8823034382054653832523485 3308637893270495187196307)
        ·
          refine ⟨4962956839905742780794461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308637893270495187196307 4962956839905742780794461)
          ·
            refine ⟨1861108814964653542797923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4962956839905742780794461 1861108814964653542797923)
            ·
              refine ⟨2791663222446980314196885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861108814964653542797923 2791663222446980314196885)
              ·
                refine ⟨130859213552202202227979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2791663222446980314196885 130859213552202202227979)
                ·
                  rfl

theorem cell21_1720220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_1720220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720220 prefixEnd_1720220 := by exact prefixLift 1720220
  have htrace : WordTrace (prefixWord ++ tailWord_1720220) baseStart_1720220 baseEnd_1720220 := by
    simpa [prefixWord, tailWord_1720220, baseEnd_1720220] using wordTrace_append hprefix tailTrace_1720220
  have hstable : (prefixWord ++ tailWord_1720220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720220).length < 2 ^ (prefixWord ++ tailWord_1720220).sum := by decide
  have hdescent : baseEnd_1720220 < baseStart_1720220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720282 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1720282 : Nat := 118140960795 + 1720282 * 2 ^ 59
def prefixEnd_1720282 : Nat := 4983230072969 + 3 ^ 40 * 1720282 * 2
def baseEnd_1720282 : Nat := 392591789901308276650477

theorem tailTrace_1720282 : CollatzResearch.WordTrace tailWord_1720282 prefixEnd_1720282 392591789901308276650477 := by
  unfold tailWord_1720282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685959788429897405008775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41829226102479726413356733 15685959788429897405008775)
  ·
    refine ⟨23528939682644846107513163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685959788429897405008775 23528939682644846107513163)
    ·
      refine ⟨35293409523967269161269745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23528939682644846107513163 35293409523967269161269745)
      ·
        refine ⟨26470057142975451870952309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35293409523967269161269745 26470057142975451870952309)
        ·
          refine ⟨2481567857153948612901779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26470057142975451870952309 2481567857153948612901779)
          ·
            refine ⟨3722351785730922919352669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481567857153948612901779 3722351785730922919352669)
            ·
              refine ⟨1395881919649096094757251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3722351785730922919352669 1395881919649096094757251)
              ·
                refine ⟨2093822879473644142135877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395881919649096094757251 2093822879473644142135877)
                ·
                  refine ⟨392591789901308276650477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093822879473644142135877 392591789901308276650477)
                  ·
                    rfl

theorem cell21_1720282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1720282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720282 prefixEnd_1720282 := by exact prefixLift 1720282
  have htrace : WordTrace (prefixWord ++ tailWord_1720282) baseStart_1720282 baseEnd_1720282 := by
    simpa [prefixWord, tailWord_1720282, baseEnd_1720282] using wordTrace_append hprefix tailTrace_1720282
  have hstable : (prefixWord ++ tailWord_1720282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720282).length < 2 ^ (prefixWord ++ tailWord_1720282).sum := by decide
  have hdescent : baseEnd_1720282 < baseStart_1720282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720333 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1720333 : Nat := 118140960795 + 1720333 * 2 ^ 59
def prefixEnd_1720333 : Nat := 4983230072969 + 3 ^ 40 * 1720333 * 2
def baseEnd_1720333 : Nat := 392603428796143521300373

theorem tailTrace_1720333 : CollatzResearch.WordTrace tailWord_1720333 prefixEnd_1720333 392603428796143521300373 := by
  unfold tailWord_1720333
  simp only [CollatzResearch.WordTrace]
  refine ⟨62745699276534825330141653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41830466184356550220094435 62745699276534825330141653)
  ·
    refine ⟨1470602326793784968675195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62745699276534825330141653 1470602326793784968675195)
    ·
      refine ⟨2205903490190677453012793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470602326793784968675195 2205903490190677453012793)
      ·
        refine ⟨1654427617643008089759595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2205903490190677453012793 1654427617643008089759595)
        ·
          refine ⟨2481641426464512134639393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654427617643008089759595 2481641426464512134639393)
          ·
            refine ⟨1861231069848384100979545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2481641426464512134639393 1861231069848384100979545)
            ·
              refine ⟨1395923302386288075734659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861231069848384100979545 1395923302386288075734659)
              ·
                refine ⟨2093884953579432113601989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395923302386288075734659 2093884953579432113601989)
                ·
                  refine ⟨392603428796143521300373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093884953579432113601989 392603428796143521300373)
                  ·
                    rfl

theorem cell21_1720333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1720333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720333 prefixEnd_1720333 := by exact prefixLift 1720333
  have htrace : WordTrace (prefixWord ++ tailWord_1720333) baseStart_1720333 baseEnd_1720333 := by
    simpa [prefixWord, tailWord_1720333, baseEnd_1720333] using wordTrace_append hprefix tailTrace_1720333
  have hstable : (prefixWord ++ tailWord_1720333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720333).length < 2 ^ (prefixWord ++ tailWord_1720333).sum := by decide
  have hdescent : baseEnd_1720333 < baseStart_1720333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720341 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1720341 : Nat := 118140960795 + 1720341 * 2 ^ 59
def prefixEnd_1720341 : Nat := 4983230072969 + 3 ^ 40 * 1720341 * 2
def baseEnd_1720341 : Nat := 392605254505137285167023

theorem tailTrace_1720341 : CollatzResearch.WordTrace tailWord_1720341 prefixEnd_1720341 392605254505137285167023 := by
  unfold tailWord_1720341
  simp only [CollatzResearch.WordTrace]
  refine ⟨62745991060505842696432877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41830660707003895130955251 62745991060505842696432877)
  ·
    refine ⟨23529746647689691011162329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62745991060505842696432877 23529746647689691011162329)
    ·
      refine ⟨17647309985767268258371747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23529746647689691011162329 17647309985767268258371747)
      ·
        refine ⟨26470964978650902387557621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17647309985767268258371747 26470964978650902387557621)
        ·
          refine ⟨2481652966748522098833527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26470964978650902387557621 2481652966748522098833527)
          ·
            refine ⟨3722479450122783148250291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481652966748522098833527 3722479450122783148250291)
            ·
              refine ⟨5583719175184174722375437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722479450122783148250291 5583719175184174722375437)
              ·
                refine ⟨2093894690694065520890789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5583719175184174722375437 2093894690694065520890789)
                ·
                  refine ⟨392605254505137285167023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093894690694065520890789 392605254505137285167023)
                  ·
                    rfl

theorem cell21_1720341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1720341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720341 prefixEnd_1720341 := by exact prefixLift 1720341
  have htrace : WordTrace (prefixWord ++ tailWord_1720341) baseStart_1720341 baseEnd_1720341 := by
    simpa [prefixWord, tailWord_1720341, baseEnd_1720341] using wordTrace_append hprefix tailTrace_1720341
  have hstable : (prefixWord ++ tailWord_1720341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720341).length < 2 ^ (prefixWord ++ tailWord_1720341).sum := by decide
  have hdescent : baseEnd_1720341 < baseStart_1720341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720372 : List Nat := [2, 5, 1, 2, 3, 8]
def baseStart_1720372 : Nat := 118140960795 + 1720372 * 2 ^ 59
def prefixEnd_1720372 : Nat := 4983230072969 + 3 ^ 40 * 1720372 * 2
def baseEnd_1720372 : Nat := 14541197375092152598159

theorem tailTrace_1720372 : CollatzResearch.WordTrace tailWord_1720372 prefixEnd_1720372 14541197375092152598159 := by
  unfold tailWord_1720372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373560861696767495405685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41831414482262356660540913 31373560861696767495405685)
  ·
    refine ⟨2941271330784071952694283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31373560861696767495405685 2941271330784071952694283)
    ·
      refine ⟨4411906996176107929041425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941271330784071952694283 4411906996176107929041425)
      ·
        refine ⟨3308930247132080946781069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411906996176107929041425 3308930247132080946781069)
        ·
          refine ⟨1240848842674530355042901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3308930247132080946781069 1240848842674530355042901)
          ·
            refine ⟨14541197375092152598159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1240848842674530355042901 14541197375092152598159)
            ·
              rfl

theorem cell21_1720372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 8].length) (baseStart_1720372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720372 prefixEnd_1720372 := by exact prefixLift 1720372
  have htrace : WordTrace (prefixWord ++ tailWord_1720372) baseStart_1720372 baseEnd_1720372 := by
    simpa [prefixWord, tailWord_1720372, baseEnd_1720372] using wordTrace_append hprefix tailTrace_1720372
  have hstable : (prefixWord ++ tailWord_1720372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720372).length < 2 ^ (prefixWord ++ tailWord_1720372).sum := by decide
  have hdescent : baseEnd_1720372 < baseStart_1720372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720383 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_1720383 : Nat := 118140960795 + 1720383 * 2 ^ 59
def prefixEnd_1720383 : Nat := 4983230072969 + 3 ^ 40 * 1720383 * 2
def baseEnd_1720383 : Nat := 392614839477354545466937

theorem tailTrace_1720383 : CollatzResearch.WordTrace tailWord_1720383 prefixEnd_1720383 392614839477354545466937 := by
  unfold tailWord_1720383
  simp only [CollatzResearch.WordTrace]
  refine ⟨62747522926353683869461803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41831681950902455912974535 62747522926353683869461803)
  ·
    refine ⟨94121284389530525804192705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62747522926353683869461803 94121284389530525804192705)
    ·
      refine ⟨70590963292147894353144529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94121284389530525804192705 70590963292147894353144529)
      ·
        refine ⟨52943222469110920764858397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70590963292147894353144529 52943222469110920764858397)
        ·
          refine ⟨19853708425916595286821899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52943222469110920764858397 19853708425916595286821899)
          ·
            refine ⟨29780562638874892930232849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19853708425916595286821899 29780562638874892930232849)
            ·
              refine ⟨22335421979156169697674637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29780562638874892930232849 22335421979156169697674637)
              ·
                refine ⟨8375783242183563636627989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22335421979156169697674637 8375783242183563636627989)
                ·
                  refine ⟨392614839477354545466937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8375783242183563636627989 392614839477354545466937)
                  ·
                    rfl

theorem cell21_1720383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_1720383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720383 prefixEnd_1720383 := by exact prefixLift 1720383
  have htrace : WordTrace (prefixWord ++ tailWord_1720383) baseStart_1720383 baseEnd_1720383 := by
    simpa [prefixWord, tailWord_1720383, baseEnd_1720383] using wordTrace_append hprefix tailTrace_1720383
  have hstable : (prefixWord ++ tailWord_1720383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720383).length < 2 ^ (prefixWord ++ tailWord_1720383).sum := by decide
  have hdescent : baseEnd_1720383 < baseStart_1720383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720445 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1720445 : Nat := 118140960795 + 1720445 * 2 ^ 59
def prefixEnd_1720445 : Nat := 4983230072969 + 3 ^ 40 * 1720445 * 2
def baseEnd_1720445 : Nat := 392628988722056215433477

theorem tailTrace_1720445 : CollatzResearch.WordTrace tailWord_1720445 prefixEnd_1720445 392628988722056215433477 := by
  unfold tailWord_1720445
  simp only [CollatzResearch.WordTrace]
  refine ⟨62749784252129068458218789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41833189501419378972145859 62749784252129068458218789)
  ·
    refine ⟨11765584547274200335916023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62749784252129068458218789 11765584547274200335916023)
    ·
      refine ⟨17648376820911300503874035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11765584547274200335916023 17648376820911300503874035)
      ·
        refine ⟨26472565231366950755811053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17648376820911300503874035 26472565231366950755811053)
        ·
          refine ⟨9927211961762606533429145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26472565231366950755811053 9927211961762606533429145)
          ·
            refine ⟨7445408971321954900071859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927211961762606533429145 7445408971321954900071859)
            ·
              refine ⟨11168113456982932350107789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445408971321954900071859 11168113456982932350107789)
              ·
                refine ⟨4188042546368599631290421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11168113456982932350107789 4188042546368599631290421)
                ·
                  refine ⟨392628988722056215433477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4188042546368599631290421 392628988722056215433477)
                  ·
                    rfl

theorem cell21_1720445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1720445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720445 prefixEnd_1720445 := by exact prefixLift 1720445
  have htrace : WordTrace (prefixWord ++ tailWord_1720445) baseStart_1720445 baseEnd_1720445 := by
    simpa [prefixWord, tailWord_1720445, baseEnd_1720445] using wordTrace_append hprefix tailTrace_1720445
  have hstable : (prefixWord ++ tailWord_1720445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720445).length < 2 ^ (prefixWord ++ tailWord_1720445).sum := by decide
  have hdescent : baseEnd_1720445 < baseStart_1720445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720479 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 3]
def baseStart_1720479 : Nat := 118140960795 + 1720479 * 2 ^ 59
def prefixEnd_1720479 : Nat := 4983230072969 + 3 ^ 40 * 1720479 * 2
def baseEnd_1720479 : Nat := 392636747985279711866741

theorem tailTrace_1720479 : CollatzResearch.WordTrace tailWord_1720479 prefixEnd_1720479 392636747985279711866741 := by
  unfold tailWord_1720479
  simp only [CollatzResearch.WordTrace]
  refine ⟨62751024334005892264956491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41834016222670594843304327 62751024334005892264956491)
  ·
    refine ⟨94126536501008838397434737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62751024334005892264956491 94126536501008838397434737)
    ·
      refine ⟨70594902375756628798076053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94126536501008838397434737 70594902375756628798076053)
      ·
        refine ⟨3309136048863591974909815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70594902375756628798076053 3309136048863591974909815)
        ·
          refine ⟨4963704073295387962364723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309136048863591974909815 4963704073295387962364723)
          ·
            refine ⟨7445556109943081943547085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963704073295387962364723 7445556109943081943547085)
            ·
              refine ⟨2792083541228655728830157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7445556109943081943547085 2792083541228655728830157)
              ·
                refine ⟨1047031327960745898311309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2792083541228655728830157 1047031327960745898311309)
                ·
                  refine ⟨392636747985279711866741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047031327960745898311309 392636747985279711866741)
                  ·
                    rfl

theorem cell21_1720479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].length) (baseStart_1720479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720479 prefixEnd_1720479 := by exact prefixLift 1720479
  have htrace : WordTrace (prefixWord ++ tailWord_1720479) baseStart_1720479 baseEnd_1720479 := by
    simpa [prefixWord, tailWord_1720479, baseEnd_1720479] using wordTrace_append hprefix tailTrace_1720479
  have hstable : (prefixWord ++ tailWord_1720479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720479).length < 2 ^ (prefixWord ++ tailWord_1720479).sum := by decide
  have hdescent : baseEnd_1720479 < baseStart_1720479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720552 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_1720552 : Nat := 118140960795 + 1720552 * 2 ^ 59
def prefixEnd_1720552 : Nat := 4983230072969 + 3 ^ 40 * 1720552 * 2
def baseEnd_1720552 : Nat := 392653407579847807149925

theorem tailTrace_1720552 : CollatzResearch.WordTrace tailWord_1720552 prefixEnd_1720552 392653407579847807149925 := by
  unfold tailWord_1720552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31376843431370712866181955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41835791241827617154909273 31376843431370712866181955)
  ·
    refine ⟨47065265147056069299272933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31376843431370712866181955 47065265147056069299272933)
    ·
      refine ⟨8824737215073012993613675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47065265147056069299272933 8824737215073012993613675)
      ·
        refine ⟨13237105822609519490420513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824737215073012993613675 13237105822609519490420513)
        ·
          refine ⟨9927829366957139617815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13237105822609519490420513 9927829366957139617815385)
          ·
            refine ⟨7445872025217854713361539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927829366957139617815385 7445872025217854713361539)
            ·
              refine ⟨11168808037826782070042309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445872025217854713361539 11168808037826782070042309)
              ·
                refine ⟨2094151507092521638132933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11168808037826782070042309 2094151507092521638132933)
                ·
                  refine ⟨392653407579847807149925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094151507092521638132933 392653407579847807149925)
                  ·
                    rfl

theorem cell21_1720552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_1720552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720552 prefixEnd_1720552 := by exact prefixLift 1720552
  have htrace : WordTrace (prefixWord ++ tailWord_1720552) baseStart_1720552 baseEnd_1720552 := by
    simpa [prefixWord, tailWord_1720552, baseEnd_1720552] using wordTrace_append hprefix tailTrace_1720552
  have hstable : (prefixWord ++ tailWord_1720552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720552).length < 2 ^ (prefixWord ++ tailWord_1720552).sum := by decide
  have hdescent : baseEnd_1720552 < baseStart_1720552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720611 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_1720611 : Nat := 118140960795 + 1720611 * 2 ^ 59
def prefixEnd_1720611 : Nat := 4983230072969 + 3 ^ 40 * 1720611 * 2
def baseEnd_1720611 : Nat := 392666872183676815666471

theorem tailTrace_1720611 : CollatzResearch.WordTrace tailWord_1720611 prefixEnd_1720611 392666872183676815666471 := by
  unfold tailWord_1720611
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755838769527678808761687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41837225846351785872507791 62755838769527678808761687)
  ·
    refine ⟨94133758154291518213142531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62755838769527678808761687 94133758154291518213142531)
    ·
      refine ⟨141200637231437277319713797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94133758154291518213142531 141200637231437277319713797)
      ·
        refine ⟨26475119480894489497446337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141200637231437277319713797 26475119480894489497446337)
        ·
          refine ⟨19856339610670867123084753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26475119480894489497446337 19856339610670867123084753)
          ·
            refine ⟨14892254708003150342313565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856339610670867123084753 14892254708003150342313565)
            ·
              refine ⟨5584595515501181378367587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14892254708003150342313565 5584595515501181378367587)
              ·
                refine ⟨8376893273251772067551381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584595515501181378367587 8376893273251772067551381)
                ·
                  refine ⟨392666872183676815666471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8376893273251772067551381 392666872183676815666471)
                  ·
                    rfl

theorem cell21_1720611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_1720611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720611 prefixEnd_1720611 := by exact prefixLift 1720611
  have htrace : WordTrace (prefixWord ++ tailWord_1720611) baseStart_1720611 baseEnd_1720611 := by
    simpa [prefixWord, tailWord_1720611, baseEnd_1720611] using wordTrace_append hprefix tailTrace_1720611
  have hstable : (prefixWord ++ tailWord_1720611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720611).length < 2 ^ (prefixWord ++ tailWord_1720611).sum := by decide
  have hdescent : baseEnd_1720611 < baseStart_1720611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720718 : List Nat := [4, 1, 1, 4, 1, 10]
def baseStart_1720718 : Nat := 118140960795 + 1720718 * 2 ^ 59
def prefixEnd_1720718 : Nat := 4983230072969 + 3 ^ 40 * 1720718 * 2
def baseEnd_1720718 : Nat := 14544121890424755828997

theorem tailTrace_1720718 : CollatzResearch.WordTrace tailWord_1720718 prefixEnd_1720718 14544121890424755828997 := by
  unfold tailWord_1720718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844967672517504510363351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41839827586760024055271205 7844967672517504510363351)
  ·
    refine ⟨11767451508776256765545027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844967672517504510363351 11767451508776256765545027)
    ·
      refine ⟨17651177263164385148317541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767451508776256765545027 17651177263164385148317541)
      ·
        refine ⟨3309595736843322215309539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17651177263164385148317541 3309595736843322215309539)
        ·
          refine ⟨4964393605264983322964309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309595736843322215309539 4964393605264983322964309)
          ·
            refine ⟨14544121890424755828997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4964393605264983322964309 14544121890424755828997)
            ·
              rfl

theorem cell21_1720718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 10].length) (baseStart_1720718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720718 prefixEnd_1720718 := by exact prefixLift 1720718
  have htrace : WordTrace (prefixWord ++ tailWord_1720718) baseStart_1720718 baseEnd_1720718 := by
    simpa [prefixWord, tailWord_1720718, baseEnd_1720718] using wordTrace_append hprefix tailTrace_1720718
  have hstable : (prefixWord ++ tailWord_1720718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720718).length < 2 ^ (prefixWord ++ tailWord_1720718).sum := by decide
  have hdescent : baseEnd_1720718 < baseStart_1720718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720766 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1720766 : Nat := 118140960795 + 1720766 * 2 ^ 59
def prefixEnd_1720766 : Nat := 4983230072969 + 3 ^ 40 * 1720766 * 2
def baseEnd_1720766 : Nat := 392702245295430990582821

theorem tailTrace_1720766 : CollatzResearch.WordTrace tailWord_1720766 prefixEnd_1720766 392702245295430990582821 := by
  unfold tailWord_1720766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845186510495767535081769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41840994722644093520436101 7845186510495767535081769)
  ·
    refine ⟨5883889882871825651311327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7845186510495767535081769 5883889882871825651311327)
    ·
      refine ⟨8825834824307738476966991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883889882871825651311327 8825834824307738476966991)
      ·
        refine ⟨13238752236461607715450487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8825834824307738476966991 13238752236461607715450487)
        ·
          refine ⟨19858128354692411573175731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238752236461607715450487 19858128354692411573175731)
          ·
            refine ⟨29787192532038617359763597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19858128354692411573175731 29787192532038617359763597)
            ·
              refine ⟨11170197199514481509911349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29787192532038617359763597 11170197199514481509911349)
              ·
                refine ⟨1047205987454482641554189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11170197199514481509911349 1047205987454482641554189)
                ·
                  refine ⟨392702245295430990582821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047205987454482641554189 392702245295430990582821)
                  ·
                    rfl

theorem cell21_1720766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1720766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720766 prefixEnd_1720766 := by exact prefixLift 1720766
  have htrace : WordTrace (prefixWord ++ tailWord_1720766) baseStart_1720766 baseEnd_1720766 := by
    simpa [prefixWord, tailWord_1720766, baseEnd_1720766] using wordTrace_append hprefix tailTrace_1720766
  have hstable : (prefixWord ++ tailWord_1720766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720766).length < 2 ^ (prefixWord ++ tailWord_1720766).sum := by decide
  have hdescent : baseEnd_1720766 < baseStart_1720766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720780 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_1720780 : Nat := 118140960795 + 1720780 * 2 ^ 59
def prefixEnd_1720780 : Nat := 4983230072969 + 3 ^ 40 * 1720780 * 2
def baseEnd_1720780 : Nat := 392705440286170077349459

theorem tailTrace_1720780 : CollatzResearch.WordTrace tailWord_1720780 prefixEnd_1720780 392705440286170077349459 := by
  unfold tailWord_1720780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381001352957710335831897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41841335137276947114442529 31381001352957710335831897)
  ·
    refine ⟨23535751014718282751873923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31381001352957710335831897 23535751014718282751873923)
    ·
      refine ⟨35303626522077424127810885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23535751014718282751873923 35303626522077424127810885)
      ·
        refine ⟨6619429972889517023964541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35303626522077424127810885 6619429972889517023964541)
        ·
          refine ⟨2482286239833568883986703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6619429972889517023964541 2482286239833568883986703)
          ·
            refine ⟨3723429359750353325980055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482286239833568883986703 3723429359750353325980055)
            ·
              refine ⟨5585144039625529988970083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723429359750353325980055 5585144039625529988970083)
              ·
                refine ⟨8377716059438294983455125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585144039625529988970083 8377716059438294983455125)
                ·
                  refine ⟨392705440286170077349459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8377716059438294983455125 392705440286170077349459)
                  ·
                    rfl

theorem cell21_1720780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_1720780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720780 prefixEnd_1720780 := by exact prefixLift 1720780
  have htrace : WordTrace (prefixWord ++ tailWord_1720780) baseStart_1720780 baseEnd_1720780 := by
    simpa [prefixWord, tailWord_1720780, baseEnd_1720780] using wordTrace_append hprefix tailTrace_1720780
  have hstable : (prefixWord ++ tailWord_1720780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720780).length < 2 ^ (prefixWord ++ tailWord_1720780).sum := by decide
  have hdescent : baseEnd_1720780 < baseStart_1720780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720797 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1720797 : Nat := 118140960795 + 1720797 * 2 ^ 59
def prefixEnd_1720797 : Nat := 4983230072969 + 3 ^ 40 * 1720797 * 2
def baseEnd_1720797 : Nat := 392709319917781825566091

theorem tailTrace_1720797 : CollatzResearch.WordTrace tailWord_1720797 prefixEnd_1720797 392709319917781825566091 := by
  unfold tailWord_1720797
  simp only [CollatzResearch.WordTrace]
  refine ⟨62762622746853832575032645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41841748497902555050021763 62762622746853832575032645)
  ·
    refine ⟨11767991765035093607818621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62762622746853832575032645 11767991765035093607818621)
    ·
      refine ⟨4412996911888160102931983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11767991765035093607818621 4412996911888160102931983)
      ·
        refine ⟨6619495367832240154397975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412996911888160102931983 6619495367832240154397975)
        ·
          refine ⟨9929243051748360231596963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619495367832240154397975 9929243051748360231596963)
          ·
            refine ⟨14893864577622540347395445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929243051748360231596963 14893864577622540347395445)
            ·
              refine ⟨1396299804152113157568323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14893864577622540347395445 1396299804152113157568323)
              ·
                refine ⟨2094449706228169736352485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396299804152113157568323 2094449706228169736352485)
                ·
                  refine ⟨392709319917781825566091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094449706228169736352485 392709319917781825566091)
                  ·
                    rfl

theorem cell21_1720797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1720797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720797 prefixEnd_1720797 := by exact prefixLift 1720797
  have htrace : WordTrace (prefixWord ++ tailWord_1720797) baseStart_1720797 baseEnd_1720797 := by
    simpa [prefixWord, tailWord_1720797, baseEnd_1720797] using wordTrace_append hprefix tailTrace_1720797
  have hstable : (prefixWord ++ tailWord_1720797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720797).length < 2 ^ (prefixWord ++ tailWord_1720797).sum := by decide
  have hdescent : baseEnd_1720797 < baseStart_1720797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720856 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_1720856 : Nat := 118140960795 + 1720856 * 2 ^ 59
def prefixEnd_1720856 : Nat := 4983230072969 + 3 ^ 40 * 1720856 * 2
def baseEnd_1720856 : Nat := 392722784521610834082637

theorem tailTrace_1720856 : CollatzResearch.WordTrace tailWord_1720856 prefixEnd_1720856 392722784521610834082637 := by
  unfold tailWord_1720856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382387326820042825715211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41843183102426723767620281 31382387326820042825715211)
  ·
    refine ⟨47073580990230064238572817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31382387326820042825715211 47073580990230064238572817)
    ·
      refine ⟨35305185742672548178929613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47073580990230064238572817 35305185742672548178929613)
      ·
        refine ⟨13239444653502205567098605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35305185742672548178929613 13239444653502205567098605)
        ·
          refine ⟨4964791745063327087661977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13239444653502205567098605 4964791745063327087661977)
          ·
            refine ⟨3723593808797495315746483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4964791745063327087661977 3723593808797495315746483)
            ·
              refine ⟨5585390713196242973619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723593808797495315746483 5585390713196242973619725)
              ·
                refine ⟨2094521517448591115107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5585390713196242973619725 2094521517448591115107397)
                ·
                  refine ⟨392722784521610834082637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094521517448591115107397 392722784521610834082637)
                  ·
                    rfl

theorem cell21_1720856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_1720856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720856 prefixEnd_1720856 := by exact prefixLift 1720856
  have htrace : WordTrace (prefixWord ++ tailWord_1720856) baseStart_1720856 baseEnd_1720856 := by
    simpa [prefixWord, tailWord_1720856, baseEnd_1720856] using wordTrace_append hprefix tailTrace_1720856
  have hstable : (prefixWord ++ tailWord_1720856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720856).length < 2 ^ (prefixWord ++ tailWord_1720856).sum := by decide
  have hdescent : baseEnd_1720856 < baseStart_1720856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720946 : List Nat := [3, 2, 1, 2, 4, 1, 8]
def baseStart_1720946 : Nat := 118140960795 + 1720946 * 2 ^ 59
def prefixEnd_1720946 : Nat := 4983230072969 + 3 ^ 40 * 1720946 * 2
def baseEnd_1720946 : Nat := 43638147083087853064717

theorem tailTrace_1720946 : CollatzResearch.WordTrace tailWord_1720946 prefixEnd_1720946 43638147083087853064717 := by
  unfold tailWord_1720946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15692014305828507755551673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41845371482209354014804461 15692014305828507755551673)
  ·
    refine ⟨11769010729371380816663755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15692014305828507755551673 11769010729371380816663755)
    ·
      refine ⟨17653516094057071224995633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769010729371380816663755 17653516094057071224995633)
      ·
        refine ⟨13240137070542803418746725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17653516094057071224995633 13240137070542803418746725)
        ·
          refine ⟨2482525700726775641015011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13240137070542803418746725 2482525700726775641015011)
          ·
            refine ⟨3723788551090163461522517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482525700726775641015011 3723788551090163461522517)
            ·
              refine ⟨43638147083087853064717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3723788551090163461522517 43638147083087853064717)
              ·
                rfl

theorem cell21_1720946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 8].length) (baseStart_1720946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720946 prefixEnd_1720946 := by exact prefixLift 1720946
  have htrace : WordTrace (prefixWord ++ tailWord_1720946) baseStart_1720946 baseEnd_1720946 := by
    simpa [prefixWord, tailWord_1720946, baseEnd_1720946] using wordTrace_append hprefix tailTrace_1720946
  have hstable : (prefixWord ++ tailWord_1720946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720946).length < 2 ^ (prefixWord ++ tailWord_1720946).sum := by decide
  have hdescent : baseEnd_1720946 < baseStart_1720946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720960 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_1720960 : Nat := 118140960795 + 1720960 * 2 ^ 59
def prefixEnd_1720960 : Nat := 4983230072969 + 3 ^ 40 * 1720960 * 2
def baseEnd_1720960 : Nat := 392746518738529764349091

theorem tailTrace_1720960 : CollatzResearch.WordTrace tailWord_1720960 prefixEnd_1720960 392746518738529764349091 := by
  unfold tailWord_1720960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31384283922631655706608167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41845711896842207608810889 31384283922631655706608167)
  ·
    refine ⟨47076425883947483559912251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31384283922631655706608167 47076425883947483559912251)
    ·
      refine ⟨70614638825921225339868377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47076425883947483559912251 70614638825921225339868377)
      ·
        refine ⟨52960979119440919004901283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70614638825921225339868377 52960979119440919004901283)
        ·
          refine ⟨79441468679161378507351925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52960979119440919004901283 79441468679161378507351925)
          ·
            refine ⟨7447637688671379235064243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79441468679161378507351925 7447637688671379235064243)
            ·
              refine ⟨11171456533007068852596365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447637688671379235064243 11171456533007068852596365)
              ·
                refine ⟨4189296199877650819723637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11171456533007068852596365 4189296199877650819723637)
                ·
                  refine ⟨392746518738529764349091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4189296199877650819723637 392746518738529764349091)
                  ·
                    rfl

theorem cell21_1720960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_1720960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720960 prefixEnd_1720960 := by exact prefixLift 1720960
  have htrace : WordTrace (prefixWord ++ tailWord_1720960) baseStart_1720960 baseEnd_1720960 := by
    simpa [prefixWord, tailWord_1720960, baseEnd_1720960] using wordTrace_append hprefix tailTrace_1720960
  have hstable : (prefixWord ++ tailWord_1720960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720960).length < 2 ^ (prefixWord ++ tailWord_1720960).sum := by decide
  have hdescent : baseEnd_1720960 < baseStart_1720960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720980 : List Nat := [2, 4, 2, 2, 1, 3, 2, 5]
def baseStart_1720980 : Nat := 118140960795 + 1720980 * 2 ^ 59
def prefixEnd_1720980 : Nat := 4983230072969 + 3 ^ 40 * 1720980 * 2
def baseEnd_1720980 : Nat := 130917027670338058005239

theorem tailTrace_1720980 : CollatzResearch.WordTrace tailWord_1720980 prefixEnd_1720980 130917027670338058005239 := by
  unfold tailWord_1720980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31384648652595427414472197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41846198203460569885962929 31384648652595427414472197)
  ·
    refine ⟨5884621622361642640213537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31384648652595427414472197 5884621622361642640213537)
    ·
      refine ⟨4413466216771231980160153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5884621622361642640213537 4413466216771231980160153)
      ·
        refine ⟨3310099662578423985120115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4413466216771231980160153 3310099662578423985120115)
        ·
          refine ⟨4965149493867635977680173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310099662578423985120115 4965149493867635977680173)
          ·
            refine ⟨1861931060200363491630065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965149493867635977680173 1861931060200363491630065)
            ·
              refine ⟨1396448295150272618722549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861931060200363491630065 1396448295150272618722549)
              ·
                refine ⟨130917027670338058005239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396448295150272618722549 130917027670338058005239)
                ·
                  rfl

theorem cell21_1720980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_1720980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1720980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1720980 prefixEnd_1720980 := by exact prefixLift 1720980
  have htrace : WordTrace (prefixWord ++ tailWord_1720980) baseStart_1720980 baseEnd_1720980 := by
    simpa [prefixWord, tailWord_1720980, baseEnd_1720980] using wordTrace_append hprefix tailTrace_1720980
  have hstable : (prefixWord ++ tailWord_1720980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720980).length < 2 ^ (prefixWord ++ tailWord_1720980).sum := by decide
  have hdescent : baseEnd_1720980 < baseStart_1720980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721022 : List Nat := [4, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1721022 : Nat := 118140960795 + 1721022 * 2 ^ 59
def prefixEnd_1721022 : Nat := 4983230072969 + 3 ^ 40 * 1721022 * 2
def baseEnd_1721022 : Nat := 130920222661077144771877

theorem tailTrace_1721022 : CollatzResearch.WordTrace tailWord_1721022 prefixEnd_1721022 130920222661077144771877 := by
  unfold tailWord_1721022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846353646379837000246665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41847219447359130667982213 7846353646379837000246665)
  ·
    refine ⟨5884765234784877750184999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7846353646379837000246665 5884765234784877750184999)
    ·
      refine ⟨8827147852177316625277499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884765234784877750184999 8827147852177316625277499)
      ·
        refine ⟨13240721778265974937916249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8827147852177316625277499 13240721778265974937916249)
        ·
          refine ⟨9930541333699481203437187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13240721778265974937916249 9930541333699481203437187)
          ·
            refine ⟨14895812000549221805155781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930541333699481203437187 14895812000549221805155781)
            ·
              refine ⟨2792964750102979088466709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14895812000549221805155781 2792964750102979088466709)
              ·
                refine ⟨130920222661077144771877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2792964750102979088466709 130920222661077144771877)
                ·
                  rfl

theorem cell21_1721022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1721022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721022 prefixEnd_1721022 := by exact prefixLift 1721022
  have htrace : WordTrace (prefixWord ++ tailWord_1721022) baseStart_1721022 baseEnd_1721022 := by
    simpa [prefixWord, tailWord_1721022, baseEnd_1721022] using wordTrace_append hprefix tailTrace_1721022
  have hstable : (prefixWord ++ tailWord_1721022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721022).length < 2 ^ (prefixWord ++ tailWord_1721022).sum := by decide
  have hdescent : baseEnd_1721022 < baseStart_1721022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721070 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1721070 : Nat := 118140960795 + 1721070 * 2 ^ 59
def prefixEnd_1721070 : Nat := 4983230072969 + 3 ^ 40 * 1721070 * 2
def baseEnd_1721070 : Nat := 392771622237194017515533

theorem tailTrace_1721070 : CollatzResearch.WordTrace tailWord_1721070 prefixEnd_1721070 392771622237194017515533 := by
  unfold tailWord_1721070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846572484358100024965083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41848386583243200133147109 7846572484358100024965083)
  ·
    refine ⟨11769858726537150037447625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7846572484358100024965083 11769858726537150037447625)
    ·
      refine ⟨8827394044902862528085719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11769858726537150037447625 8827394044902862528085719)
      ·
        refine ⟨13241091067354293792128579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8827394044902862528085719 13241091067354293792128579)
        ·
          refine ⟨19861636601031440688192869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13241091067354293792128579 19861636601031440688192869)
          ·
            refine ⟨3724056862693395129036163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19861636601031440688192869 3724056862693395129036163)
            ·
              refine ⟨5586085294040092693554245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724056862693395129036163 5586085294040092693554245)
              ·
                refine ⟨1047390992632517380041421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5586085294040092693554245 1047390992632517380041421)
                ·
                  refine ⟨392771622237194017515533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047390992632517380041421 392771622237194017515533)
                  ·
                    rfl

theorem cell21_1721070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1721070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721070 prefixEnd_1721070 := by exact prefixLift 1721070
  have htrace : WordTrace (prefixWord ++ tailWord_1721070) baseStart_1721070 baseEnd_1721070 := by
    simpa [prefixWord, tailWord_1721070, baseEnd_1721070] using wordTrace_append hprefix tailTrace_1721070
  have hstable : (prefixWord ++ tailWord_1721070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721070).length < 2 ^ (prefixWord ++ tailWord_1721070).sum := by decide
  have hdescent : baseEnd_1721070 < baseStart_1721070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721098 : List Nat := [3, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1721098 : Nat := 118140960795 + 1721098 * 2 ^ 59
def prefixEnd_1721098 : Nat := 4983230072969 + 3 ^ 40 * 1721098 * 2
def baseEnd_1721098 : Nat := 130926004072890730349603

theorem tailTrace_1721098 : CollatzResearch.WordTrace tailWord_1721098 prefixEnd_1721098 130926004072890730349603 := by
  unfold tailWord_1721098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693400279690840245434987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41849067412508907321159965 15693400279690840245434987)
  ·
    refine ⟨23540100419536260368152481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15693400279690840245434987 23540100419536260368152481)
    ·
      refine ⟨17655075314652195276114361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23540100419536260368152481 17655075314652195276114361)
      ·
        refine ⟨13241306485989146457085771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17655075314652195276114361 13241306485989146457085771)
        ·
          refine ⟨19861959728983719685628657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13241306485989146457085771 19861959728983719685628657)
          ·
            refine ⟨14896469796737789764221493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19861959728983719685628657 14896469796737789764221493)
            ·
              refine ⟨1396544043444167790395765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14896469796737789764221493 1396544043444167790395765)
              ·
                refine ⟨130926004072890730349603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396544043444167790395765 130926004072890730349603)
                ·
                  rfl

theorem cell21_1721098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1721098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721098 prefixEnd_1721098 := by exact prefixLift 1721098
  have htrace : WordTrace (prefixWord ++ tailWord_1721098) baseStart_1721098 baseEnd_1721098 := by
    simpa [prefixWord, tailWord_1721098, baseEnd_1721098] using wordTrace_append hprefix tailTrace_1721098
  have hstable : (prefixWord ++ tailWord_1721098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721098).length < 2 ^ (prefixWord ++ tailWord_1721098).sum := by decide
  have hdescent : baseEnd_1721098 < baseStart_1721098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721171 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_1721171 : Nat := 118140960795 + 1721171 * 2 ^ 59
def prefixEnd_1721171 : Nat := 4983230072969 + 3 ^ 40 * 1721171 * 2
def baseEnd_1721171 : Nat := 392794671813240286331993

theorem tailTrace_1721171 : CollatzResearch.WordTrace tailWord_1721171 prefixEnd_1721171 392794671813240286331993 := by
  unfold tailWord_1721171
  simp only [CollatzResearch.WordTrace]
  refine ⟨62776263647498894449147367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41850842431665929632764911 62776263647498894449147367)
  ·
    refine ⟨94164395471248341673721051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62776263647498894449147367 94164395471248341673721051)
    ·
      refine ⟨141246593206872512510581577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94164395471248341673721051 141246593206872512510581577)
      ·
        refine ⟨105934944905154384382936183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141246593206872512510581577 105934944905154384382936183)
        ·
          refine ⟨158902417357731576574404275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105934944905154384382936183 158902417357731576574404275)
          ·
            refine ⟨238353626036597364861606413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158902417357731576574404275 238353626036597364861606413)
            ·
              refine ⟨89382609763724011823102405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238353626036597364861606413 89382609763724011823102405)
              ·
                refine ⟨16759239330698252216831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89382609763724011823102405 16759239330698252216831701)
                ·
                  refine ⟨392794671813240286331993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16759239330698252216831701 392794671813240286331993)
                  ·
                    rfl

theorem cell21_1721171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_1721171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721171 prefixEnd_1721171 := by exact prefixLift 1721171
  have htrace : WordTrace (prefixWord ++ tailWord_1721171) baseStart_1721171 baseEnd_1721171 := by
    simpa [prefixWord, tailWord_1721171, baseEnd_1721171] using wordTrace_append hprefix tailTrace_1721171
  have hstable : (prefixWord ++ tailWord_1721171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721171).length < 2 ^ (prefixWord ++ tailWord_1721171).sum := by decide
  have hdescent : baseEnd_1721171 < baseStart_1721171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721236 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1721236 : Nat := 118140960795 + 1721236 * 2 ^ 59
def prefixEnd_1721236 : Nat := 4983230072969 + 3 ^ 40 * 1721236 * 2
def baseEnd_1721236 : Nat := 392809505698814617748527

theorem tailTrace_1721236 : CollatzResearch.WordTrace tailWord_1721236 prefixEnd_1721236 392809505698814617748527 := by
  unfold tailWord_1721236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389317196131705275131781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41852422928175607033509041 31389317196131705275131781)
  ·
    refine ⟨5885496974274694739087209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31389317196131705275131781 5885496974274694739087209)
    ·
      refine ⟨4414122730706021054315407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5885496974274694739087209 4414122730706021054315407)
      ·
        refine ⟨6621184096059031581473111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414122730706021054315407 6621184096059031581473111)
        ·
          refine ⟨9931776144088547372209667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621184096059031581473111 9931776144088547372209667)
          ·
            refine ⟨14897664216132821058314501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931776144088547372209667 14897664216132821058314501)
            ·
              refine ⟨2793312040524903948433969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14897664216132821058314501 2793312040524903948433969)
              ·
                refine ⟨2094984030393677961325477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793312040524903948433969 2094984030393677961325477)
                ·
                  refine ⟨392809505698814617748527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094984030393677961325477 392809505698814617748527)
                  ·
                    rfl

theorem cell21_1721236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1721236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721236 prefixEnd_1721236 := by exact prefixLift 1721236
  have htrace : WordTrace (prefixWord ++ tailWord_1721236) baseStart_1721236 baseEnd_1721236 := by
    simpa [prefixWord, tailWord_1721236, baseEnd_1721236] using wordTrace_append hprefix tailTrace_1721236
  have hstable : (prefixWord ++ tailWord_1721236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721236).length < 2 ^ (prefixWord ++ tailWord_1721236).sum := by decide
  have hdescent : baseEnd_1721236 < baseStart_1721236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721250 : List Nat := [3, 3, 1, 2, 2, 1, 3, 6]
def baseStart_1721250 : Nat := 118140960795 + 1721250 * 2 ^ 59
def prefixEnd_1721250 : Nat := 4983230072969 + 3 ^ 40 * 1721250 * 2
def baseEnd_1721250 : Nat := 130937566896517901505055

theorem tailTrace_1721250 : CollatzResearch.WordTrace tailWord_1721250 prefixEnd_1721250 130937566896517901505055 := by
  unfold tailWord_1721250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15694786253553172735318301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41852763342808460627515469 15694786253553172735318301)
  ·
    refine ⟨5885544845082439775744363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15694786253553172735318301 5885544845082439775744363)
    ·
      refine ⟨8828317267623659663616545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885544845082439775744363 8828317267623659663616545)
      ·
        refine ⟨6621237950717744747712409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8828317267623659663616545 6621237950717744747712409)
        ·
          refine ⟨4965928463038308560784307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6621237950717744747712409 4965928463038308560784307)
          ·
            refine ⟨7448892694557462841176461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965928463038308560784307 7448892694557462841176461)
            ·
              refine ⟨2793334760459048565441173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7448892694557462841176461 2793334760459048565441173)
              ·
                refine ⟨130937566896517901505055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2793334760459048565441173 130937566896517901505055)
                ·
                  rfl

theorem cell21_1721250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_1721250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721250 prefixEnd_1721250 := by exact prefixLift 1721250
  have htrace : WordTrace (prefixWord ++ tailWord_1721250) baseStart_1721250 baseEnd_1721250 := by
    simpa [prefixWord, tailWord_1721250, baseEnd_1721250] using wordTrace_append hprefix tailTrace_1721250
  have hstable : (prefixWord ++ tailWord_1721250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721250).length < 2 ^ (prefixWord ++ tailWord_1721250).sum := by decide
  have hdescent : baseEnd_1721250 < baseStart_1721250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721295 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_1721295 : Nat := 118140960795 + 1721295 * 2 ^ 59
def prefixEnd_1721295 : Nat := 4983230072969 + 3 ^ 40 * 1721295 * 2
def baseEnd_1721295 : Nat := 392822970302643626265073

theorem tailTrace_1721295 : CollatzResearch.WordTrace tailWord_1721295 prefixEnd_1721295 392822970302643626265073 := by
  unfold tailWord_1721295
  simp only [CollatzResearch.WordTrace]
  refine ⟨62780786299049663626661339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41853857532699775751107559 62780786299049663626661339)
  ·
    refine ⟨94171179448574495439992009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62780786299049663626661339 94171179448574495439992009)
    ·
      refine ⟨70628384586430871579994007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94171179448574495439992009 70628384586430871579994007)
      ·
        refine ⟨105942576879646307369991011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70628384586430871579994007 105942576879646307369991011)
        ·
          refine ⟨158913865319469461054986517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105942576879646307369991011 158913865319469461054986517)
          ·
            refine ⟨7449087436850130986952493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158913865319469461054986517 7449087436850130986952493)
            ·
              refine ⟨2793407788818799120107185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7449087436850130986952493 2793407788818799120107185)
              ·
                refine ⟨2095055841614099340080389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793407788818799120107185 2095055841614099340080389)
                ·
                  refine ⟨392822970302643626265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2095055841614099340080389 392822970302643626265073)
                  ·
                    rfl

theorem cell21_1721295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_1721295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721295 prefixEnd_1721295 := by exact prefixLift 1721295
  have htrace : WordTrace (prefixWord ++ tailWord_1721295) baseStart_1721295 baseEnd_1721295 := by
    simpa [prefixWord, tailWord_1721295, baseEnd_1721295] using wordTrace_append hprefix tailTrace_1721295
  have hstable : (prefixWord ++ tailWord_1721295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721295).length < 2 ^ (prefixWord ++ tailWord_1721295).sum := by decide
  have hdescent : baseEnd_1721295 < baseStart_1721295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721298 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1721298 : Nat := 118140960795 + 1721298 * 2 ^ 59
def prefixEnd_1721298 : Nat := 4983230072969 + 3 ^ 40 * 1721298 * 2
def baseEnd_1721298 : Nat := 392823654943516287715067

theorem tailTrace_1721298 : CollatzResearch.WordTrace tailWord_1721298 prefixEnd_1721298 392823654943516287715067 := by
  unfold tailWord_1721298
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695223929509698784755137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41853930478692530092680365 15695223929509698784755137)
  ·
    refine ⟨11771417947132274088566353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15695223929509698784755137 11771417947132274088566353)
    ·
      refine ⟨8828563460349205566424765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11771417947132274088566353 8828563460349205566424765)
      ·
        refine ⟨3310711297630952087409287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8828563460349205566424765 3310711297630952087409287)
        ·
          refine ⟨4966066946446428131113931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310711297630952087409287 4966066946446428131113931)
          ·
            refine ⟨7449100419669642196670897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966066946446428131113931 7449100419669642196670897)
            ·
              refine ⟨5586825314752231647503173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449100419669642196670897 5586825314752231647503173)
              ·
                refine ⟨1047529746516043433906845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5586825314752231647503173 1047529746516043433906845)
                ·
                  refine ⟨392823654943516287715067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047529746516043433906845 392823654943516287715067)
                  ·
                    rfl

theorem cell21_1721298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1721298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721298 prefixEnd_1721298 := by exact prefixLift 1721298
  have htrace : WordTrace (prefixWord ++ tailWord_1721298) baseStart_1721298 baseEnd_1721298 := by
    simpa [prefixWord, tailWord_1721298, baseEnd_1721298] using wordTrace_append hprefix tailTrace_1721298
  have hstable : (prefixWord ++ tailWord_1721298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721298).length < 2 ^ (prefixWord ++ tailWord_1721298).sum := by decide
  have hdescent : baseEnd_1721298 < baseStart_1721298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721326 : List Nat := [4, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1721326 : Nat := 118140960795 + 1721326 * 2 ^ 59
def prefixEnd_1721326 : Nat := 4983230072969 + 3 ^ 40 * 1721326 * 2
def baseEnd_1721326 : Nat := 130943348308331487082781

theorem tailTrace_1721326 : CollatzResearch.WordTrace tailWord_1721326 prefixEnd_1721326 130943348308331487082781 := by
  unfold tailWord_1721326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847739620242169490129979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41854611307958237280693221 7847739620242169490129979)
  ·
    refine ⟨11771609430363254235194969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847739620242169490129979 11771609430363254235194969)
    ·
      refine ⟨8828707072772440676396227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11771609430363254235194969 8828707072772440676396227)
      ·
        refine ⟨13243060609158661014594341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828707072772440676396227 13243060609158661014594341)
        ·
          refine ⟨2483073864217248940236439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13243060609158661014594341 2483073864217248940236439)
          ·
            refine ⟨3724610796325873410354659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483073864217248940236439 3724610796325873410354659)
            ·
              refine ⟨5586916194488810115531989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724610796325873410354659 5586916194488810115531989)
              ·
                refine ⟨130943348308331487082781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5586916194488810115531989 130943348308331487082781)
                ·
                  rfl

theorem cell21_1721326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1721326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721326 prefixEnd_1721326 := by exact prefixLift 1721326
  have htrace : WordTrace (prefixWord ++ tailWord_1721326) baseStart_1721326 baseEnd_1721326 := by
    simpa [prefixWord, tailWord_1721326, baseEnd_1721326] using wordTrace_append hprefix tailTrace_1721326
  have hstable : (prefixWord ++ tailWord_1721326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721326).length < 2 ^ (prefixWord ++ tailWord_1721326).sum := by decide
  have hdescent : baseEnd_1721326 < baseStart_1721326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721450 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_1721450 : Nat := 118140960795 + 1721450 * 2 ^ 59
def prefixEnd_1721450 : Nat := 4983230072969 + 3 ^ 40 * 1721450 * 2
def baseEnd_1721450 : Nat := 392858343414397801181423

theorem tailTrace_1721450 : CollatzResearch.WordTrace tailWord_1721450 prefixEnd_1721450 392858343414397801181423 := by
  unfold tailWord_1721450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696609903372031274638451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41857626408992083399035869 15696609903372031274638451)
  ·
    refine ⟨23544914855058046911957677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696609903372031274638451 23544914855058046911957677)
    ·
      refine ⟨8829343070646767591984129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23544914855058046911957677 8829343070646767591984129)
      ·
        refine ⟨6622007302985075693988097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8829343070646767591984129 6622007302985075693988097)
        ·
          refine ⟨4966505477238806770491073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6622007302985075693988097 4966505477238806770491073)
          ·
            refine ⟨3724879107929105077868305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966505477238806770491073 3724879107929105077868305)
            ·
              refine ⟨2793659330946828808401229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724879107929105077868305 2793659330946828808401229)
              ·
                refine ⟨1047622249105060803150461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793659330946828808401229 1047622249105060803150461)
                ·
                  refine ⟨392858343414397801181423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047622249105060803150461 392858343414397801181423)
                  ·
                    rfl

theorem cell21_1721450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_1721450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721450 prefixEnd_1721450 := by exact prefixLift 1721450
  have htrace : WordTrace (prefixWord ++ tailWord_1721450) baseStart_1721450 baseEnd_1721450 := by
    simpa [prefixWord, tailWord_1721450, baseEnd_1721450] using wordTrace_append hprefix tailTrace_1721450
  have hstable : (prefixWord ++ tailWord_1721450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721450).length < 2 ^ (prefixWord ++ tailWord_1721450).sum := by decide
  have hdescent : baseEnd_1721450 < baseStart_1721450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721509 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 3]
def baseStart_1721509 : Nat := 118140960795 + 1721509 * 2 ^ 59
def prefixEnd_1721509 : Nat := 4983230072969 + 3 ^ 40 * 1721509 * 2
def baseEnd_1721509 : Nat := 392871808018226809697969

theorem tailTrace_1721509 : CollatzResearch.WordTrace tailWord_1721509 prefixEnd_1721509 392871808018226809697969 := by
  unfold tailWord_1721509
  simp only [CollatzResearch.WordTrace]
  refine ⟨62788591520274378174951581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41859061013516252116634387 62788591520274378174951581)
  ·
    refine ⟨23545721820102891815606843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62788591520274378174951581 23545721820102891815606843)
    ·
      refine ⟨35318582730154337723410265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23545721820102891815606843 35318582730154337723410265)
      ·
        refine ⟨26488937047615753292557699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35318582730154337723410265 26488937047615753292557699)
        ·
          refine ⟨39733405571423629938836549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488937047615753292557699 39733405571423629938836549)
          ·
            refine ⟨7450013544641930613531853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39733405571423629938836549 7450013544641930613531853)
            ·
              refine ⟨2793755079240723980074445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7450013544641930613531853 2793755079240723980074445)
              ·
                refine ⟨1047658154715271492527917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793755079240723980074445 1047658154715271492527917)
                ·
                  refine ⟨392871808018226809697969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047658154715271492527917 392871808018226809697969)
                  ·
                    rfl

theorem cell21_1721509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_1721509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721509 prefixEnd_1721509 := by exact prefixLift 1721509
  have htrace : WordTrace (prefixWord ++ tailWord_1721509) baseStart_1721509 baseEnd_1721509 := by
    simpa [prefixWord, tailWord_1721509, baseEnd_1721509] using wordTrace_append hprefix tailTrace_1721509
  have hstable : (prefixWord ++ tailWord_1721509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721509).length < 2 ^ (prefixWord ++ tailWord_1721509).sum := by decide
  have hdescent : baseEnd_1721509 < baseStart_1721509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721540 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1721540 : Nat := 118140960795 + 1721540 * 2 ^ 59
def prefixEnd_1721540 : Nat := 4983230072969 + 3 ^ 40 * 1721540 * 2
def baseEnd_1721540 : Nat := 392878882640577644681239

theorem tailTrace_1721540 : CollatzResearch.WordTrace tailWord_1721540 prefixEnd_1721540 392878882640577644681239 := by
  unfold tailWord_1721540
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394861091581035234665037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41859814788774713646220049 31394861091581035234665037)
  ·
    refine ⟨11773072909342888212999389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31394861091581035234665037 11773072909342888212999389)
    ·
      refine ⟨4414902341003583079874771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11773072909342888212999389 4414902341003583079874771)
      ·
        refine ⟨6622353511505374619812157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414902341003583079874771 6622353511505374619812157)
        ·
          refine ⟨2483382566814515482429559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6622353511505374619812157 2483382566814515482429559)
          ·
            refine ⟨3725073850221773223644339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483382566814515482429559 3725073850221773223644339)
            ·
              refine ⟨5587610775332659835466509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725073850221773223644339 5587610775332659835466509)
              ·
                refine ⟨2095354040749747438299941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587610775332659835466509 2095354040749747438299941)
                ·
                  refine ⟨392878882640577644681239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2095354040749747438299941 392878882640577644681239)
                  ·
                    rfl

theorem cell21_1721540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1721540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721540 prefixEnd_1721540 := by exact prefixLift 1721540
  have htrace : WordTrace (prefixWord ++ tailWord_1721540) baseStart_1721540 baseEnd_1721540 := by
    simpa [prefixWord, tailWord_1721540, baseEnd_1721540] using wordTrace_append hprefix tailTrace_1721540
  have hstable : (prefixWord ++ tailWord_1721540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721540).length < 2 ^ (prefixWord ++ tailWord_1721540).sum := by decide
  have hdescent : baseEnd_1721540 < baseStart_1721540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721582 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1721582 : Nat := 118140960795 + 1721582 * 2 ^ 59
def prefixEnd_1721582 : Nat := 4983230072969 + 3 ^ 40 * 1721582 * 2
def baseEnd_1721582 : Nat := 392888467612794904981153

theorem tailTrace_1721582 : CollatzResearch.WordTrace tailWord_1721582 prefixEnd_1721582 392888467612794904981153 := by
  unfold tailWord_1721582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7848906756126238955294875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41860836032673274428239333 7848906756126238955294875)
  ·
    refine ⟨11773360134189358432942313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7848906756126238955294875 11773360134189358432942313)
    ·
      refine ⟨8830020100642018824706735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11773360134189358432942313 8830020100642018824706735)
      ·
        refine ⟨13245030150963028237060103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830020100642018824706735 13245030150963028237060103)
        ·
          refine ⟨19867545226444542355590155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245030150963028237060103 19867545226444542355590155)
          ·
            refine ⟨29801317839666813533385233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19867545226444542355590155 29801317839666813533385233)
            ·
              refine ⟨22350988379750110150038925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29801317839666813533385233 22350988379750110150038925)
              ·
                refine ⟨8381620642406291306264597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22350988379750110150038925 8381620642406291306264597)
                ·
                  refine ⟨392888467612794904981153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8381620642406291306264597 392888467612794904981153)
                  ·
                    rfl

theorem cell21_1721582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1721582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721582 prefixEnd_1721582 := by exact prefixLift 1721582
  have htrace : WordTrace (prefixWord ++ tailWord_1721582) baseStart_1721582 baseEnd_1721582 := by
    simpa [prefixWord, tailWord_1721582, baseEnd_1721582] using wordTrace_append hprefix tailTrace_1721582
  have hstable : (prefixWord ++ tailWord_1721582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721582).length < 2 ^ (prefixWord ++ tailWord_1721582).sum := by decide
  have hdescent : baseEnd_1721582 < baseStart_1721582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721706 : List Nat := [3, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1721706 : Nat := 118140960795 + 1721706 * 2 ^ 59
def prefixEnd_1721706 : Nat := 4983230072969 + 3 ^ 40 * 1721706 * 2
def baseEnd_1721706 : Nat := 130972255367399414971411

theorem tailTrace_1721706 : CollatzResearch.WordTrace tailWord_1721706 prefixEnd_1721706 130972255367399414971411 := by
  unfold tailWord_1721706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698944175140170204968243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41863851133707120546581981 15698944175140170204968243)
  ·
    refine ⟨23548416262710255307452365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15698944175140170204968243 23548416262710255307452365)
    ·
      refine ⟨8830656098516345740294637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23548416262710255307452365 8830656098516345740294637)
      ·
        refine ⟨3311496036943629652610489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8830656098516345740294637 3311496036943629652610489)
        ·
          refine ⟨2483622027707722239457867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3311496036943629652610489 2483622027707722239457867)
          ·
            refine ⟨3725433041561583359186801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483622027707722239457867 3725433041561583359186801)
            ·
              refine ⟨2794074781171187519390101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725433041561583359186801 2794074781171187519390101)
              ·
                refine ⟨130972255367399414971411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2794074781171187519390101 130972255367399414971411)
                ·
                  rfl

theorem cell21_1721706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1721706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721706 prefixEnd_1721706 := by exact prefixLift 1721706
  have htrace : WordTrace (prefixWord ++ tailWord_1721706) baseStart_1721706 baseEnd_1721706 := by
    simpa [prefixWord, tailWord_1721706, baseEnd_1721706] using wordTrace_append hprefix tailTrace_1721706
  have hstable : (prefixWord ++ tailWord_1721706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721706).length < 2 ^ (prefixWord ++ tailWord_1721706).sum := by decide
  have hdescent : baseEnd_1721706 < baseStart_1721706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721841 : List Nat := [1, 2, 2, 2, 3, 2, 4, 5]
def baseStart_1721841 : Nat := 118140960795 + 1721841 * 2 ^ 59
def prefixEnd_1721841 : Nat := 4983230072969 + 3 ^ 40 * 1721841 * 2
def baseEnd_1721841 : Nat := 130982524980489336721319

theorem tailTrace_1721841 : CollatzResearch.WordTrace tailWord_1721841 prefixEnd_1721841 130982524980489336721319 := by
  unfold tailWord_1721841
  simp only [CollatzResearch.WordTrace]
  refine ⟨62800700555071598876037377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41867133703381065917358251 62800700555071598876037377)
  ·
    refine ⟨47100525416303699157028033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62800700555071598876037377 47100525416303699157028033)
    ·
      refine ⟨35325394062227774367771025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47100525416303699157028033 35325394062227774367771025)
      ·
        refine ⟨26494045546670830775828269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35325394062227774367771025 26494045546670830775828269)
        ·
          refine ⟨9935267080001561540935601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26494045546670830775828269 9935267080001561540935601)
          ·
            refine ⟨7451450310001171155701701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935267080001561540935601 7451450310001171155701701)
            ·
              refine ⟨1397146933125219591694069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7451450310001171155701701 1397146933125219591694069)
              ·
                refine ⟨130982524980489336721319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1397146933125219591694069 130982524980489336721319)
                ·
                  rfl

theorem cell21_1721841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].length) (baseStart_1721841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721841 prefixEnd_1721841 := by exact prefixLift 1721841
  have htrace : WordTrace (prefixWord ++ tailWord_1721841) baseStart_1721841 baseEnd_1721841 := by
    simpa [prefixWord, tailWord_1721841, baseEnd_1721841] using wordTrace_append hprefix tailTrace_1721841
  have hstable : (prefixWord ++ tailWord_1721841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721841).length < 2 ^ (prefixWord ++ tailWord_1721841).sum := by decide
  have hdescent : baseEnd_1721841 < baseStart_1721841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721858 : List Nat := [3, 4, 1, 2, 1, 3, 7]
def baseStart_1721858 : Nat := 118140960795 + 1721858 * 2 ^ 59
def prefixEnd_1721858 : Nat := 4983230072969 + 3 ^ 40 * 1721858 * 2
def baseEnd_1721858 : Nat := 43661272730342195375621

theorem tailTrace_1721858 : CollatzResearch.WordTrace tailWord_1721858 prefixEnd_1721858 43661272730342195375621 := by
  unfold tailWord_1721858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700330149002502694851557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41867547064006673852937485 15700330149002502694851557)
  ·
    refine ⟨2943811902937969255284667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15700330149002502694851557 2943811902937969255284667)
    ·
      refine ⟨4415717854406953882927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943811902937969255284667 4415717854406953882927001)
      ·
        refine ⟨3311788390805215412195251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4415717854406953882927001 3311788390805215412195251)
        ·
          refine ⟨4967682586207823118292877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311788390805215412195251 4967682586207823118292877)
          ·
            refine ⟨1862880969827933669359829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4967682586207823118292877 1862880969827933669359829)
            ·
              refine ⟨43661272730342195375621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1862880969827933669359829 43661272730342195375621)
              ·
                rfl

theorem cell21_1721858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 7].length) (baseStart_1721858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721858 prefixEnd_1721858 := by exact prefixLift 1721858
  have htrace : WordTrace (prefixWord ++ tailWord_1721858) baseStart_1721858 baseEnd_1721858 := by
    simpa [prefixWord, tailWord_1721858, baseEnd_1721858] using wordTrace_append hprefix tailTrace_1721858
  have hstable : (prefixWord ++ tailWord_1721858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721858).length < 2 ^ (prefixWord ++ tailWord_1721858).sum := by decide
  have hdescent : baseEnd_1721858 < baseStart_1721858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721917 : List Nat := [1, 4, 1, 3, 4, 8]
def baseStart_1721917 : Nat := 118140960795 + 1721917 * 2 ^ 59
def prefixEnd_1721917 : Nat := 4983230072969 + 3 ^ 40 * 1721917 * 2
def baseEnd_1721917 : Nat := 14554256265811435811005

theorem tailTrace_1721917 : CollatzResearch.WordTrace tailWord_1721917 prefixEnd_1721917 14554256265811435811005 := by
  unfold tailWord_1721917
  simp only [CollatzResearch.WordTrace]
  refine ⟨62803472502796263855804005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41868981668530842570536003 62803472502796263855804005)
  ·
    refine ⟨11775651094274299472963251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62803472502796263855804005 11775651094274299472963251)
    ·
      refine ⟨17663476641411449209444877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775651094274299472963251 17663476641411449209444877)
      ·
        refine ⟨6623803740529293453541829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17663476641411449209444877 6623803740529293453541829)
        ·
          refine ⟨1241963201349242522539093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6623803740529293453541829 1241963201349242522539093)
          ·
            refine ⟨14554256265811435811005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1241963201349242522539093 14554256265811435811005)
            ·
              rfl

theorem cell21_1721917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 8].length) (baseStart_1721917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721917 prefixEnd_1721917 := by exact prefixLift 1721917
  have htrace : WordTrace (prefixWord ++ tailWord_1721917) baseStart_1721917 baseEnd_1721917 := by
    simpa [prefixWord, tailWord_1721917, baseEnd_1721917] using wordTrace_append hprefix tailTrace_1721917
  have hstable : (prefixWord ++ tailWord_1721917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721917).length < 2 ^ (prefixWord ++ tailWord_1721917).sum := by decide
  have hdescent : baseEnd_1721917 < baseStart_1721917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721948 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1721948 : Nat := 118140960795 + 1721948 * 2 ^ 59
def prefixEnd_1721948 : Nat := 4983230072969 + 3 ^ 40 * 1721948 * 2
def baseEnd_1721948 : Nat := 392971993799259601880405

theorem tailTrace_1721948 : CollatzResearch.WordTrace tailWord_1721948 prefixEnd_1721948 392971993799259601880405 := by
  unfold tailWord_1721948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31402301582841978075091249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41869735443789304100121665 31402301582841978075091249)
  ·
    refine ⟨23551726187131483556318437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31402301582841978075091249 23551726187131483556318437)
    ·
      refine ⟨4415948660087153166809707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23551726187131483556318437 4415948660087153166809707)
      ·
        refine ⟨6623922990130729750214561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415948660087153166809707 6623922990130729750214561)
        ·
          refine ⟨4967942242598047312660921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6623922990130729750214561 4967942242598047312660921)
          ·
            refine ⟨3725956681948535484495691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967942242598047312660921 3725956681948535484495691)
            ·
              refine ⟨5588935022922803226743537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725956681948535484495691 5588935022922803226743537)
              ·
                refine ⟨4191701267192102420057653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588935022922803226743537 4191701267192102420057653)
                ·
                  refine ⟨392971993799259601880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4191701267192102420057653 392971993799259601880405)
                  ·
                    rfl

theorem cell21_1721948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1721948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1721948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1721948 prefixEnd_1721948 := by exact prefixLift 1721948
  have htrace : WordTrace (prefixWord ++ tailWord_1721948) baseStart_1721948 baseEnd_1721948 := by
    simpa [prefixWord, tailWord_1721948, baseEnd_1721948] using wordTrace_append hprefix tailTrace_1721948
  have hstable : (prefixWord ++ tailWord_1721948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721948).length < 2 ^ (prefixWord ++ tailWord_1721948).sum := by decide
  have hdescent : baseEnd_1721948 < baseStart_1721948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722007 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_1722007 : Nat := 118140960795 + 1722007 * 2 ^ 59
def prefixEnd_1722007 : Nat := 4983230072969 + 3 ^ 40 * 1722007 * 2
def baseEnd_1722007 : Nat := 392985458403088610396951

theorem tailTrace_1722007 : CollatzResearch.WordTrace tailWord_1722007 prefixEnd_1722007 392985458403088610396951 := by
  unfold tailWord_1722007
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806755072470209226580275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41871170048313472817720183 62806755072470209226580275)
  ·
    refine ⟨94210132608705313839870413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62806755072470209226580275 94210132608705313839870413)
    ·
      refine ⟨35328799728264492689951405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94210132608705313839870413 35328799728264492689951405)
      ·
        refine ⟨13248299898099184758731777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35328799728264492689951405 13248299898099184758731777)
        ·
          refine ⟨9936224923574388569048833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13248299898099184758731777 9936224923574388569048833)
          ·
            refine ⟨7452168692680791426786625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9936224923574388569048833 7452168692680791426786625)
            ·
              refine ⟨5589126519510593570089969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452168692680791426786625 5589126519510593570089969)
              ·
                refine ⟨4191844889632945177567477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589126519510593570089969 4191844889632945177567477)
                ·
                  refine ⟨392985458403088610396951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4191844889632945177567477 392985458403088610396951)
                  ·
                    rfl

theorem cell21_1722007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_1722007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722007 prefixEnd_1722007 := by exact prefixLift 1722007
  have htrace : WordTrace (prefixWord ++ tailWord_1722007) baseStart_1722007 baseEnd_1722007 := by
    simpa [prefixWord, tailWord_1722007, baseEnd_1722007] using wordTrace_append hprefix tailTrace_1722007
  have hstable : (prefixWord ++ tailWord_1722007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722007).length < 2 ^ (prefixWord ++ tailWord_1722007).sum := by decide
  have hdescent : baseEnd_1722007 < baseStart_1722007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722021 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1722021 : Nat := 118140960795 + 1722021 * 2 ^ 59
def prefixEnd_1722021 : Nat := 4983230072969 + 3 ^ 40 * 1722021 * 2
def baseEnd_1722021 : Nat := 392988653393827697163589

theorem tailTrace_1722021 : CollatzResearch.WordTrace tailWord_1722021 prefixEnd_1722021 392988653393827697163589 := by
  unfold tailWord_1722021
  simp only [CollatzResearch.WordTrace]
  refine ⟨62807265694419489617589917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41871510462946326411726611 62807265694419489617589917)
  ·
    refine ⟨23552724635407308606596219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62807265694419489617589917 23552724635407308606596219)
    ·
      refine ⟨35329086953110962909894329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23552724635407308606596219 35329086953110962909894329)
      ·
        refine ⟨26496815214833222182420747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35329086953110962909894329 26496815214833222182420747)
        ·
          refine ⟨39745222822249833273631121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26496815214833222182420747 39745222822249833273631121)
          ·
            refine ⟨29808917116687374955223341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39745222822249833273631121 29808917116687374955223341)
            ·
              refine ⟨11178343918757765608208753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29808917116687374955223341 11178343918757765608208753)
              ·
                refine ⟨8383757939068324206156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178343918757765608208753 8383757939068324206156565)
                ·
                  refine ⟨392988653393827697163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8383757939068324206156565 392988653393827697163589)
                  ·
                    rfl

theorem cell21_1722021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1722021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722021 prefixEnd_1722021 := by exact prefixLift 1722021
  have htrace : WordTrace (prefixWord ++ tailWord_1722021) baseStart_1722021 baseEnd_1722021 := by
    simpa [prefixWord, tailWord_1722021, baseEnd_1722021] using wordTrace_append hprefix tailTrace_1722021
  have hstable : (prefixWord ++ tailWord_1722021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722021).length < 2 ^ (prefixWord ++ tailWord_1722021).sum := by decide
  have hdescent : baseEnd_1722021 < baseStart_1722021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722193 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 3]
def baseStart_1722193 : Nat := 118140960795 + 1722193 * 2 ^ 59
def prefixEnd_1722193 : Nat := 4983230072969 + 3 ^ 40 * 1722193 * 2
def baseEnd_1722193 : Nat := 393027906137193620296571

theorem tailTrace_1722193 : CollatzResearch.WordTrace tailWord_1722193 prefixEnd_1722193 393027906137193620296571 := by
  unfold tailWord_1722193
  simp only [CollatzResearch.WordTrace]
  refine ⟨62813539049796362992851233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41875692699864241995234155 62813539049796362992851233)
  ·
    refine ⟨47110154287347272244638425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62813539049796362992851233 47110154287347272244638425)
    ·
      refine ⟨35332615715510454183478819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47110154287347272244638425 35332615715510454183478819)
      ·
        refine ⟨52998923573265681275218229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35332615715510454183478819 52998923573265681275218229)
        ·
          refine ⟨4968649084993657619551709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52998923573265681275218229 4968649084993657619551709)
          ·
            refine ⟨1863243406872621607331891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4968649084993657619551709 1863243406872621607331891)
            ·
              refine ⟨2794865110308932410997837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863243406872621607331891 2794865110308932410997837)
              ·
                refine ⟨1048074416365849654124189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2794865110308932410997837 1048074416365849654124189)
                ·
                  refine ⟨393027906137193620296571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048074416365849654124189 393027906137193620296571)
                  ·
                    rfl

theorem cell21_1722193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_1722193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722193 prefixEnd_1722193 := by exact prefixLift 1722193
  have htrace : WordTrace (prefixWord ++ tailWord_1722193) baseStart_1722193 baseEnd_1722193 := by
    simpa [prefixWord, tailWord_1722193, baseEnd_1722193] using wordTrace_append hprefix tailTrace_1722193
  have hstable : (prefixWord ++ tailWord_1722193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722193).length < 2 ^ (prefixWord ++ tailWord_1722193).sum := by decide
  have hdescent : baseEnd_1722193 < baseStart_1722193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722210 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1722210 : Nat := 118140960795 + 1722210 * 2 ^ 59
def prefixEnd_1722210 : Nat := 4983230072969 + 3 ^ 40 * 1722210 * 2
def baseEnd_1722210 : Nat := 393031785768805368513203

theorem tailTrace_1722210 : CollatzResearch.WordTrace tailWord_1722210 prefixEnd_1722210 393031785768805368513203 := by
  unfold tailWord_1722210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703539772683693724055021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41876106060489849930813389 15703539772683693724055021)
  ·
    refine ⟨5888827414756385146520633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15703539772683693724055021 5888827414756385146520633)
    ·
      refine ⟨4416620561067288859890475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888827414756385146520633 4416620561067288859890475)
      ·
        refine ⟨6624930841600933289835713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416620561067288859890475 6624930841600933289835713)
        ·
          refine ⟨4968698131200699967376785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6624930841600933289835713 4968698131200699967376785)
          ·
            refine ⟨3726523598400524975532589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4968698131200699967376785 3726523598400524975532589)
            ·
              refine ⟨1397446349400196865824721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3726523598400524975532589 1397446349400196865824721)
              ·
                refine ⟨1048084762050147649368541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397446349400196865824721 1048084762050147649368541)
                ·
                  refine ⟨393031785768805368513203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048084762050147649368541 393031785768805368513203)
                  ·
                    rfl

theorem cell21_1722210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1722210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722210 prefixEnd_1722210 := by exact prefixLift 1722210
  have htrace : WordTrace (prefixWord ++ tailWord_1722210) baseStart_1722210 baseEnd_1722210 := by
    simpa [prefixWord, tailWord_1722210, baseEnd_1722210] using wordTrace_append hprefix tailTrace_1722210
  have hstable : (prefixWord ++ tailWord_1722210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722210).length < 2 ^ (prefixWord ++ tailWord_1722210).sum := by decide
  have hdescent : baseEnd_1722210 < baseStart_1722210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722263 : List Nat := [1, 1, 3, 3, 1, 12]
def baseStart_1722263 : Nat := 118140960795 + 1722263 * 2 ^ 59
def prefixEnd_1722263 : Nat := 4983230072969 + 3 ^ 40 * 1722263 * 2
def baseEnd_1722263 : Nat := 14557180781144039041843

theorem tailTrace_1722263 : CollatzResearch.WordTrace tailWord_1722263 prefixEnd_1722263 14557180781144039041843 := by
  unfold tailWord_1722263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62816092159542764947899443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41877394773028509965266295 62816092159542764947899443)
  ·
    refine ⟨94224138239314147421849165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62816092159542764947899443 94224138239314147421849165)
    ·
      refine ⟨35334051839742805283193437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94224138239314147421849165 35334051839742805283193437)
      ·
        refine ⟨13250269439903551981197539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35334051839742805283193437 13250269439903551981197539)
        ·
          refine ⟨19875404159855327971796309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13250269439903551981197539 19875404159855327971796309)
          ·
            refine ⟨14557180781144039041843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19875404159855327971796309 14557180781144039041843)
            ·
              rfl

theorem cell21_1722263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 12].length) (baseStart_1722263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722263 prefixEnd_1722263 := by exact prefixLift 1722263
  have htrace : WordTrace (prefixWord ++ tailWord_1722263) baseStart_1722263 baseEnd_1722263 := by
    simpa [prefixWord, tailWord_1722263, baseEnd_1722263] using wordTrace_append hprefix tailTrace_1722263
  have hstable : (prefixWord ++ tailWord_1722263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722263).length < 2 ^ (prefixWord ++ tailWord_1722263).sum := by decide
  have hdescent : baseEnd_1722263 < baseStart_1722263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722266 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1722266 : Nat := 118140960795 + 1722266 * 2 ^ 59
def prefixEnd_1722266 : Nat := 4983230072969 + 3 ^ 40 * 1722266 * 2
def baseEnd_1722266 : Nat := 393044565731761715579755

theorem tailTrace_1722266 : CollatzResearch.WordTrace tailWord_1722266 prefixEnd_1722266 393044565731761715579755 := by
  unfold tailWord_1722266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704050394632974115064663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41877467719021264306839101 15704050394632974115064663)
  ·
    refine ⟨23556075591949461172596995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15704050394632974115064663 23556075591949461172596995)
    ·
      refine ⟨35334113387924191758895493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23556075591949461172596995 35334113387924191758895493)
      ·
        refine ⟨6625146260235785954792905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35334113387924191758895493 6625146260235785954792905)
        ·
          refine ⟨4968859695176839466094679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6625146260235785954792905 4968859695176839466094679)
          ·
            refine ⟨7453289542765259199142019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968859695176839466094679 7453289542765259199142019)
            ·
              refine ⟨11179934314147888798713029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453289542765259199142019 11179934314147888798713029)
              ·
                refine ⟨2096237683902729149758693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11179934314147888798713029 2096237683902729149758693)
                ·
                  refine ⟨393044565731761715579755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2096237683902729149758693 393044565731761715579755)
                  ·
                    rfl

theorem cell21_1722266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1722266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722266 prefixEnd_1722266 := by exact prefixLift 1722266
  have htrace : WordTrace (prefixWord ++ tailWord_1722266) baseStart_1722266 baseEnd_1722266 := by
    simpa [prefixWord, tailWord_1722266, baseEnd_1722266] using wordTrace_append hprefix tailTrace_1722266
  have hstable : (prefixWord ++ tailWord_1722266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722266).length < 2 ^ (prefixWord ++ tailWord_1722266).sum := by decide
  have hdescent : baseEnd_1722266 < baseStart_1722266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722269 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1722269 : Nat := 118140960795 + 1722269 * 2 ^ 59
def prefixEnd_1722269 : Nat := 4983230072969 + 3 ^ 40 * 1722269 * 2
def baseEnd_1722269 : Nat := 393045250372634377029749

theorem tailTrace_1722269 : CollatzResearch.WordTrace tailWord_1722269 prefixEnd_1722269 393045250372634377029749 := by
  unfold tailWord_1722269
  simp only [CollatzResearch.WordTrace]
  refine ⟨62816310997521027972617861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41877540665014018648411907 62816310997521027972617861)
  ·
    refine ⟨11778058312035192744865849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62816310997521027972617861 11778058312035192744865849)
    ·
      refine ⟨8833543734026394558649387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778058312035192744865849 8833543734026394558649387)
      ·
        refine ⟨13250315601039591837974081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833543734026394558649387 13250315601039591837974081)
        ·
          refine ⟨9937736700779693878480561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13250315601039591837974081 9937736700779693878480561)
          ·
            refine ⟨7453302525584770408860421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9937736700779693878480561 7453302525584770408860421)
            ·
              refine ⟨1397494223547144451661329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7453302525584770408860421 1397494223547144451661329)
              ·
                refine ⟨1048120667660358338745997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397494223547144451661329 1048120667660358338745997)
                ·
                  refine ⟨393045250372634377029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048120667660358338745997 393045250372634377029749)
                  ·
                    rfl

theorem cell21_1722269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1722269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722269 prefixEnd_1722269 := by exact prefixLift 1722269
  have htrace : WordTrace (prefixWord ++ tailWord_1722269) baseStart_1722269 baseEnd_1722269 := by
    simpa [prefixWord, tailWord_1722269, baseEnd_1722269] using wordTrace_append hprefix tailTrace_1722269
  have hstable : (prefixWord ++ tailWord_1722269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722269).length < 2 ^ (prefixWord ++ tailWord_1722269).sum := by decide
  have hdescent : baseEnd_1722269 < baseStart_1722269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722286 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1722286 : Nat := 118140960795 + 1722286 * 2 ^ 59
def prefixEnd_1722286 : Nat := 4983230072969 + 3 ^ 40 * 1722286 * 2
def baseEnd_1722286 : Nat := 393049130004246125246381

theorem tailTrace_1722286 : CollatzResearch.WordTrace tailWord_1722286 prefixEnd_1722286 393049130004246125246381 := by
  unfold tailWord_1722286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852116379807429984498339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41877954025639626583991141 7852116379807429984498339)
  ·
    refine ⟨11778174569711144976747509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7852116379807429984498339 11778174569711144976747509)
    ·
      refine ⟨1104203865910419841570079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11778174569711144976747509 1104203865910419841570079)
      ·
        refine ⟨1656305798865629762355119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104203865910419841570079 1656305798865629762355119)
        ·
          refine ⟨2484458698298444643532679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656305798865629762355119 2484458698298444643532679)
          ·
            refine ⟨3726688047447666965299019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484458698298444643532679 3726688047447666965299019)
            ·
              refine ⟨5590032071171500447948529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726688047447666965299019 5590032071171500447948529)
              ·
                refine ⟨4192524053378625335961397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590032071171500447948529 4192524053378625335961397)
                ·
                  refine ⟨393049130004246125246381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4192524053378625335961397 393049130004246125246381)
                  ·
                    rfl

theorem cell21_1722286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1722286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722286 prefixEnd_1722286 := by exact prefixLift 1722286
  have htrace : WordTrace (prefixWord ++ tailWord_1722286) baseStart_1722286 baseEnd_1722286 := by
    simpa [prefixWord, tailWord_1722286, baseEnd_1722286] using wordTrace_append hprefix tailTrace_1722286
  have hstable : (prefixWord ++ tailWord_1722286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722286).length < 2 ^ (prefixWord ++ tailWord_1722286).sum := by decide
  have hdescent : baseEnd_1722286 < baseStart_1722286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722387 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 3]
def baseStart_1722387 : Nat := 118140960795 + 1722387 * 2 ^ 59
def prefixEnd_1722387 : Nat := 4983230072969 + 3 ^ 40 * 1722387 * 2
def baseEnd_1722387 : Nat := 393072179580292394062841

theorem tailTrace_1722387 : CollatzResearch.WordTrace tailWord_1722387 prefixEnd_1722387 393072179580292394062841 := by
  unfold tailWord_1722387
  simp only [CollatzResearch.WordTrace]
  refine ⟨62820614811093534125413415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41880409874062356083608943 62820614811093534125413415)
  ·
    refine ⟨94230922216640301188120123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62820614811093534125413415 94230922216640301188120123)
    ·
      refine ⟨141346383324960451782180185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94230922216640301188120123 141346383324960451782180185)
      ·
        refine ⟨106009787493720338836635139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141346383324960451782180185 106009787493720338836635139)
        ·
          refine ⟨159014681240580508254952709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106009787493720338836635139 159014681240580508254952709)
          ·
            refine ⟨29815252732608845297803633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159014681240580508254952709 29815252732608845297803633)
            ·
              refine ⟨22361439549456633973352725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29815252732608845297803633 22361439549456633973352725)
              ·
                refine ⟨1048192478880779717500909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22361439549456633973352725 1048192478880779717500909)
                ·
                  refine ⟨393072179580292394062841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048192478880779717500909 393072179580292394062841)
                  ·
                    rfl

theorem cell21_1722387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].length) (baseStart_1722387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722387 prefixEnd_1722387 := by exact prefixLift 1722387
  have htrace : WordTrace (prefixWord ++ tailWord_1722387) baseStart_1722387 baseEnd_1722387 := by
    simpa [prefixWord, tailWord_1722387, baseEnd_1722387] using wordTrace_append hprefix tailTrace_1722387
  have hstable : (prefixWord ++ tailWord_1722387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722387).length < 2 ^ (prefixWord ++ tailWord_1722387).sum := by decide
  have hdescent : baseEnd_1722387 < baseStart_1722387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722466 : List Nat := [3, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1722466 : Nat := 118140960795 + 1722466 * 2 ^ 59
def prefixEnd_1722466 : Nat := 4983230072969 + 3 ^ 40 * 1722466 * 2
def baseEnd_1722466 : Nat := 131030069485535270748671

theorem tailTrace_1722466 : CollatzResearch.WordTrace tailWord_1722466 prefixEnd_1722466 131030069485535270748671 := by
  unfold tailWord_1722466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705874044451832654384813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41882330785204887078359501 15705874044451832654384813)
  ·
    refine ⟨5889702766669437245394305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15705874044451832654384813 5889702766669437245394305)
    ·
      refine ⟨4417277075002077934045729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5889702766669437245394305 4417277075002077934045729)
      ·
        refine ⟨3312957806251558450534297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4417277075002077934045729 3312957806251558450534297)
        ·
          refine ⟨2484718354688668837900723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312957806251558450534297 2484718354688668837900723)
          ·
            refine ⟨3727077532033003256851085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484718354688668837900723 3727077532033003256851085)
            ·
              refine ⟨1397654074512376221319157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3727077532033003256851085 1397654074512376221319157)
              ·
                refine ⟨131030069485535270748671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1397654074512376221319157 131030069485535270748671)
                ·
                  rfl

theorem cell21_1722466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1722466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722466 prefixEnd_1722466 := by exact prefixLift 1722466
  have htrace : WordTrace (prefixWord ++ tailWord_1722466) baseStart_1722466 baseEnd_1722466 := by
    simpa [prefixWord, tailWord_1722466, baseEnd_1722466] using wordTrace_append hprefix tailTrace_1722466
  have hstable : (prefixWord ++ tailWord_1722466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722466).length < 2 ^ (prefixWord ++ tailWord_1722466).sum := by decide
  have hdescent : baseEnd_1722466 < baseStart_1722466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722477 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1722477 : Nat := 118140960795 + 1722477 * 2 ^ 59
def prefixEnd_1722477 : Nat := 4983230072969 + 3 ^ 40 * 1722477 * 2
def baseEnd_1722477 : Nat := 393092718806472237562657

theorem tailTrace_1722477 : CollatzResearch.WordTrace tailWord_1722477 prefixEnd_1722477 393092718806472237562657 := by
  unfold tailWord_1722477
  simp only [CollatzResearch.WordTrace]
  refine ⟨62823897380767479496189685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41882598253844986330793123 62823897380767479496189685)
  ·
    refine ⟨5889740379446951202767783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62823897380767479496189685 5889740379446951202767783)
    ·
      refine ⟨8834610569170426804151675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889740379446951202767783 8834610569170426804151675)
      ·
        refine ⟨13251915853755640206227513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834610569170426804151675 13251915853755640206227513)
        ·
          refine ⟨9938936890316730154670635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13251915853755640206227513 9938936890316730154670635)
          ·
            refine ⟨14908405335475095232005953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938936890316730154670635 14908405335475095232005953)
            ·
              refine ⟨11181304001606321424004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14908405335475095232005953 11181304001606321424004465)
              ·
                refine ⟨8385978001204741068003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11181304001606321424004465 8385978001204741068003349)
                ·
                  refine ⟨393092718806472237562657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8385978001204741068003349 393092718806472237562657)
                  ·
                    rfl

theorem cell21_1722477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1722477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722477 prefixEnd_1722477 := by exact prefixLift 1722477
  have htrace : WordTrace (prefixWord ++ tailWord_1722477) baseStart_1722477 baseEnd_1722477 := by
    simpa [prefixWord, tailWord_1722477, baseEnd_1722477] using wordTrace_append hprefix tailTrace_1722477
  have hstable : (prefixWord ++ tailWord_1722477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722477).length < 2 ^ (prefixWord ++ tailWord_1722477).sum := by decide
  have hdescent : baseEnd_1722477 < baseStart_1722477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722480 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_1722480 : Nat := 118140960795 + 1722480 * 2 ^ 59
def prefixEnd_1722480 : Nat := 4983230072969 + 3 ^ 40 * 1722480 * 2
def baseEnd_1722480 : Nat := 393093403447344899012651

theorem tailTrace_1722480 : CollatzResearch.WordTrace tailWord_1722480 prefixEnd_1722480 393093403447344899012651 := by
  unfold tailWord_1722480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412003399878305504274447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41882671199837740672365929 31412003399878305504274447)
  ·
    refine ⟨47118005099817458256411671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31412003399878305504274447 47118005099817458256411671)
    ·
      refine ⟨70677007649726187384617507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47118005099817458256411671 70677007649726187384617507)
      ·
        refine ⟨106015511474589281076926261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70677007649726187384617507 106015511474589281076926261)
        ·
          refine ⟨9938954200742745100961837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106015511474589281076926261 9938954200742745100961837)
          ·
            refine ⟨3727107825278529412860689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9938954200742745100961837 3727107825278529412860689)
            ·
              refine ⟨2795330868958897059645517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727107825278529412860689 2795330868958897059645517)
              ·
                refine ⟨1048249075859586397367069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795330868958897059645517 1048249075859586397367069)
                ·
                  refine ⟨393093403447344899012651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048249075859586397367069 393093403447344899012651)
                  ·
                    rfl

theorem cell21_1722480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_1722480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722480 prefixEnd_1722480 := by exact prefixLift 1722480
  have htrace : WordTrace (prefixWord ++ tailWord_1722480) baseStart_1722480 baseEnd_1722480 := by
    simpa [prefixWord, tailWord_1722480, baseEnd_1722480] using wordTrace_append hprefix tailTrace_1722480
  have hstable : (prefixWord ++ tailWord_1722480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722480).length < 2 ^ (prefixWord ++ tailWord_1722480).sum := by decide
  have hdescent : baseEnd_1722480 < baseStart_1722480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722525 : List Nat := [1, 4, 2, 1, 1, 5, 2, 5]
def baseStart_1722525 : Nat := 118140960795 + 1722525 * 2 ^ 59
def prefixEnd_1722525 : Nat := 4983230072969 + 3 ^ 40 * 1722525 * 2
def baseEnd_1722525 : Nat := 131034557686811606920853

theorem tailTrace_1722525 : CollatzResearch.WordTrace tailWord_1722525 prefixEnd_1722525 131034557686811606920853 := by
  unfold tailWord_1722525
  simp only [CollatzResearch.WordTrace]
  refine ⟨62825648084593583693937029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41883765389729055795958019 62825648084593583693937029)
  ·
    refine ⟨11779809015861296942613193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62825648084593583693937029 11779809015861296942613193)
    ·
      refine ⟨8834856761895972706959895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11779809015861296942613193 8834856761895972706959895)
      ·
        refine ⟨13252285142843959060439843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834856761895972706959895 13252285142843959060439843)
        ·
          refine ⟨19878427714265938590659765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252285142843959060439843 19878427714265938590659765)
          ·
            refine ⟨1863602598212431742874353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19878427714265938590659765 1863602598212431742874353)
            ·
              refine ⟨1397701948659323807155765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863602598212431742874353 1397701948659323807155765)
              ·
                refine ⟨131034557686811606920853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1397701948659323807155765 131034557686811606920853)
                ·
                  rfl

theorem cell21_1722525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].length) (baseStart_1722525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722525 prefixEnd_1722525 := by exact prefixLift 1722525
  have htrace : WordTrace (prefixWord ++ tailWord_1722525) baseStart_1722525 baseEnd_1722525 := by
    simpa [prefixWord, tailWord_1722525, baseEnd_1722525] using wordTrace_append hprefix tailTrace_1722525
  have hstable : (prefixWord ++ tailWord_1722525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722525).length < 2 ^ (prefixWord ++ tailWord_1722525).sum := by decide
  have hdescent : baseEnd_1722525 < baseStart_1722525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722542 : List Nat := [4, 1, 4, 2, 1, 2, 7]
def baseStart_1722542 : Nat := 118140960795 + 1722542 * 2 ^ 59
def prefixEnd_1722542 : Nat := 4983230072969 + 3 ^ 40 * 1722542 * 2
def baseEnd_1722542 : Nat := 43678616965782952108799

theorem tailTrace_1722542 : CollatzResearch.WordTrace tailWord_1722542 prefixEnd_1722542 43678616965782952108799 := by
  unfold tailWord_1722542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853283515691499449663235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41884178750354663731537253 7853283515691499449663235)
  ·
    refine ⟨11779925273537249174494853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853283515691499449663235 11779925273537249174494853)
    ·
      refine ⟨2208735988788234220217785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11779925273537249174494853 2208735988788234220217785)
      ·
        refine ⟨1656551991591175665163339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208735988788234220217785 1656551991591175665163339)
        ·
          refine ⟨2484827987386763497745009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656551991591175665163339 2484827987386763497745009)
          ·
            refine ⟨1863620990540072623308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484827987386763497745009 1863620990540072623308757)
            ·
              refine ⟨43678616965782952108799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1863620990540072623308757 43678616965782952108799)
              ·
                rfl

theorem cell21_1722542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 7].length) (baseStart_1722542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722542 prefixEnd_1722542 := by exact prefixLift 1722542
  have htrace : WordTrace (prefixWord ++ tailWord_1722542) baseStart_1722542 baseEnd_1722542 := by
    simpa [prefixWord, tailWord_1722542, baseEnd_1722542] using wordTrace_append hprefix tailTrace_1722542
  have hstable : (prefixWord ++ tailWord_1722542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722542).length < 2 ^ (prefixWord ++ tailWord_1722542).sum := by decide
  have hdescent : baseEnd_1722542 < baseStart_1722542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722548 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1722548 : Nat := 118140960795 + 1722548 * 2 ^ 59
def prefixEnd_1722548 : Nat := 4983230072969 + 3 ^ 40 * 1722548 * 2
def baseEnd_1722548 : Nat := 393108921973791891879179

theorem tailTrace_1722548 : CollatzResearch.WordTrace tailWord_1722548 prefixEnd_1722548 393108921973791891879179 := by
  unfold tailWord_1722548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31413243481755129311012149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41884324642340172414682865 31413243481755129311012149)
  ·
    refine ⟨2944991576414543372907389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31413243481755129311012149 2944991576414543372907389)
    ·
      refine ⟨1104371841155453764840271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2944991576414543372907389 1104371841155453764840271)
      ·
        refine ⟨1656557761733180647260407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104371841155453764840271 1656557761733180647260407)
        ·
          refine ⟨2484836642599770970890611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656557761733180647260407 2484836642599770970890611)
          ·
            refine ⟨3727254963899656456335917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484836642599770970890611 3727254963899656456335917)
            ·
              refine ⟨1397720611462371171125969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3727254963899656456335917 1397720611462371171125969)
              ·
                refine ⟨1048290458596778378344477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397720611462371171125969 1048290458596778378344477)
                ·
                  refine ⟨393108921973791891879179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048290458596778378344477 393108921973791891879179)
                  ·
                    rfl

theorem cell21_1722548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1722548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722548 prefixEnd_1722548 := by exact prefixLift 1722548
  have htrace : WordTrace (prefixWord ++ tailWord_1722548) baseStart_1722548 baseEnd_1722548 := by
    simpa [prefixWord, tailWord_1722548, baseEnd_1722548] using wordTrace_append hprefix tailTrace_1722548
  have hstable : (prefixWord ++ tailWord_1722548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722548).length < 2 ^ (prefixWord ++ tailWord_1722548).sum := by decide
  have hdescent : baseEnd_1722548 < baseStart_1722548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722553 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_1722553 : Nat := 118140960795 + 1722553 * 2 ^ 59
def prefixEnd_1722553 : Nat := 4983230072969 + 3 ^ 40 * 1722553 * 2
def baseEnd_1722553 : Nat := 393110063041912994295835

theorem tailTrace_1722553 : CollatzResearch.WordTrace tailWord_1722553 prefixEnd_1722553 393110063041912994295835 := by
  unfold tailWord_1722553
  simp only [CollatzResearch.WordTrace]
  refine ⟨62826669328492144475956313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41884446218994762983970875 62826669328492144475956313)
  ·
    refine ⟨47120001996369108356967235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62826669328492144475956313 47120001996369108356967235)
    ·
      refine ⟨70680002994553662535450853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47120001996369108356967235 70680002994553662535450853)
      ·
        refine ⟨13252500561478811725397035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70680002994553662535450853 13252500561478811725397035)
        ·
          refine ⟨19878750842218217588095553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252500561478811725397035 19878750842218217588095553)
          ·
            refine ⟨14909063131663663191071665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19878750842218217588095553 14909063131663663191071665)
            ·
              refine ⟨11181797348747747393303749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14909063131663663191071665 11181797348747747393303749)
              ·
                refine ⟨2096587002890202636244453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11181797348747747393303749 2096587002890202636244453)
                ·
                  refine ⟨393110063041912994295835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2096587002890202636244453 393110063041912994295835)
                  ·
                    rfl

theorem cell21_1722553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_1722553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722553 prefixEnd_1722553 := by exact prefixLift 1722553
  have htrace : WordTrace (prefixWord ++ tailWord_1722553) baseStart_1722553 baseEnd_1722553 := by
    simpa [prefixWord, tailWord_1722553, baseEnd_1722553] using wordTrace_append hprefix tailTrace_1722553
  have hstable : (prefixWord ++ tailWord_1722553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722553).length < 2 ^ (prefixWord ++ tailWord_1722553).sum := by decide
  have hdescent : baseEnd_1722553 < baseStart_1722553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722556 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1722556 : Nat := 118140960795 + 1722556 * 2 ^ 59
def prefixEnd_1722556 : Nat := 4983230072969 + 3 ^ 40 * 1722556 * 2
def baseEnd_1722556 : Nat := 393110747682785655745829

theorem tailTrace_1722556 : CollatzResearch.WordTrace tailWord_1722556 prefixEnd_1722556 393110747682785655745829 := by
  unfold tailWord_1722556
  simp only [CollatzResearch.WordTrace]
  refine ⟨31413389373740637994157761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41884519164987517325543681 31413389373740637994157761)
  ·
    refine ⟨23560042030305478495618321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31413389373740637994157761 23560042030305478495618321)
    ·
      refine ⟨17670031522729108871713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23560042030305478495618321 17670031522729108871713741)
      ·
        refine ⟨6626261821023415826892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17670031522729108871713741 6626261821023415826892653)
        ·
          refine ⟨2484848182883780935084745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6626261821023415826892653 2484848182883780935084745)
          ·
            refine ⟨1863636137162835701313559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484848182883780935084745 1863636137162835701313559)
            ·
              refine ⟨2795454205744253551970339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863636137162835701313559 2795454205744253551970339)
              ·
                refine ⟨4193181308616380327955509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795454205744253551970339 4193181308616380327955509)
                ·
                  refine ⟨393110747682785655745829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4193181308616380327955509 393110747682785655745829)
                  ·
                    rfl

theorem cell21_1722556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1722556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722556 prefixEnd_1722556 := by exact prefixLift 1722556
  have htrace : WordTrace (prefixWord ++ tailWord_1722556) baseStart_1722556 baseEnd_1722556 := by
    simpa [prefixWord, tailWord_1722556, baseEnd_1722556] using wordTrace_append hprefix tailTrace_1722556
  have hstable : (prefixWord ++ tailWord_1722556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722556).length < 2 ^ (prefixWord ++ tailWord_1722556).sum := by decide
  have hdescent : baseEnd_1722556 < baseStart_1722556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722708 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1722708 : Nat := 118140960795 + 1722708 * 2 ^ 59
def prefixEnd_1722708 : Nat := 4983230072969 + 3 ^ 40 * 1722708 * 2
def baseEnd_1722708 : Nat := 393145436153667169212185

theorem tailTrace_1722708 : CollatzResearch.WordTrace tailWord_1722708 prefixEnd_1722708 393145436153667169212185 := by
  unfold tailWord_1722708
  simp only [CollatzResearch.WordTrace]
  refine ⟨31416161321465302973924389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41888215095287070631899185 31416161321465302973924389)
  ·
    refine ⟨5890530247774744307610823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31416161321465302973924389 5890530247774744307610823)
    ·
      refine ⟨8835795371662116461416235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890530247774744307610823 8835795371662116461416235)
      ·
        refine ⟨13253693057493174692124353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835795371662116461416235 13253693057493174692124353)
        ·
          refine ⟨9940269793119881019093265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13253693057493174692124353 9940269793119881019093265)
          ·
            refine ⟨7455202344839910764319949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9940269793119881019093265 7455202344839910764319949)
            ·
              refine ⟨2795700879314966536619981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7455202344839910764319949 2795700879314966536619981)
              ·
                refine ⟨1048387829743112451232493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795700879314966536619981 1048387829743112451232493)
                ·
                  refine ⟨393145436153667169212185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048387829743112451232493 393145436153667169212185)
                  ·
                    rfl

theorem cell21_1722708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1722708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722708 prefixEnd_1722708 := by exact prefixLift 1722708
  have htrace : WordTrace (prefixWord ++ tailWord_1722708) baseStart_1722708 baseEnd_1722708 := by
    simpa [prefixWord, tailWord_1722708, baseEnd_1722708] using wordTrace_append hprefix tailTrace_1722708
  have hstable : (prefixWord ++ tailWord_1722708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722708).length < 2 ^ (prefixWord ++ tailWord_1722708).sum := by decide
  have hdescent : baseEnd_1722708 < baseStart_1722708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722784 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_1722784 : Nat := 118140960795 + 1722784 * 2 ^ 59
def prefixEnd_1722784 : Nat := 4983230072969 + 3 ^ 40 * 1722784 * 2
def baseEnd_1722784 : Nat := 393162780389107925945363

theorem tailTrace_1722784 : CollatzResearch.WordTrace tailWord_1722784 prefixEnd_1722784 393162780389107925945363 := by
  unfold tailWord_1722784
  simp only [CollatzResearch.WordTrace]
  refine ⟨31417547295327635463807703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41890063060436847285076937 31417547295327635463807703)
  ·
    refine ⟨47126320942991453195711555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31417547295327635463807703 47126320942991453195711555)
    ·
      refine ⟨70689481414487179793567333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47126320942991453195711555 70689481414487179793567333)
      ·
        refine ⟨13254277765216346211293875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70689481414487179793567333 13254277765216346211293875)
        ·
          refine ⟨19881416647824519316940813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254277765216346211293875 19881416647824519316940813)
          ·
            refine ⟨7455531242934194743852805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19881416647824519316940813 7455531242934194743852805)
            ·
              refine ⟨1397912108050161514472401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7455531242934194743852805 1397912108050161514472401)
              ·
                refine ⟨1048434081037621135854301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397912108050161514472401 1048434081037621135854301)
                ·
                  refine ⟨393162780389107925945363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048434081037621135854301 393162780389107925945363)
                  ·
                    rfl

theorem cell21_1722784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_1722784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722784 prefixEnd_1722784 := by exact prefixLift 1722784
  have htrace : WordTrace (prefixWord ++ tailWord_1722784) baseStart_1722784 baseEnd_1722784 := by
    simpa [prefixWord, tailWord_1722784, baseEnd_1722784] using wordTrace_append hprefix tailTrace_1722784
  have hstable : (prefixWord ++ tailWord_1722784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722784).length < 2 ^ (prefixWord ++ tailWord_1722784).sum := by decide
  have hdescent : baseEnd_1722784 < baseStart_1722784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722885 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1722885 : Nat := 118140960795 + 1722885 * 2 ^ 59
def prefixEnd_1722885 : Nat := 4983230072969 + 3 ^ 40 * 1722885 * 2
def baseEnd_1722885 : Nat := 393185829965154194761823

theorem tailTrace_1722885 : CollatzResearch.WordTrace tailWord_1722885 prefixEnd_1722885 393185829965154194761823 := by
  unfold tailWord_1722885
  simp only [CollatzResearch.WordTrace]
  refine ⟨62838778363289365177042109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41892518908859576784694739 62838778363289365177042109)
  ·
    refine ⟨23564541886233511941390791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62838778363289365177042109 23564541886233511941390791)
    ·
      refine ⟨35346812829350267912086187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23564541886233511941390791 35346812829350267912086187)
      ·
        refine ⟨53020219244025401868129281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35346812829350267912086187 53020219244025401868129281)
        ·
          refine ⟨39765164433019051401096961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53020219244025401868129281 39765164433019051401096961)
          ·
            refine ⟨29823873324764288550822721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39765164433019051401096961 29823873324764288550822721)
            ·
              refine ⟨22367904993573216413117041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29823873324764288550822721 22367904993573216413117041)
              ·
                refine ⟨16775928745179912309837781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22367904993573216413117041 16775928745179912309837781)
                ·
                  refine ⟨393185829965154194761823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16775928745179912309837781 393185829965154194761823)
                  ·
                    rfl

theorem cell21_1722885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1722885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722885 prefixEnd_1722885 := by exact prefixLift 1722885
  have htrace : WordTrace (prefixWord ++ tailWord_1722885) baseStart_1722885 baseEnd_1722885 := by
    simpa [prefixWord, tailWord_1722885, baseEnd_1722885] using wordTrace_append hprefix tailTrace_1722885
  have hstable : (prefixWord ++ tailWord_1722885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722885).length < 2 ^ (prefixWord ++ tailWord_1722885).sum := by decide
  have hdescent : baseEnd_1722885 < baseStart_1722885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722964 : List Nat := [2, 4, 1, 1, 1, 5, 1, 6]
def baseStart_1722964 : Nat := 118140960795 + 1722964 * 2 ^ 59
def prefixEnd_1722964 : Nat := 4983230072969 + 3 ^ 40 * 1722964 * 2
def baseEnd_1722964 : Nat := 131067952947155870981665

theorem tailTrace_1722964 : CollatzResearch.WordTrace tailWord_1722964 prefixEnd_1722964 131067952947155870981665 := by
  unfold tailWord_1722964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420829865001580834583973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41894439820002107779445297 31420829865001580834583973)
  ·
    refine ⟨5891405599687796406484495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31420829865001580834583973 5891405599687796406484495)
    ·
      refine ⟨8837108399531694609726743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891405599687796406484495 8837108399531694609726743)
      ·
        refine ⟨13255662599297541914590115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8837108399531694609726743 13255662599297541914590115)
        ·
          refine ⟨19883493898946312871885173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13255662599297541914590115 19883493898946312871885173)
          ·
            refine ⟨1864077553026216831739235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19883493898946312871885173 1864077553026216831739235)
            ·
              refine ⟨2796116329539325247608853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864077553026216831739235 2796116329539325247608853)
              ·
                refine ⟨131067952947155870981665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2796116329539325247608853 131067952947155870981665)
                ·
                  rfl

theorem cell21_1722964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_1722964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1722964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1722964 prefixEnd_1722964 := by exact prefixLift 1722964
  have htrace : WordTrace (prefixWord ++ tailWord_1722964) baseStart_1722964 baseEnd_1722964 := by
    simpa [prefixWord, tailWord_1722964, baseEnd_1722964] using wordTrace_append hprefix tailTrace_1722964
  have hstable : (prefixWord ++ tailWord_1722964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722964).length < 2 ^ (prefixWord ++ tailWord_1722964).sum := by decide
  have hdescent : baseEnd_1722964 < baseStart_1722964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723057 : List Nat := [1, 2, 2, 6, 2, 1, 7]
def baseStart_1723057 : Nat := 118140960795 + 1723057 * 2 ^ 59
def prefixEnd_1723057 : Nat := 4983230072969 + 3 ^ 40 * 1723057 * 2
def baseEnd_1723057 : Nat := 43691675856502235321645

theorem tailTrace_1723057 : CollatzResearch.WordTrace tailWord_1723057 prefixEnd_1723057 43691675856502235321645 := by
  unfold tailWord_1723057
  simp only [CollatzResearch.WordTrace]
  refine ⟨62845051718666238552303425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41896701145777492368202283 62845051718666238552303425)
  ·
    refine ⟨47133788788999678914227569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62845051718666238552303425 47133788788999678914227569)
    ·
      refine ⟨35350341591749759185670677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47133788788999678914227569 35350341591749759185670677)
      ·
        refine ⟨1657047262113269961828313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35350341591749759185670677 1657047262113269961828313)
        ·
          refine ⟨1242785446584952471371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657047262113269961828313 1242785446584952471371235)
          ·
            refine ⟨1864178169877428707056853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242785446584952471371235 1864178169877428707056853)
            ·
              refine ⟨43691675856502235321645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1864178169877428707056853 43691675856502235321645)
              ·
                rfl

theorem cell21_1723057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 7].length) (baseStart_1723057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723057 prefixEnd_1723057 := by exact prefixLift 1723057
  have htrace : WordTrace (prefixWord ++ tailWord_1723057) baseStart_1723057 baseEnd_1723057 := by
    simpa [prefixWord, tailWord_1723057, baseEnd_1723057] using wordTrace_append hprefix tailTrace_1723057
  have hstable : (prefixWord ++ tailWord_1723057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723057).length < 2 ^ (prefixWord ++ tailWord_1723057).sum := by decide
  have hdescent : baseEnd_1723057 < baseStart_1723057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723068 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1723068 : Nat := 118140960795 + 1723068 * 2 ^ 59
def prefixEnd_1723068 : Nat := 4983230072969 + 3 ^ 40 * 1723068 * 2
def baseEnd_1723068 : Nat := 393227593058386543211449

theorem tailTrace_1723068 : CollatzResearch.WordTrace tailWord_1723068 prefixEnd_1723068 393227593058386543211449 := by
  unfold tailWord_1723068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31422726460813193715476929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41896968614417591620635905 31422726460813193715476929)
  ·
    refine ⟨23567044845609895286607697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31422726460813193715476929 23567044845609895286607697)
    ·
      refine ⟨17675283634207421464955773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23567044845609895286607697 17675283634207421464955773)
      ·
        refine ⟨6628231362827783049358415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17675283634207421464955773 6628231362827783049358415)
        ·
          refine ⟨9942347044241674574037623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628231362827783049358415 9942347044241674574037623)
          ·
            refine ⟨14913520566362511861056435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9942347044241674574037623 14913520566362511861056435)
            ·
              refine ⟨22370280849543767791584653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14913520566362511861056435 22370280849543767791584653)
              ·
                refine ⟨8388855318578912921844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22370280849543767791584653 8388855318578912921844245)
                ·
                  refine ⟨393227593058386543211449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8388855318578912921844245 393227593058386543211449)
                  ·
                    rfl

theorem cell21_1723068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1723068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723068 prefixEnd_1723068 := by exact prefixLift 1723068
  have htrace : WordTrace (prefixWord ++ tailWord_1723068) baseStart_1723068 baseEnd_1723068 := by
    simpa [prefixWord, tailWord_1723068, baseEnd_1723068] using wordTrace_append hprefix tailTrace_1723068
  have hstable : (prefixWord ++ tailWord_1723068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723068).length < 2 ^ (prefixWord ++ tailWord_1723068).sum := by decide
  have hdescent : baseEnd_1723068 < baseStart_1723068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723178 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_1723178 : Nat := 118140960795 + 1723178 * 2 ^ 59
def prefixEnd_1723178 : Nat := 4983230072969 + 3 ^ 40 * 1723178 * 2
def baseEnd_1723178 : Nat := 393252696557050796377891

theorem tailTrace_1723178 : CollatzResearch.WordTrace tailWord_1723178 prefixEnd_1723178 393252696557050796377891 := by
  unfold tailWord_1723178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712366237806969054364547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41899643300818584144972125 15712366237806969054364547)
  ·
    refine ⟨23568549356710453581546821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15712366237806969054364547 23568549356710453581546821)
    ·
      refine ⟨4419103004383210046540029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23568549356710453581546821 4419103004383210046540029)
      ·
        refine ⟨1657163626643703767452511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4419103004383210046540029 1657163626643703767452511)
        ·
          refine ⟨2485745439965555651178767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657163626643703767452511 2485745439965555651178767)
          ·
            refine ⟨3728618159948333476768151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485745439965555651178767 3728618159948333476768151)
            ·
              refine ⟨5592927239922500215152227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728618159948333476768151 5592927239922500215152227)
              ·
                refine ⟨8389390859883750322728341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592927239922500215152227 8389390859883750322728341)
                ·
                  refine ⟨393252696557050796377891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8389390859883750322728341 393252696557050796377891)
                  ·
                    rfl

theorem cell21_1723178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_1723178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723178 prefixEnd_1723178 := by exact prefixLift 1723178
  have htrace : WordTrace (prefixWord ++ tailWord_1723178) baseStart_1723178 baseEnd_1723178 := by
    simpa [prefixWord, tailWord_1723178, baseEnd_1723178] using wordTrace_append hprefix tailTrace_1723178
  have hstable : (prefixWord ++ tailWord_1723178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723178).length < 2 ^ (prefixWord ++ tailWord_1723178).sum := by decide
  have hdescent : baseEnd_1723178 < baseStart_1723178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723223 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 3]
def baseStart_1723223 : Nat := 118140960795 + 1723223 * 2 ^ 59
def prefixEnd_1723223 : Nat := 4983230072969 + 3 ^ 40 * 1723223 * 2
def baseEnd_1723223 : Nat := 393262966170140718127799

theorem tailTrace_1723223 : CollatzResearch.WordTrace tailWord_1723223 prefixEnd_1723223 393262966170140718127799 := by
  unfold tailWord_1723223
  simp only [CollatzResearch.WordTrace]
  refine ⟨62851106236064848902846323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41900737490709899268564215 62851106236064848902846323)
  ·
    refine ⟨94276659354097273354269485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62851106236064848902846323 94276659354097273354269485)
    ·
      refine ⟨35353747257786477507851057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94276659354097273354269485 35353747257786477507851057)
      ·
        refine ⟨26515310443339858130888293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35353747257786477507851057 26515310443339858130888293)
        ·
          refine ⟨4971620708126223399541555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26515310443339858130888293 4971620708126223399541555)
          ·
            refine ⟨7457431062189335099312333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971620708126223399541555 7457431062189335099312333)
            ·
              refine ⟨2796536648321000662242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7457431062189335099312333 2796536648321000662242125)
              ·
                refine ⟨1048701243120375248340797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2796536648321000662242125 1048701243120375248340797)
                ·
                  refine ⟨393262966170140718127799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048701243120375248340797 393262966170140718127799)
                  ·
                    rfl

theorem cell21_1723223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].length) (baseStart_1723223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723223 prefixEnd_1723223 := by exact prefixLift 1723223
  have htrace : WordTrace (prefixWord ++ tailWord_1723223) baseStart_1723223 baseEnd_1723223 := by
    simpa [prefixWord, tailWord_1723223, baseEnd_1723223] using wordTrace_append hprefix tailTrace_1723223
  have hstable : (prefixWord ++ tailWord_1723223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723223).length < 2 ^ (prefixWord ++ tailWord_1723223).sum := by decide
  have hdescent : baseEnd_1723223 < baseStart_1723223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723240 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_1723240 : Nat := 118140960795 + 1723240 * 2 ^ 59
def prefixEnd_1723240 : Nat := 4983230072969 + 3 ^ 40 * 1723240 * 2
def baseEnd_1723240 : Nat := 393266845801752466344431

theorem tailTrace_1723240 : CollatzResearch.WordTrace tailWord_1723240 prefixEnd_1723240 393266845801752466344431 := by
  unfold tailWord_1723240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425863138501630403107587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41901150851335507204143449 31425863138501630403107587)
  ·
    refine ⟨47138794707752445604661381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425863138501630403107587 47138794707752445604661381)
    ·
      refine ⟨8838524007703583550874009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47138794707752445604661381 8838524007703583550874009)
      ·
        refine ⟨6628893005777687663155507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838524007703583550874009 6628893005777687663155507)
        ·
          refine ⟨9943339508666531494733261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628893005777687663155507 9943339508666531494733261)
          ·
            refine ⟨3728752315749949310524973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9943339508666531494733261 3728752315749949310524973)
            ·
              refine ⟨1398282118406230991446865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3728752315749949310524973 1398282118406230991446865)
              ·
                refine ⟨1048711588804673243585149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398282118406230991446865 1048711588804673243585149)
                ·
                  refine ⟨393266845801752466344431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048711588804673243585149 393266845801752466344431)
                  ·
                    rfl

theorem cell21_1723240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_1723240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723240 prefixEnd_1723240 := by exact prefixLift 1723240
  have htrace : WordTrace (prefixWord ++ tailWord_1723240) baseStart_1723240 baseEnd_1723240 := by
    simpa [prefixWord, tailWord_1723240, baseEnd_1723240] using wordTrace_append hprefix tailTrace_1723240
  have hstable : (prefixWord ++ tailWord_1723240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723240).length < 2 ^ (prefixWord ++ tailWord_1723240).sum := by decide
  have hdescent : baseEnd_1723240 < baseStart_1723240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723254 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1723254 : Nat := 118140960795 + 1723254 * 2 ^ 59
def prefixEnd_1723254 : Nat := 4983230072969 + 3 ^ 40 * 1723254 * 2
def baseEnd_1723254 : Nat := 393270040792491553111069

theorem tailTrace_1723254 : CollatzResearch.WordTrace tailWord_1723254 prefixEnd_1723254 393270040792491553111069 := by
  unfold tailWord_1723254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928264806184533824826551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41901491265968360798149877 3928264806184533824826551)
  ·
    refine ⟨5892397209276800737239827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928264806184533824826551 5892397209276800737239827)
    ·
      refine ⟨8838595813915201105859741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892397209276800737239827 8838595813915201105859741)
      ·
        refine ⟨3314473430218200414697403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8838595813915201105859741 3314473430218200414697403)
        ·
          refine ⟨4971710145327300622046105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314473430218200414697403 4971710145327300622046105)
          ·
            refine ⟨3728782608995475466534579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971710145327300622046105 3728782608995475466534579)
            ·
              refine ⟨5593173913493213199801869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728782608995475466534579 5593173913493213199801869)
              ·
                refine ⟨2097440217559954949925701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5593173913493213199801869 2097440217559954949925701)
                ·
                  refine ⟨393270040792491553111069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097440217559954949925701 393270040792491553111069)
                  ·
                    rfl

theorem cell21_1723254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1723254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723254 prefixEnd_1723254 := by exact prefixLift 1723254
  have htrace : WordTrace (prefixWord ++ tailWord_1723254) baseStart_1723254 baseEnd_1723254 := by
    simpa [prefixWord, tailWord_1723254, baseEnd_1723254] using wordTrace_append hprefix tailTrace_1723254
  have hstable : (prefixWord ++ tailWord_1723254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723254).length < 2 ^ (prefixWord ++ tailWord_1723254).sum := by decide
  have hdescent : baseEnd_1723254 < baseStart_1723254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723296 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1723296 : Nat := 118140960795 + 1723296 * 2 ^ 59
def prefixEnd_1723296 : Nat := 4983230072969 + 3 ^ 40 * 1723296 * 2
def baseEnd_1723296 : Nat := 393279625764708813410983

theorem tailTrace_1723296 : CollatzResearch.WordTrace tailWord_1723296 prefixEnd_1723296 393279625764708813410983 := by
  unfold tailWord_1723296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426884382400191185126871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41902512509866921580169161 31426884382400191185126871)
  ·
    refine ⟨47140326573600286777690307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31426884382400191185126871 47140326573600286777690307)
    ·
      refine ⟨70710489860400430166535461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47140326573600286777690307 70710489860400430166535461)
      ·
        refine ⟨13258216848825080656225399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70710489860400430166535461 13258216848825080656225399)
        ·
          refine ⟨19887325273237620984338099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13258216848825080656225399 19887325273237620984338099)
          ·
            refine ⟨29830987909856431476507149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19887325273237620984338099 29830987909856431476507149)
            ·
              refine ⟨11186620466196161803690181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29830987909856431476507149 11186620466196161803690181)
              ·
                refine ⟨2097491337411780338191909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11186620466196161803690181 2097491337411780338191909)
                ·
                  refine ⟨393279625764708813410983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097491337411780338191909 393279625764708813410983)
                  ·
                    rfl

theorem cell21_1723296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1723296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723296 prefixEnd_1723296 := by exact prefixLift 1723296
  have htrace : WordTrace (prefixWord ++ tailWord_1723296) baseStart_1723296 baseEnd_1723296 := by
    simpa [prefixWord, tailWord_1723296, baseEnd_1723296] using wordTrace_append hprefix tailTrace_1723296
  have hstable : (prefixWord ++ tailWord_1723296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723296).length < 2 ^ (prefixWord ++ tailWord_1723296).sum := by decide
  have hdescent : baseEnd_1723296 < baseStart_1723296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723299 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 3]
def baseStart_1723299 : Nat := 118140960795 + 1723299 * 2 ^ 59
def prefixEnd_1723299 : Nat := 4983230072969 + 3 ^ 40 * 1723299 * 2
def baseEnd_1723299 : Nat := 393280310405581474860977

theorem tailTrace_1723299 : CollatzResearch.WordTrace tailWord_1723299 prefixEnd_1723299 393280310405581474860977 := by
  unfold tailWord_1723299
  simp only [CollatzResearch.WordTrace]
  refine ⟨62853878183789513882612951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41902585455859675921741967 62853878183789513882612951)
  ·
    refine ⟨94280817275684270823919427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62853878183789513882612951 94280817275684270823919427)
    ·
      refine ⟨141421225913526406235879141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94280817275684270823919427 141421225913526406235879141)
      ·
        refine ⟨26516479858786201169227339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141421225913526406235879141 26516479858786201169227339)
        ·
          refine ⟨39774719788179301753841009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26516479858786201169227339 39774719788179301753841009)
          ·
            refine ⟨29831039841134476315380757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39774719788179301753841009 29831039841134476315380757)
            ·
              refine ⟨1398329992553178577283473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29831039841134476315380757 1398329992553178577283473)
              ·
                refine ⟨1048747494414883932962605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398329992553178577283473 1048747494414883932962605)
                ·
                  refine ⟨393280310405581474860977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048747494414883932962605 393280310405581474860977)
                  ·
                    rfl

theorem cell21_1723299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].length) (baseStart_1723299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723299 prefixEnd_1723299 := by exact prefixLift 1723299
  have htrace : WordTrace (prefixWord ++ tailWord_1723299) baseStart_1723299 baseEnd_1723299 := by
    simpa [prefixWord, tailWord_1723299, baseEnd_1723299] using wordTrace_append hprefix tailTrace_1723299
  have hstable : (prefixWord ++ tailWord_1723299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723299).length < 2 ^ (prefixWord ++ tailWord_1723299).sum := by decide
  have hdescent : baseEnd_1723299 < baseStart_1723299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723378 : List Nat := [3, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1723378 : Nat := 118140960795 + 1723378 * 2 ^ 59
def prefixEnd_1723378 : Nat := 4983230072969 + 3 ^ 40 * 1723378 * 2
def baseEnd_1723378 : Nat := 131099446427298297681383

theorem tailTrace_1723378 : CollatzResearch.WordTrace tailWord_1723378 prefixEnd_1723378 131099446427298297681383 := by
  unfold tailWord_1723378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15714189887625827593684697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41904506367002206916492525 15714189887625827593684697)
  ·
    refine ⟨11785642415719370695263523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15714189887625827593684697 11785642415719370695263523)
    ·
      refine ⟨17678463623579056042895285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11785642415719370695263523 17678463623579056042895285)
      ·
        refine ⟨1657355964710536504021433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17678463623579056042895285 1657355964710536504021433)
        ·
          refine ⟨1243016973532902378016075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657355964710536504021433 1243016973532902378016075)
          ·
            refine ⟨1864525460299353567024113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243016973532902378016075 1864525460299353567024113)
            ·
              refine ⟨1398394095224515175268085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864525460299353567024113 1398394095224515175268085)
              ·
                refine ⟨131099446427298297681383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398394095224515175268085 131099446427298297681383)
                ·
                  rfl

theorem cell21_1723378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1723378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723378 prefixEnd_1723378 := by exact prefixLift 1723378
  have htrace : WordTrace (prefixWord ++ tailWord_1723378) baseStart_1723378 baseEnd_1723378 := by
    simpa [prefixWord, tailWord_1723378, baseEnd_1723378] using wordTrace_append hprefix tailTrace_1723378
  have hstable : (prefixWord ++ tailWord_1723378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723378).length < 2 ^ (prefixWord ++ tailWord_1723378).sum := by decide
  have hdescent : baseEnd_1723378 < baseStart_1723378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723417 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_1723417 : Nat := 118140960795 + 1723417 * 2 ^ 59
def prefixEnd_1723417 : Nat := 4983230072969 + 3 ^ 40 * 1723417 * 2
def baseEnd_1723417 : Nat := 393307239613239491894069

theorem tailTrace_1723417 : CollatzResearch.WordTrace tailWord_1723417 prefixEnd_1723417 393307239613239491894069 := by
  unfold tailWord_1723417
  simp only [CollatzResearch.WordTrace]
  refine ⟨62858181997362020035408505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41905454664908013356939003 62858181997362020035408505)
  ·
    refine ⟨47143636498021515026556379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62858181997362020035408505 47143636498021515026556379)
    ·
      refine ⟨70715454747032272539834569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47143636498021515026556379 70715454747032272539834569)
      ·
        refine ⟨53036591060274204404875927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70715454747032272539834569 53036591060274204404875927)
        ·
          refine ⟨79554886590411306607313891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53036591060274204404875927 79554886590411306607313891)
          ·
            refine ⟨119332329885616959910970837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79554886590411306607313891 119332329885616959910970837)
            ·
              refine ⟨2796851481694147497913379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119332329885616959910970837 2796851481694147497913379)
              ·
                refine ⟨4195277222541221246870069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796851481694147497913379 4195277222541221246870069)
                ·
                  refine ⟨393307239613239491894069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4195277222541221246870069 393307239613239491894069)
                  ·
                    rfl

theorem cell21_1723417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_1723417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723417 prefixEnd_1723417 := by exact prefixLift 1723417
  have htrace : WordTrace (prefixWord ++ tailWord_1723417) baseStart_1723417 baseEnd_1723417 := by
    simpa [prefixWord, tailWord_1723417, baseEnd_1723417] using wordTrace_append hprefix tailTrace_1723417
  have hstable : (prefixWord ++ tailWord_1723417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723417).length < 2 ^ (prefixWord ++ tailWord_1723417).sum := by decide
  have hdescent : baseEnd_1723417 < baseStart_1723417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723493 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1723493 : Nat := 118140960795 + 1723493 * 2 ^ 59
def prefixEnd_1723493 : Nat := 4983230072969 + 3 ^ 40 * 1723493 * 2
def baseEnd_1723493 : Nat := 393324583848680248627247

theorem tailTrace_1723493 : CollatzResearch.WordTrace tailWord_1723493 prefixEnd_1723493 393324583848680248627247 := by
  unfold tailWord_1723493
  simp only [CollatzResearch.WordTrace]
  refine ⟨62860953945086685015175133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41907302630057790010116755 62860953945086685015175133)
  ·
    refine ⟨23572857729407506880690675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62860953945086685015175133 23572857729407506880690675)
    ·
      refine ⟨35359286594111260321036013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23572857729407506880690675 35359286594111260321036013)
      ·
        refine ⟨13259732472791722620388505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35359286594111260321036013 13259732472791722620388505)
        ·
          refine ⟨9944799354593791965291379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13259732472791722620388505 9944799354593791965291379)
          ·
            refine ⟨14917199031890687947937069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944799354593791965291379 14917199031890687947937069)
            ·
              refine ⟨5593949636959007980476401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14917199031890687947937069 5593949636959007980476401)
              ·
                refine ⟨4195462227719255985357301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593949636959007980476401 4195462227719255985357301)
                ·
                  refine ⟨393324583848680248627247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4195462227719255985357301 393324583848680248627247)
                  ·
                    rfl

theorem cell21_1723493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1723493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723493 prefixEnd_1723493 := by exact prefixLift 1723493
  have htrace : WordTrace (prefixWord ++ tailWord_1723493) baseStart_1723493 baseEnd_1723493 := by
    simpa [prefixWord, tailWord_1723493, baseEnd_1723493] using wordTrace_append hprefix tailTrace_1723493
  have hstable : (prefixWord ++ tailWord_1723493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723493).length < 2 ^ (prefixWord ++ tailWord_1723493).sum := by decide
  have hdescent : baseEnd_1723493 < baseStart_1723493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723524 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1723524 : Nat := 118140960795 + 1723524 * 2 ^ 59
def prefixEnd_1723524 : Nat := 4983230072969 + 3 ^ 40 * 1723524 * 2
def baseEnd_1723524 : Nat := 393331658471031083610517

theorem tailTrace_1723524 : CollatzResearch.WordTrace tailWord_1723524 prefixEnd_1723524 393331658471031083610517 := by
  unfold tailWord_1723524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31431042303987188654776813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41908056405316251539702417 31431042303987188654776813)
  ·
    refine ⟨11786640863995195745541305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31431042303987188654776813 11786640863995195745541305)
    ·
      refine ⟨8839980647996396809155979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786640863995195745541305 8839980647996396809155979)
      ·
        refine ⟨13259970971994595213733969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839980647996396809155979 13259970971994595213733969)
        ·
          refine ⟨9944978228995946410300477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13259970971994595213733969 9944978228995946410300477)
          ·
            refine ⟨3729366835873479903862679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9944978228995946410300477 3729366835873479903862679)
            ·
              refine ⟨5594050253810219855794019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729366835873479903862679 5594050253810219855794019)
              ·
                refine ⟨8391075380715329783691029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594050253810219855794019 8391075380715329783691029)
                ·
                  refine ⟨393331658471031083610517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8391075380715329783691029 393331658471031083610517)
                  ·
                    rfl

theorem cell21_1723524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1723524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723524 prefixEnd_1723524 := by exact prefixLift 1723524
  have htrace : WordTrace (prefixWord ++ tailWord_1723524) baseStart_1723524 baseEnd_1723524 := by
    simpa [prefixWord, tailWord_1723524, baseEnd_1723524] using wordTrace_append hprefix tailTrace_1723524
  have hstable : (prefixWord ++ tailWord_1723524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723524).length < 2 ^ (prefixWord ++ tailWord_1723524).sum := by decide
  have hdescent : baseEnd_1723524 < baseStart_1723524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723583 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_1723583 : Nat := 118140960795 + 1723583 * 2 ^ 59
def prefixEnd_1723583 : Nat := 4983230072969 + 3 ^ 40 * 1723583 * 2
def baseEnd_1723583 : Nat := 393345123074860092127063

theorem tailTrace_1723583 : CollatzResearch.WordTrace tailWord_1723583 prefixEnd_1723583 393345123074860092127063 := by
  unfold tailWord_1723583
  simp only [CollatzResearch.WordTrace]
  refine ⟨62864236514760630385951403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41909491009840420257300935 62864236514760630385951403)
  ·
    refine ⟨94296354772140945578927105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62864236514760630385951403 94296354772140945578927105)
    ·
      refine ⟨70722266079105709184195329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94296354772140945578927105 70722266079105709184195329)
      ·
        refine ⟨53041699559329281888146497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70722266079105709184195329 53041699559329281888146497)
        ·
          refine ⟨39781274669496961416109873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53041699559329281888146497 39781274669496961416109873)
          ·
            refine ⟨29835956002122721062082405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39781274669496961416109873 29835956002122721062082405)
            ·
              refine ⟨5594241750398010199140451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29835956002122721062082405 5594241750398010199140451)
              ·
                refine ⟨8391362625597015298710677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594241750398010199140451 8391362625597015298710677)
                ·
                  refine ⟨393345123074860092127063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8391362625597015298710677 393345123074860092127063)
                  ·
                    rfl

theorem cell21_1723583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_1723583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723583 prefixEnd_1723583 := by exact prefixLift 1723583
  have htrace : WordTrace (prefixWord ++ tailWord_1723583) baseStart_1723583 baseEnd_1723583 := by
    simpa [prefixWord, tailWord_1723583, baseEnd_1723583] using wordTrace_append hprefix tailTrace_1723583
  have hstable : (prefixWord ++ tailWord_1723583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723583).length < 2 ^ (prefixWord ++ tailWord_1723583).sum := by decide
  have hdescent : baseEnd_1723583 < baseStart_1723583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723679 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 3]
def baseStart_1723679 : Nat := 118140960795 + 1723679 * 2 ^ 59
def prefixEnd_1723679 : Nat := 4983230072969 + 3 ^ 40 * 1723679 * 2
def baseEnd_1723679 : Nat := 393367031582785258526867

theorem tailTrace_1723679 : CollatzResearch.WordTrace tailWord_1723679 prefixEnd_1723679 393367031582785258526867 := by
  unfold tailWord_1723679
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867737922412838781446091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41911825281608559187630727 62867737922412838781446091)
  ·
    refine ⟨94301606883619258172169137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62867737922412838781446091 94301606883619258172169137)
    ·
      refine ⟨70726205162714443629126853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94301606883619258172169137 70726205162714443629126853)
      ·
        refine ⟨13261163468008958180461285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70726205162714443629126853 13261163468008958180461285)
        ·
          refine ⟨2486468150251679658836491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13261163468008958180461285 2486468150251679658836491)
          ·
            refine ⟨3729702225377519488254737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486468150251679658836491 3729702225377519488254737)
            ·
              refine ⟨2797276669033139616191053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729702225377519488254737 2797276669033139616191053)
              ·
                refine ⟨1048978750887427356071645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797276669033139616191053 1048978750887427356071645)
                ·
                  refine ⟨393367031582785258526867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048978750887427356071645 393367031582785258526867)
                  ·
                    rfl

theorem cell21_1723679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].length) (baseStart_1723679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723679 prefixEnd_1723679 := by exact prefixLift 1723679
  have htrace : WordTrace (prefixWord ++ tailWord_1723679) baseStart_1723679 baseEnd_1723679 := by
    simpa [prefixWord, tailWord_1723679, baseEnd_1723679] using wordTrace_append hprefix tailTrace_1723679
  have hstable : (prefixWord ++ tailWord_1723679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723679).length < 2 ^ (prefixWord ++ tailWord_1723679).sum := by decide
  have hdescent : baseEnd_1723679 < baseStart_1723679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723693 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1723693 : Nat := 118140960795 + 1723693 * 2 ^ 59
def prefixEnd_1723693 : Nat := 4983230072969 + 3 ^ 40 * 1723693 * 2
def baseEnd_1723693 : Nat := 393370226573524345293505

theorem tailTrace_1723693 : CollatzResearch.WordTrace tailWord_1723693 prefixEnd_1723693 393370226573524345293505 := by
  unfold tailWord_1723693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62868248544362119172455733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41912165696241412781637155 62868248544362119172455733)
  ·
    refine ⟨5893898301033948672417725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62868248544362119172455733 5893898301033948672417725)
    ·
      refine ⟨2210211862887730752156647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5893898301033948672417725 2210211862887730752156647)
      ·
        refine ⟨3315317794331596128234971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210211862887730752156647 3315317794331596128234971)
        ·
          refine ⟨4972976691497394192352457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315317794331596128234971 4972976691497394192352457)
          ·
            refine ⟨3729732518623045644264343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972976691497394192352457 3729732518623045644264343)
            ·
              refine ⟨5594598777934568466396515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729732518623045644264343 5594598777934568466396515)
              ·
                refine ⟨8391898166901852699594773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594598777934568466396515 8391898166901852699594773)
                ·
                  refine ⟨393370226573524345293505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8391898166901852699594773 393370226573524345293505)
                  ·
                    rfl

theorem cell21_1723693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1723693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723693 prefixEnd_1723693 := by exact prefixLift 1723693
  have htrace : WordTrace (prefixWord ++ tailWord_1723693) baseStart_1723693 baseEnd_1723693 := by
    simpa [prefixWord, tailWord_1723693, baseEnd_1723693] using wordTrace_append hprefix tailTrace_1723693
  have hstable : (prefixWord ++ tailWord_1723693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723693).length < 2 ^ (prefixWord ++ tailWord_1723693).sum := by decide
  have hdescent : baseEnd_1723693 < baseStart_1723693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723735 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_1723735 : Nat := 118140960795 + 1723735 * 2 ^ 59
def prefixEnd_1723735 : Nat := 4983230072969 + 3 ^ 40 * 1723735 * 2
def baseEnd_1723735 : Nat := 393379811545741605593419

theorem tailTrace_1723735 : CollatzResearch.WordTrace tailWord_1723735 prefixEnd_1723735 393379811545741605593419 := by
  unfold tailWord_1723735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62869780410209960345484659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41913186940139973563656439 62869780410209960345484659)
  ·
    refine ⟨94304670615314940518226989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62869780410209960345484659 94304670615314940518226989)
    ·
      refine ⟨35364251480743102694335121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94304670615314940518226989 35364251480743102694335121)
      ·
        refine ⟨26523188610557327020751341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35364251480743102694335121 26523188610557327020751341)
        ·
          refine ⟨9946195728958997632781753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26523188610557327020751341 9946195728958997632781753)
          ·
            refine ⟨7459646796719248224586315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9946195728958997632781753 7459646796719248224586315)
            ·
              refine ⟨11189470195078872336879473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459646796719248224586315 11189470195078872336879473)
              ·
                refine ⟨8392102646309154252659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11189470195078872336879473 8392102646309154252659605)
                ·
                  refine ⟨393379811545741605593419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8392102646309154252659605 393379811545741605593419)
                  ·
                    rfl

theorem cell21_1723735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_1723735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723735 prefixEnd_1723735 := by exact prefixLift 1723735
  have htrace : WordTrace (prefixWord ++ tailWord_1723735) baseStart_1723735 baseEnd_1723735 := by
    simpa [prefixWord, tailWord_1723735, baseEnd_1723735] using wordTrace_append hprefix tailTrace_1723735
  have hstable : (prefixWord ++ tailWord_1723735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723735).length < 2 ^ (prefixWord ++ tailWord_1723735).sum := by decide
  have hdescent : baseEnd_1723735 < baseStart_1723735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723738 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1723738 : Nat := 118140960795 + 1723738 * 2 ^ 59
def prefixEnd_1723738 : Nat := 4983230072969 + 3 ^ 40 * 1723738 * 2
def baseEnd_1723738 : Nat := 393380496186614267043413

theorem tailTrace_1723738 : CollatzResearch.WordTrace tailWord_1723738 prefixEnd_1723738 393380496186614267043413 := by
  unfold tailWord_1723738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717472457299772964460967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41913259886132727905229245 15717472457299772964460967)
  ·
    refine ⟨23576208685949659446691451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15717472457299772964460967 23576208685949659446691451)
    ·
      refine ⟨35364313028924489170037177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23576208685949659446691451 35364313028924489170037177)
      ·
        refine ⟨26523234771693366877527883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35364313028924489170037177 26523234771693366877527883)
        ·
          refine ⟨39784852157540050316291825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26523234771693366877527883 39784852157540050316291825)
          ·
            refine ⟨29838639118155037737218869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39784852157540050316291825 29838639118155037737218869)
            ·
              refine ⟨2797372417327034787864269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29838639118155037737218869 2797372417327034787864269)
              ·
                refine ⟨1049014656497638045449101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797372417327034787864269 1049014656497638045449101)
                ·
                  refine ⟨393380496186614267043413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049014656497638045449101 393380496186614267043413)
                  ·
                    rfl

theorem cell21_1723738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1723738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723738 prefixEnd_1723738 := by exact prefixLift 1723738
  have htrace : WordTrace (prefixWord ++ tailWord_1723738) baseStart_1723738 baseEnd_1723738 := by
    simpa [prefixWord, tailWord_1723738, baseEnd_1723738] using wordTrace_append hprefix tailTrace_1723738
  have hstable : (prefixWord ++ tailWord_1723738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723738).length < 2 ^ (prefixWord ++ tailWord_1723738).sum := by decide
  have hdescent : baseEnd_1723738 < baseStart_1723738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723741 : List Nat := [1, 4, 5, 1, 1, 2, 7]
def baseStart_1723741 : Nat := 118140960795 + 1723741 * 2 ^ 59
def prefixEnd_1723741 : Nat := 4983230072969 + 3 ^ 40 * 1723741 * 2
def baseEnd_1723741 : Nat := 43709020091942992054823

theorem tailTrace_1723741 : CollatzResearch.WordTrace tailWord_1723741 prefixEnd_1723741 43709020091942992054823 := by
  unfold tailWord_1723741
  simp only [CollatzResearch.WordTrace]
  refine ⟨62869999248188223370203077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41913332832125482246802051 62869999248188223370203077)
  ·
    refine ⟨11788124859035291881913077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62869999248188223370203077 11788124859035291881913077)
    ·
      refine ⟨1105136705534558613929351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11788124859035291881913077 1105136705534558613929351)
      ·
        refine ⟨1657705058301837920894027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105136705534558613929351 1657705058301837920894027)
        ·
          refine ⟨2486557587452756881341041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657705058301837920894027 2486557587452756881341041)
          ·
            refine ⟨1864918190589567661005781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486557587452756881341041 1864918190589567661005781)
            ·
              refine ⟨43709020091942992054823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1864918190589567661005781 43709020091942992054823)
              ·
                rfl

theorem cell21_1723741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 7].length) (baseStart_1723741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723741 prefixEnd_1723741 := by exact prefixLift 1723741
  have htrace : WordTrace (prefixWord ++ tailWord_1723741) baseStart_1723741 baseEnd_1723741 := by
    simpa [prefixWord, tailWord_1723741, baseEnd_1723741] using wordTrace_append hprefix tailTrace_1723741
  have hstable : (prefixWord ++ tailWord_1723741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723741).length < 2 ^ (prefixWord ++ tailWord_1723741).sum := by decide
  have hdescent : baseEnd_1723741 < baseStart_1723741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723806 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1723806 : Nat := 118140960795 + 1723806 * 2 ^ 59
def prefixEnd_1723806 : Nat := 4983230072969 + 3 ^ 40 * 1723806 * 2
def baseEnd_1723806 : Nat := 393396014713061259909941

theorem tailTrace_1723806 : CollatzResearch.WordTrace tailWord_1723806 prefixEnd_1723806 393396014713061259909941 := by
  unfold tailWord_1723806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859046249119092433914909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41914913328635159647546181 7859046249119092433914909)
  ·
    refine ⟨2947142343419659662718091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7859046249119092433914909 2947142343419659662718091)
    ·
      refine ⟨4420713515129489494077137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947142343419659662718091 4420713515129489494077137)
      ·
        refine ⟨3315535136347117120557853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420713515129489494077137 3315535136347117120557853)
        ·
          refine ⟨1243325676130168920209195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315535136347117120557853 1243325676130168920209195)
          ·
            refine ⟨1864988514195253380313793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243325676130168920209195 1864988514195253380313793)
            ·
              refine ⟨1398741385646440035235345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864988514195253380313793 1398741385646440035235345)
              ·
                refine ⟨1049056039234830026426509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398741385646440035235345 1049056039234830026426509)
                ·
                  refine ⟨393396014713061259909941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049056039234830026426509 393396014713061259909941)
                  ·
                    rfl

theorem cell21_1723806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1723806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723806 prefixEnd_1723806 := by exact prefixLift 1723806
  have htrace : WordTrace (prefixWord ++ tailWord_1723806) baseStart_1723806 baseEnd_1723806 := by
    simpa [prefixWord, tailWord_1723806, baseEnd_1723806] using wordTrace_append hprefix tailTrace_1723806
  have hstable : (prefixWord ++ tailWord_1723806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723806).length < 2 ^ (prefixWord ++ tailWord_1723806).sum := by decide
  have hdescent : baseEnd_1723806 < baseStart_1723806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723862 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1723862 : Nat := 118140960795 + 1723862 * 2 ^ 59
def prefixEnd_1723862 : Nat := 4983230072969 + 3 ^ 40 * 1723862 * 2
def baseEnd_1723862 : Nat := 393408794676017606976493

theorem tailTrace_1723862 : CollatzResearch.WordTrace tailWord_1723862 prefixEnd_1723862 393408794676017606976493 := by
  unfold tailWord_1723862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929650780046866314709865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41916274987166574023571893 3929650780046866314709865)
  ·
    refine ⟨2947238085035149736032399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3929650780046866314709865 2947238085035149736032399)
    ·
      refine ⟨4420857127552724604048599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947238085035149736032399 4420857127552724604048599)
      ·
        refine ⟨6631285691329086906072899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420857127552724604048599 6631285691329086906072899)
        ·
          refine ⟨9946928536993630359109349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631285691329086906072899 9946928536993630359109349)
          ·
            refine ⟨1865049100686305692333003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9946928536993630359109349 1865049100686305692333003)
            ·
              refine ⟨2797573651029458538499505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865049100686305692333003 2797573651029458538499505)
              ·
                refine ⟨2098180238272093903874629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797573651029458538499505 2098180238272093903874629)
                ·
                  refine ⟨393408794676017606976493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098180238272093903874629 393408794676017606976493)
                  ·
                    rfl

theorem cell21_1723862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1723862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723862 prefixEnd_1723862 := by exact prefixLift 1723862
  have htrace : WordTrace (prefixWord ++ tailWord_1723862) baseStart_1723862 baseEnd_1723862 := by
    simpa [prefixWord, tailWord_1723862, baseEnd_1723862] using wordTrace_append hprefix tailTrace_1723862
  have hstable : (prefixWord ++ tailWord_1723862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723862).length < 2 ^ (prefixWord ++ tailWord_1723862).sum := by decide
  have hdescent : baseEnd_1723862 < baseStart_1723862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723873 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_1723873 : Nat := 118140960795 + 1723873 * 2 ^ 59
def prefixEnd_1723873 : Nat := 4983230072969 + 3 ^ 40 * 1723873 * 2
def baseEnd_1723873 : Nat := 393411305025884032293137

theorem tailTrace_1723873 : CollatzResearch.WordTrace tailWord_1723873 prefixEnd_1723873 393411305025884032293137 := by
  unfold tailWord_1723873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62874813683710009914008273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41916542455806673276005515 62874813683710009914008273)
  ·
    refine ⟨47156110262782507435506205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62874813683710009914008273 47156110262782507435506205)
    ·
      refine ⟨17683541348543440288314827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47156110262782507435506205 17683541348543440288314827)
      ·
        refine ⟨26525312022815160432472241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17683541348543440288314827 26525312022815160432472241)
        ·
          refine ⟨19893984017111370324354181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26525312022815160432472241 19893984017111370324354181)
          ·
            refine ⟨3730122003208381935816409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19893984017111370324354181 3730122003208381935816409)
            ·
              refine ⟨2797591502406286451862307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730122003208381935816409 2797591502406286451862307)
              ·
                refine ⟨4196387253609429677793461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797591502406286451862307 4196387253609429677793461)
                ·
                  refine ⟨393411305025884032293137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196387253609429677793461 393411305025884032293137)
                  ·
                    rfl

theorem cell21_1723873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_1723873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723873 prefixEnd_1723873 := by exact prefixLift 1723873
  have htrace : WordTrace (prefixWord ++ tailWord_1723873) baseStart_1723873 baseEnd_1723873 := by
    simpa [prefixWord, tailWord_1723873, baseEnd_1723873] using wordTrace_append hprefix tailTrace_1723873
  have hstable : (prefixWord ++ tailWord_1723873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723873).length < 2 ^ (prefixWord ++ tailWord_1723873).sum := by decide
  have hdescent : baseEnd_1723873 < baseStart_1723873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723887 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_1723887 : Nat := 118140960795 + 1723887 * 2 ^ 59
def prefixEnd_1723887 : Nat := 4983230072969 + 3 ^ 40 * 1723887 * 2
def baseEnd_1723887 : Nat := 393414500016623119059775

theorem tailTrace_1723887 : CollatzResearch.WordTrace tailWord_1723887 prefixEnd_1723887 393414500016623119059775 := by
  unfold tailWord_1723887
  simp only [CollatzResearch.WordTrace]
  refine ⟨62875324305659290305017915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41916882870439526870011943 62875324305659290305017915)
  ·
    refine ⟨94312986458488935457526873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62875324305659290305017915 94312986458488935457526873)
    ·
      refine ⟨70734739843866701593145155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94312986458488935457526873 70734739843866701593145155)
      ·
        refine ⟨106102109765800052389717733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70734739843866701593145155 106102109765800052389717733)
        ·
          refine ⟨19894145581087509823072075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106102109765800052389717733 19894145581087509823072075)
          ·
            refine ⟨29841218371631264734608113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19894145581087509823072075 29841218371631264734608113)
            ·
              refine ⟨22380913778723448550956085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29841218371631264734608113 22380913778723448550956085)
              ·
                refine ⟨2098210666755323301652133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22380913778723448550956085 2098210666755323301652133)
                ·
                  refine ⟨393414500016623119059775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098210666755323301652133 393414500016623119059775)
                  ·
                    rfl

theorem cell21_1723887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_1723887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723887 prefixEnd_1723887 := by exact prefixLift 1723887
  have htrace : WordTrace (prefixWord ++ tailWord_1723887) baseStart_1723887 baseEnd_1723887 := by
    simpa [prefixWord, tailWord_1723887, baseEnd_1723887] using wordTrace_append hprefix tailTrace_1723887
  have hstable : (prefixWord ++ tailWord_1723887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723887).length < 2 ^ (prefixWord ++ tailWord_1723887).sum := by decide
  have hdescent : baseEnd_1723887 < baseStart_1723887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723910 : List Nat := [6, 2, 1, 1, 3, 1, 7]
def baseStart_1723910 : Nat := 118140960795 + 1723910 * 2 ^ 59
def prefixEnd_1723910 : Nat := 4983230072969 + 3 ^ 40 * 1723910 * 2
def baseEnd_1723910 : Nat := 43713305436664465575155

theorem tailTrace_1723910 : CollatzResearch.WordTrace tailWord_1723910 prefixEnd_1723910 43713305436664465575155 := by
  unfold tailWord_1723910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964880099517998913534537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41917442123050643488736789 1964880099517998913534537)
  ·
    refine ⟨1473660074638499185150903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1964880099517998913534537 1473660074638499185150903)
    ·
      refine ⟨2210490111957748777726355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473660074638499185150903 2210490111957748777726355)
      ·
        refine ⟨3315735167936623166589533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210490111957748777726355 3315735167936623166589533)
        ·
          refine ⟨1243400687976233687471075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315735167936623166589533 1243400687976233687471075)
          ·
            refine ⟨1865101031964350531206613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243400687976233687471075 1865101031964350531206613)
            ·
              refine ⟨43713305436664465575155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1865101031964350531206613 43713305436664465575155)
              ·
                rfl

theorem cell21_1723910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 7].length) (baseStart_1723910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723910 prefixEnd_1723910 := by exact prefixLift 1723910
  have htrace : WordTrace (prefixWord ++ tailWord_1723910) baseStart_1723910 baseEnd_1723910 := by
    simpa [prefixWord, tailWord_1723910, baseEnd_1723910] using wordTrace_append hprefix tailTrace_1723910
  have hstable : (prefixWord ++ tailWord_1723910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723910).length < 2 ^ (prefixWord ++ tailWord_1723910).sum := by decide
  have hdescent : baseEnd_1723910 < baseStart_1723910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723924 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1723924 : Nat := 118140960795 + 1723924 * 2 ^ 59
def prefixEnd_1723924 : Nat := 4983230072969 + 3 ^ 40 * 1723924 * 2
def baseEnd_1723924 : Nat := 393422943920719276943033

theorem tailTrace_1723924 : CollatzResearch.WordTrace tailWord_1723924 prefixEnd_1723924 393422943920719276943033 := by
  unfold tailWord_1723924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31438336903262622812057413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41917782537683497082743217 31438336903262622812057413)
  ·
    refine ⟨5894688169361741777260765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31438336903262622812057413 5894688169361741777260765)
    ·
      refine ⟨2210508063510653166472787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5894688169361741777260765 2210508063510653166472787)
      ·
        refine ⟨3315762095265979749709181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210508063510653166472787 3315762095265979749709181)
        ·
          refine ⟨1243410785724742406140943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315762095265979749709181 1243410785724742406140943)
          ·
            refine ⟨1865116178587113609211415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243410785724742406140943 1865116178587113609211415)
            ·
              refine ⟨2797674267880670413817123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865116178587113609211415 2797674267880670413817123)
              ·
                refine ⟨4196511401821005620725685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797674267880670413817123 4196511401821005620725685)
                ·
                  refine ⟨393422943920719276943033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196511401821005620725685 393422943920719276943033)
                  ·
                    rfl

theorem cell21_1723924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1723924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723924 prefixEnd_1723924 := by exact prefixLift 1723924
  have htrace : WordTrace (prefixWord ++ tailWord_1723924) baseStart_1723924 baseEnd_1723924 := by
    simpa [prefixWord, tailWord_1723924, baseEnd_1723924] using wordTrace_append hprefix tailTrace_1723924
  have hstable : (prefixWord ++ tailWord_1723924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723924).length < 2 ^ (prefixWord ++ tailWord_1723924).sum := by decide
  have hdescent : baseEnd_1723924 < baseStart_1723924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723980 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1723980 : Nat := 118140960795 + 1723980 * 2 ^ 59
def prefixEnd_1723980 : Nat := 4983230072969 + 3 ^ 40 * 1723980 * 2
def baseEnd_1723980 : Nat := 393435723883675624009585

theorem tailTrace_1723980 : CollatzResearch.WordTrace tailWord_1723980 prefixEnd_1723980 393435723883675624009585 := by
  unfold tailWord_1723980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439358147161183594076697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41919144196214911458768929 31439358147161183594076697)
  ·
    refine ⟨23579518610370887695557523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31439358147161183594076697 23579518610370887695557523)
    ·
      refine ⟨35369277915556331543336285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23579518610370887695557523 35369277915556331543336285)
      ·
        refine ⟨13263479218333624328751107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35369277915556331543336285 13263479218333624328751107)
        ·
          refine ⟨19895218827500436493126661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263479218333624328751107 19895218827500436493126661)
          ·
            refine ⟨3730353530156331842461249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19895218827500436493126661 3730353530156331842461249)
            ·
              refine ⟨2797765147617248881845937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730353530156331842461249 2797765147617248881845937)
              ·
                refine ⟨2098323860712936661384453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797765147617248881845937 2098323860712936661384453)
                ·
                  refine ⟨393435723883675624009585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098323860712936661384453 393435723883675624009585)
                  ·
                    rfl

theorem cell21_1723980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1723980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1723980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1723980 prefixEnd_1723980 := by exact prefixLift 1723980
  have htrace : WordTrace (prefixWord ++ tailWord_1723980) baseStart_1723980 baseEnd_1723980 := by
    simpa [prefixWord, tailWord_1723980, baseEnd_1723980] using wordTrace_append hprefix tailTrace_1723980
  have hstable : (prefixWord ++ tailWord_1723980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723980).length < 2 ^ (prefixWord ++ tailWord_1723980).sum := by decide
  have hdescent : baseEnd_1723980 < baseStart_1723980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724039 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_1724039 : Nat := 118140960795 + 1724039 * 2 ^ 59
def prefixEnd_1724039 : Nat := 4983230072969 + 3 ^ 40 * 1724039 * 2
def baseEnd_1724039 : Nat := 393449188487504632526131

theorem tailTrace_1724039 : CollatzResearch.WordTrace tailWord_1724039 prefixEnd_1724039 393449188487504632526131 := by
  unfold tailWord_1724039
  simp only [CollatzResearch.WordTrace]
  refine ⟨62880868201108620264551171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41920578800739080176367447 62880868201108620264551171)
  ·
    refine ⟨94321302301662930396826757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62880868201108620264551171 94321302301662930396826757)
    ·
      refine ⟨17685244181561799449405017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94321302301662930396826757 17685244181561799449405017)
      ·
        refine ⟨13263933136171349587053763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17685244181561799449405017 13263933136171349587053763)
        ·
          refine ⟨19895899704257024380580645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263933136171349587053763 19895899704257024380580645)
          ·
            refine ⟨3730481194548192071358871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19895899704257024380580645 3730481194548192071358871)
            ·
              refine ⟨5595721791822288107038307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730481194548192071358871 5595721791822288107038307)
              ·
                refine ⟨8393582687733432160557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595721791822288107038307 8393582687733432160557461)
                ·
                  refine ⟨393449188487504632526131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8393582687733432160557461 393449188487504632526131)
                  ·
                    rfl

theorem cell21_1724039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_1724039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724039 prefixEnd_1724039 := by exact prefixLift 1724039
  have htrace : WordTrace (prefixWord ++ tailWord_1724039) baseStart_1724039 baseEnd_1724039 := by
    simpa [prefixWord, tailWord_1724039, baseEnd_1724039] using wordTrace_append hprefix tailTrace_1724039
  have hstable : (prefixWord ++ tailWord_1724039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724039).length < 2 ^ (prefixWord ++ tailWord_1724039).sum := by decide
  have hdescent : baseEnd_1724039 < baseStart_1724039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724042 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_1724042 : Nat := 118140960795 + 1724042 * 2 ^ 59
def prefixEnd_1724042 : Nat := 4983230072969 + 3 ^ 40 * 1724042 * 2
def baseEnd_1724042 : Nat := 393449873128377293976125

theorem tailTrace_1724042 : CollatzResearch.WordTrace tailWord_1724042 prefixEnd_1724042 393449873128377293976125 := by
  unfold tailWord_1724042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720244405024437944227595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41920651746731834517940253 15720244405024437944227595)
  ·
    refine ⟨23580366607536656916341393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720244405024437944227595 23580366607536656916341393)
    ·
      refine ⟨17685274955652492687256045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23580366607536656916341393 17685274955652492687256045)
      ·
        refine ⟨6631978108369684757721017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17685274955652492687256045 6631978108369684757721017)
        ·
          refine ⟨4973983581277263568290763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631978108369684757721017 4973983581277263568290763)
          ·
            refine ⟨7460975371915895352436145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973983581277263568290763 7460975371915895352436145)
            ·
              refine ⟨5595731528936921514327109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460975371915895352436145 5595731528936921514327109)
              ·
                refine ⟨1049199661675672783936333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5595731528936921514327109 1049199661675672783936333)
                ·
                  refine ⟨393449873128377293976125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049199661675672783936333 393449873128377293976125)
                  ·
                    rfl

theorem cell21_1724042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_1724042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724042 prefixEnd_1724042 := by exact prefixLift 1724042
  have htrace : WordTrace (prefixWord ++ tailWord_1724042) baseStart_1724042 baseEnd_1724042 := by
    simpa [prefixWord, tailWord_1724042, baseEnd_1724042] using wordTrace_append hprefix tailTrace_1724042
  have hstable : (prefixWord ++ tailWord_1724042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724042).length < 2 ^ (prefixWord ++ tailWord_1724042).sum := by decide
  have hdescent : baseEnd_1724042 < baseStart_1724042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724194 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1724194 : Nat := 118140960795 + 1724194 * 2 ^ 59
def prefixEnd_1724194 : Nat := 4983230072969 + 3 ^ 40 * 1724194 * 2
def baseEnd_1724194 : Nat := 393484561599258807442481

theorem tailTrace_1724194 : CollatzResearch.WordTrace tailWord_1724194 prefixEnd_1724194 393484561599258807442481 := by
  unfold tailWord_1724194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721630378886770434110909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41924347677031387824295757 15721630378886770434110909)
  ·
    refine ⟨5895611392082538912791591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15721630378886770434110909 5895611392082538912791591)
    ·
      refine ⟨8843417088123808369187387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895611392082538912791591 8843417088123808369187387)
      ·
        refine ⟨13265125632185712553781081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843417088123808369187387 13265125632185712553781081)
        ·
          refine ⟨9948844224139284415335811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13265125632185712553781081 9948844224139284415335811)
          ·
            refine ⟨14923266336208926623003717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9948844224139284415335811 14923266336208926623003717)
            ·
              refine ⟨2798112438039173741813197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14923266336208926623003717 2798112438039173741813197)
              ·
                refine ⟨1049292164264690153179949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2798112438039173741813197 1049292164264690153179949)
                ·
                  refine ⟨393484561599258807442481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049292164264690153179949 393484561599258807442481)
                  ·
                    rfl

theorem cell21_1724194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1724194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724194 prefixEnd_1724194 := by exact prefixLift 1724194
  have htrace : WordTrace (prefixWord ++ tailWord_1724194) baseStart_1724194 baseEnd_1724194 := by
    simpa [prefixWord, tailWord_1724194, baseEnd_1724194] using wordTrace_append hprefix tailTrace_1724194
  have hstable : (prefixWord ++ tailWord_1724194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724194).length < 2 ^ (prefixWord ++ tailWord_1724194).sum := by decide
  have hdescent : baseEnd_1724194 < baseStart_1724194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724250 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1724250 : Nat := 118140960795 + 1724250 * 2 ^ 59
def prefixEnd_1724250 : Nat := 4983230072969 + 3 ^ 40 * 1724250 * 2
def baseEnd_1724250 : Nat := 393497341562215154509033

theorem tailTrace_1724250 : CollatzResearch.WordTrace tailWord_1724250 prefixEnd_1724250 393497341562215154509033 := by
  unfold tailWord_1724250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722141000836050825120551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41925709335562802200321469 15722141000836050825120551)
  ·
    refine ⟨23583211501254076237680827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722141000836050825120551 23583211501254076237680827)
    ·
      refine ⟨35374817251881114356521241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23583211501254076237680827 35374817251881114356521241)
      ·
        refine ⟨26531112938910835767390931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35374817251881114356521241 26531112938910835767390931)
        ·
          refine ⟨39796669408366253651086397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26531112938910835767390931 39796669408366253651086397)
          ·
            refine ⟨14923751028137345119157399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39796669408366253651086397 14923751028137345119157399)
            ·
              refine ⟨22385626542206017678736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14923751028137345119157399 22385626542206017678736099)
              ·
                refine ⟨33578439813309026518104149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22385626542206017678736099 33578439813309026518104149)
                ·
                  refine ⟨393497341562215154509033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33578439813309026518104149 393497341562215154509033)
                  ·
                    rfl

theorem cell21_1724250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1724250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724250 prefixEnd_1724250 := by exact prefixLift 1724250
  have htrace : WordTrace (prefixWord ++ tailWord_1724250) baseStart_1724250 baseEnd_1724250 := by
    simpa [prefixWord, tailWord_1724250, baseEnd_1724250] using wordTrace_append hprefix tailTrace_1724250
  have hstable : (prefixWord ++ tailWord_1724250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724250).length < 2 ^ (prefixWord ++ tailWord_1724250).sum := by decide
  have hdescent : baseEnd_1724250 < baseStart_1724250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724270 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1724270 : Nat := 118140960795 + 1724270 * 2 ^ 59
def prefixEnd_1724270 : Nat := 4983230072969 + 3 ^ 40 * 1724270 * 2
def baseEnd_1724270 : Nat := 393501905834699564175659

theorem tailTrace_1724270 : CollatzResearch.WordTrace tailWord_1724270 prefixEnd_1724270 393501905834699564175659 := by
  unfold tailWord_1724270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861161682908968339526283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41926195642181164477473509 7861161682908968339526283)
  ·
    refine ⟨11791742524363452509289425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7861161682908968339526283 11791742524363452509289425)
    ·
      refine ⟨8843806893272589381967069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11791742524363452509289425 8843806893272589381967069)
      ·
        refine ⟨3316427584977221018237651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8843806893272589381967069 3316427584977221018237651)
        ·
          refine ⟨4974641377465831527356477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316427584977221018237651 4974641377465831527356477)
          ·
            refine ⟨1865490516549686822758679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4974641377465831527356477 1865490516549686822758679)
            ·
              refine ⟨2798235774824530234138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865490516549686822758679 2798235774824530234138019)
              ·
                refine ⟨4197353662236795351207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798235774824530234138019 4197353662236795351207029)
                ·
                  refine ⟨393501905834699564175659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197353662236795351207029 393501905834699564175659)
                  ·
                    rfl

theorem cell21_1724270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1724270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724270 prefixEnd_1724270 := by exact prefixLift 1724270
  have htrace : WordTrace (prefixWord ++ tailWord_1724270) baseStart_1724270 baseEnd_1724270 := by
    simpa [prefixWord, tailWord_1724270, baseEnd_1724270] using wordTrace_append hprefix tailTrace_1724270
  have hstable : (prefixWord ++ tailWord_1724270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724270).length < 2 ^ (prefixWord ++ tailWord_1724270).sum := by decide
  have hdescent : baseEnd_1724270 < baseStart_1724270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724281 : List Nat := [1, 2, 1, 3, 2, 2, 4, 6]
def baseStart_1724281 : Nat := 118140960795 + 1724281 * 2 ^ 59
def prefixEnd_1724281 : Nat := 4983230072969 + 3 ^ 40 * 1724281 * 2
def baseEnd_1724281 : Nat := 131168138728188663164101

theorem tailTrace_1724281 : CollatzResearch.WordTrace tailWord_1724281 prefixEnd_1724281 131168138728188663164101 := by
  unfold tailWord_1724281
  simp only [CollatzResearch.WordTrace]
  refine ⟨62889694666231895594860697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41926463110821263729907131 62889694666231895594860697)
  ·
    refine ⟨47167270999673921696145523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62889694666231895594860697 47167270999673921696145523)
    ·
      refine ⟨70750906499510882544218285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47167270999673921696145523 70750906499510882544218285)
      ·
        refine ⟨26531589937316580954081857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70750906499510882544218285 26531589937316580954081857)
        ·
          refine ⟨19898692452987435715561393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26531589937316580954081857 19898692452987435715561393)
          ·
            refine ⟨14924019339740576786671045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19898692452987435715561393 14924019339740576786671045)
            ·
              refine ⟨2798253626201358147500821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14924019339740576786671045 2798253626201358147500821)
              ·
                refine ⟨131168138728188663164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2798253626201358147500821 131168138728188663164101)
                ·
                  rfl

theorem cell21_1724281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_1724281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724281 prefixEnd_1724281 := by exact prefixLift 1724281
  have htrace : WordTrace (prefixWord ++ tailWord_1724281) baseStart_1724281 baseEnd_1724281 := by
    simpa [prefixWord, tailWord_1724281, baseEnd_1724281] using wordTrace_append hprefix tailTrace_1724281
  have hstable : (prefixWord ++ tailWord_1724281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724281).length < 2 ^ (prefixWord ++ tailWord_1724281).sum := by decide
  have hdescent : baseEnd_1724281 < baseStart_1724281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724318 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1724318 : Nat := 118140960795 + 1724318 * 2 ^ 59
def prefixEnd_1724318 : Nat := 4983230072969 + 3 ^ 40 * 1724318 * 2
def baseEnd_1724318 : Nat := 393512860088662147375561

theorem tailTrace_1724318 : CollatzResearch.WordTrace tailWord_1724318 prefixEnd_1724318 393512860088662147375561 := by
  unfold tailWord_1724318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861380520887231364244701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41927362778065233942638405 7861380520887231364244701)
  ·
    refine ⟨2948017695332711761591763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7861380520887231364244701 2948017695332711761591763)
    ·
      refine ⟨4422026542999067642387645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948017695332711761591763 4422026542999067642387645)
      ·
        refine ⟨1658259953624650365895367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4422026542999067642387645 1658259953624650365895367)
        ·
          refine ⟨2487389930436975548843051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658259953624650365895367 2487389930436975548843051)
          ·
            refine ⟨3731084895655463323264577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487389930436975548843051 3731084895655463323264577)
            ·
              refine ⟨2798313671741597492448433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731084895655463323264577 2798313671741597492448433)
              ·
                refine ⟨2098735253806198119336325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798313671741597492448433 2098735253806198119336325)
                ·
                  refine ⟨393512860088662147375561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098735253806198119336325 393512860088662147375561)
                  ·
                    rfl

theorem cell21_1724318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1724318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724318 prefixEnd_1724318 := by exact prefixLift 1724318
  have htrace : WordTrace (prefixWord ++ tailWord_1724318) baseStart_1724318 baseEnd_1724318 := by
    simpa [prefixWord, tailWord_1724318, baseEnd_1724318] using wordTrace_append hprefix tailTrace_1724318
  have hstable : (prefixWord ++ tailWord_1724318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724318).length < 2 ^ (prefixWord ++ tailWord_1724318).sum := by decide
  have hdescent : baseEnd_1724318 < baseStart_1724318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724377 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 4]
def baseStart_1724377 : Nat := 118140960795 + 1724377 * 2 ^ 59
def prefixEnd_1724377 : Nat := 4983230072969 + 3 ^ 40 * 1724377 * 2
def baseEnd_1724377 : Nat := 393526324692491155892107

theorem tailTrace_1724377 : CollatzResearch.WordTrace tailWord_1724377 prefixEnd_1724377 393526324692491155892107 := by
  unfold tailWord_1724377
  simp only [CollatzResearch.WordTrace]
  refine ⟨62893196073884103990355385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41928797382589402660236923 62893196073884103990355385)
  ·
    refine ⟨47169897055413077992766539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62893196073884103990355385 47169897055413077992766539)
    ·
      refine ⟨70754845583119616989149809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47169897055413077992766539 70754845583119616989149809)
      ·
        refine ⟨53066134187339712741862357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70754845583119616989149809 53066134187339712741862357)
        ·
          refine ⟨1243737520015774517387399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53066134187339712741862357 1243737520015774517387399)
          ·
            refine ⟨1865606280023661776081099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243737520015774517387399 1865606280023661776081099)
            ·
              refine ⟨2798409420035492664121649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865606280023661776081099 2798409420035492664121649)
              ·
                refine ⟨2098807065026619498091237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798409420035492664121649 2098807065026619498091237)
                ·
                  refine ⟨393526324692491155892107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098807065026619498091237 393526324692491155892107)
                  ·
                    rfl

theorem cell21_1724377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_1724377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724377 prefixEnd_1724377 := by exact prefixLift 1724377
  have htrace : WordTrace (prefixWord ++ tailWord_1724377) baseStart_1724377 baseEnd_1724377 := by
    simpa [prefixWord, tailWord_1724377, baseEnd_1724377] using wordTrace_append hprefix tailTrace_1724377
  have hstable : (prefixWord ++ tailWord_1724377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724377).length < 2 ^ (prefixWord ++ tailWord_1724377).sum := by decide
  have hdescent : baseEnd_1724377 < baseStart_1724377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724388 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1724388 : Nat := 118140960795 + 1724388 * 2 ^ 59
def prefixEnd_1724388 : Nat := 4983230072969 + 3 ^ 40 * 1724388 * 2
def baseEnd_1724388 : Nat := 393528835042357581208751

theorem tailTrace_1724388 : CollatzResearch.WordTrace tailWord_1724388 prefixEnd_1724388 393528835042357581208751 := by
  unfold tailWord_1724388
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446798638422126434502909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41929064851229501912670545 31446798638422126434502909)
  ·
    refine ⟨11792549489408297412938591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31446798638422126434502909 11792549489408297412938591)
    ·
      refine ⟨17688824234112446119407887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11792549489408297412938591 17688824234112446119407887)
      ·
        refine ⟨26533236351168669179111831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17688824234112446119407887 26533236351168669179111831)
        ·
          refine ⟨39799854526753003768667747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26533236351168669179111831 39799854526753003768667747)
          ·
            refine ⟨59699781790129505653001621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39799854526753003768667747 59699781790129505653001621)
            ·
              refine ⟨2798427271412320577484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59699781790129505653001621 2798427271412320577484451)
              ·
                refine ⟨4197640907118480866226677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798427271412320577484451 4197640907118480866226677)
                ·
                  refine ⟨393528835042357581208751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197640907118480866226677 393528835042357581208751)
                  ·
                    rfl

theorem cell21_1724388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1724388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724388 prefixEnd_1724388 := by exact prefixLift 1724388
  have htrace : WordTrace (prefixWord ++ tailWord_1724388) baseStart_1724388 baseEnd_1724388 := by
    simpa [prefixWord, tailWord_1724388, baseEnd_1724388] using wordTrace_append hprefix tailTrace_1724388
  have hstable : (prefixWord ++ tailWord_1724388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724388).length < 2 ^ (prefixWord ++ tailWord_1724388).sum := by decide
  have hdescent : baseEnd_1724388 < baseStart_1724388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724439 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 3]
def baseStart_1724439 : Nat := 118140960795 + 1724439 * 2 ^ 59
def prefixEnd_1724439 : Nat := 4983230072969 + 3 ^ 40 * 1724439 * 2
def baseEnd_1724439 : Nat := 393540473937192825858647

theorem tailTrace_1724439 : CollatzResearch.WordTrace tailWord_1724439 prefixEnd_1724439 393540473937192825858647 := by
  unfold tailWord_1724439
  simp only [CollatzResearch.WordTrace]
  refine ⟨62895457399659488579112371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41930304933106325719408247 62895457399659488579112371)
  ·
    refine ⟨94343186099489232868668557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62895457399659488579112371 94343186099489232868668557)
    ·
      refine ⟨35378694787308462325750709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94343186099489232868668557 35378694787308462325750709)
      ·
        refine ⟨3316752636310168343039129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35378694787308462325750709 3316752636310168343039129)
        ·
          refine ⟨2487564477232626257279347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316752636310168343039129 2487564477232626257279347)
          ·
            refine ⟨3731346715848939385919021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487564477232626257279347 3731346715848939385919021)
            ·
              refine ⟨1399255018443352269719633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3731346715848939385919021 1399255018443352269719633)
              ·
                refine ⟨1049441263832514202289725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399255018443352269719633 1049441263832514202289725)
                ·
                  refine ⟨393540473937192825858647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049441263832514202289725 393540473937192825858647)
                  ·
                    rfl

theorem cell21_1724439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].length) (baseStart_1724439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724439 prefixEnd_1724439 := by exact prefixLift 1724439
  have htrace : WordTrace (prefixWord ++ tailWord_1724439) baseStart_1724439 baseEnd_1724439 := by
    simpa [prefixWord, tailWord_1724439, baseEnd_1724439] using wordTrace_append hprefix tailTrace_1724439
  have hstable : (prefixWord ++ tailWord_1724439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724439).length < 2 ^ (prefixWord ++ tailWord_1724439).sum := by decide
  have hdescent : baseEnd_1724439 < baseStart_1724439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724498 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1724498 : Nat := 118140960795 + 1724498 * 2 ^ 59
def prefixEnd_1724498 : Nat := 4983230072969 + 3 ^ 40 * 1724498 * 2
def baseEnd_1724498 : Nat := 393553938541021834375193

theorem tailTrace_1724498 : CollatzResearch.WordTrace tailWord_1724498 prefixEnd_1724498 393553938541021834375193 := by
  unfold tailWord_1724498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724402326611435413877537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41931739537630494437006765 15724402326611435413877537)
  ·
    refine ⟨11793301744958576560408153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15724402326611435413877537 11793301744958576560408153)
    ·
      refine ⟨8844976308718932420306115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11793301744958576560408153 8844976308718932420306115)
      ·
        refine ⟨13267464463078398630459173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844976308718932420306115 13267464463078398630459173)
        ·
          refine ⟨2487649586827199743211095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13267464463078398630459173 2487649586827199743211095)
          ·
            refine ⟨3731474380240799614816643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487649586827199743211095 3731474380240799614816643)
            ·
              refine ⟨5597211570361199422224965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731474380240799614816643 5597211570361199422224965)
              ·
                refine ⟨1049477169442724891667181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5597211570361199422224965 1049477169442724891667181)
                ·
                  refine ⟨393553938541021834375193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049477169442724891667181 393553938541021834375193)
                  ·
                    rfl

theorem cell21_1724498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1724498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724498 prefixEnd_1724498 := by exact prefixLift 1724498
  have htrace : WordTrace (prefixWord ++ tailWord_1724498) baseStart_1724498 baseEnd_1724498 := by
    simpa [prefixWord, tailWord_1724498, baseEnd_1724498] using wordTrace_append hprefix tailTrace_1724498
  have hstable : (prefixWord ++ tailWord_1724498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724498).length < 2 ^ (prefixWord ++ tailWord_1724498).sum := by decide
  have hdescent : baseEnd_1724498 < baseStart_1724498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724526 : List Nat := [4, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1724526 : Nat := 118140960795 + 1724526 * 2 ^ 59
def prefixEnd_1724526 : Nat := 4983230072969 + 3 ^ 40 * 1724526 * 2
def baseEnd_1724526 : Nat := 131186776174166669302823

theorem tailTrace_1724526 : CollatzResearch.WordTrace tailWord_1724526 prefixEnd_1724526 131186776174166669302823 := by
  unfold tailWord_1724526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862328818793037804691179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41932420366896201625019621 7862328818793037804691179)
  ·
    refine ⟨11793493228189556707036769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7862328818793037804691179 11793493228189556707036769)
    ·
      refine ⟨8845119921142167530277577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11793493228189556707036769 8845119921142167530277577)
      ·
        refine ⟨6633839940856625647708183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8845119921142167530277577 6633839940856625647708183)
        ·
          refine ⟨9950759911284938471562275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633839940856625647708183 9950759911284938471562275)
          ·
            refine ⟨14926139866927407707343413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9950759911284938471562275 14926139866927407707343413)
            ·
              refine ⟨1399325612524444472563445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14926139866927407707343413 1399325612524444472563445)
              ·
                refine ⟨131186776174166669302823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1399325612524444472563445 131186776174166669302823)
                ·
                  rfl

theorem cell21_1724526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1724526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724526 prefixEnd_1724526 := by exact prefixLift 1724526
  have htrace : WordTrace (prefixWord ++ tailWord_1724526) baseStart_1724526 baseEnd_1724526 := by
    simpa [prefixWord, tailWord_1724526, baseEnd_1724526] using wordTrace_append hprefix tailTrace_1724526
  have hstable : (prefixWord ++ tailWord_1724526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724526).length < 2 ^ (prefixWord ++ tailWord_1724526).sum := by decide
  have hdescent : baseEnd_1724526 < baseStart_1724526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724675 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_1724675 : Nat := 118140960795 + 1724675 * 2 ^ 59
def prefixEnd_1724675 : Nat := 4983230072969 + 3 ^ 40 * 1724675 * 2
def baseEnd_1724675 : Nat := 393594332352508859924831

theorem tailTrace_1724675 : CollatzResearch.WordTrace tailWord_1724675 prefixEnd_1724675 393594332352508859924831 := by
  unfold tailWord_1724675
  simp only [CollatzResearch.WordTrace]
  refine ⟨62904065026804500884703479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41936043351203000589802319 62904065026804500884703479)
  ·
    refine ⟨94356097540206751327055219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62904065026804500884703479 94356097540206751327055219)
    ·
      refine ⟨141534146310310126990582829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94356097540206751327055219 141534146310310126990582829)
      ·
        refine ⟨53075304866366297621468561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141534146310310126990582829 53075304866366297621468561)
        ·
          refine ⟨39806478649774723216101421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53075304866366297621468561 39806478649774723216101421)
          ·
            refine ⟨14927429493665521206038033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39806478649774723216101421 14927429493665521206038033)
            ·
              refine ⟨11195572120249140904528525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14927429493665521206038033 11195572120249140904528525)
              ·
                refine ⟨4198339545093427839198197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11195572120249140904528525 4198339545093427839198197)
                ·
                  refine ⟨393594332352508859924831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198339545093427839198197 393594332352508859924831)
                  ·
                    rfl

theorem cell21_1724675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_1724675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724675 prefixEnd_1724675 := by exact prefixLift 1724675
  have htrace : WordTrace (prefixWord ++ tailWord_1724675) baseStart_1724675 baseEnd_1724675 := by
    simpa [prefixWord, tailWord_1724675, baseEnd_1724675] using wordTrace_append hprefix tailTrace_1724675
  have hstable : (prefixWord ++ tailWord_1724675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724675).length < 2 ^ (prefixWord ++ tailWord_1724675).sum := by decide
  have hdescent : baseEnd_1724675 < baseStart_1724675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724841 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1724841 : Nat := 118140960795 + 1724841 * 2 ^ 59
def prefixEnd_1724841 : Nat := 4983230072969 + 3 ^ 40 * 1724841 * 2
def baseEnd_1724841 : Nat := 393632215814129460157825

theorem tailTrace_1724841 : CollatzResearch.WordTrace tailWord_1724841 prefixEnd_1724841 393632215814129460157825 := by
  unfold tailWord_1724841
  simp only [CollatzResearch.WordTrace]
  refine ⟨62910119544203111235246377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41940079696135407490164251 62910119544203111235246377)
  ·
    refine ⟨47182589658152333426434783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62910119544203111235246377 47182589658152333426434783)
    ·
      refine ⟨70773884487228500139652175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47182589658152333426434783 70773884487228500139652175)
      ·
        refine ⟨106160826730842750209478263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70773884487228500139652175 106160826730842750209478263)
        ·
          refine ⟨159241240096264125314217395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106160826730842750209478263 159241240096264125314217395)
          ·
            refine ⟨238861860144396187971326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159241240096264125314217395 238861860144396187971326093)
            ·
              refine ⟨89573197554148570489247285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238861860144396187971326093 89573197554148570489247285)
              ·
                refine ⟨8397487270701428483366933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89573197554148570489247285 8397487270701428483366933)
                ·
                  refine ⟨393632215814129460157825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8397487270701428483366933 393632215814129460157825)
                  ·
                    rfl

theorem cell21_1724841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1724841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724841 prefixEnd_1724841 := by exact prefixLift 1724841
  have htrace : WordTrace (prefixWord ++ tailWord_1724841) baseStart_1724841 baseEnd_1724841 := by
    simpa [prefixWord, tailWord_1724841, baseEnd_1724841] using wordTrace_append hprefix tailTrace_1724841
  have hstable : (prefixWord ++ tailWord_1724841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724841).length < 2 ^ (prefixWord ++ tailWord_1724841).sum := by decide
  have hdescent : baseEnd_1724841 < baseStart_1724841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724968 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_1724968 : Nat := 118140960795 + 1724968 * 2 ^ 59
def prefixEnd_1724968 : Nat := 4983230072969 + 3 ^ 40 * 1724968 * 2
def baseEnd_1724968 : Nat := 393661198944405461540899

theorem tailTrace_1724968 : CollatzResearch.WordTrace tailWord_1724968 prefixEnd_1724968 393661198944405461540899 := by
  unfold tailWord_1724968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457375807371505962559779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41943167743162007950079705 31457375807371505962559779)
  ·
    refine ⟨47186063711057258943839669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31457375807371505962559779 47186063711057258943839669)
    ·
      refine ⟨4423693472911618025984969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47186063711057258943839669 4423693472911618025984969)
      ·
        refine ⟨3317770104683713519488727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4423693472911618025984969 3317770104683713519488727)
        ·
          refine ⟨4976655157025570279233091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317770104683713519488727 4976655157025570279233091)
          ·
            refine ⟨7464982735538355418849637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976655157025570279233091 7464982735538355418849637)
            ·
              refine ⟨1399684262913441641034307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7464982735538355418849637 1399684262913441641034307)
              ·
                refine ⟨2099526394370162461551461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399684262913441641034307 2099526394370162461551461)
                ·
                  refine ⟨393661198944405461540899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099526394370162461551461 393661198944405461540899)
                  ·
                    rfl

theorem cell21_1724968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_1724968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1724968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1724968 prefixEnd_1724968 := by exact prefixLift 1724968
  have htrace : WordTrace (prefixWord ++ tailWord_1724968) baseStart_1724968 baseEnd_1724968 := by
    simpa [prefixWord, tailWord_1724968, baseEnd_1724968] using wordTrace_append hprefix tailTrace_1724968
  have hstable : (prefixWord ++ tailWord_1724968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724968).length < 2 ^ (prefixWord ++ tailWord_1724968).sum := by decide
  have hdescent : baseEnd_1724968 < baseStart_1724968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725013 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 3]
def baseStart_1725013 : Nat := 118140960795 + 1725013 * 2 ^ 59
def prefixEnd_1725013 : Nat := 4983230072969 + 3 ^ 40 * 1725013 * 2
def baseEnd_1725013 : Nat := 393671468557495383290807

theorem tailTrace_1725013 : CollatzResearch.WordTrace tailWord_1725013 prefixEnd_1725013 393671468557495383290807 := by
  unfold tailWord_1725013
  simp only [CollatzResearch.WordTrace]
  refine ⟨62916392899579984610507693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41944261933053323073671795 62916392899579984610507693)
  ·
    refine ⟨23593647337342494228940385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62916392899579984610507693 23593647337342494228940385)
    ·
      refine ⟨17695235503006870671705289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23593647337342494228940385 17695235503006870671705289)
      ·
        refine ⟨13271426627255153003778967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17695235503006870671705289 13271426627255153003778967)
        ·
          refine ⟨19907139940882729505668451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271426627255153003778967 19907139940882729505668451)
          ·
            refine ⟨29860709911324094258502677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907139940882729505668451 29860709911324094258502677)
            ·
              refine ⟨1399720777093316918367313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29860709911324094258502677 1399720777093316918367313)
              ·
                refine ⟨1049790582819987688775485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399720777093316918367313 1049790582819987688775485)
                ·
                  refine ⟨393671468557495383290807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049790582819987688775485 393671468557495383290807)
                  ·
                    rfl

theorem cell21_1725013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_1725013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725013 prefixEnd_1725013 := by exact prefixLift 1725013
  have htrace : WordTrace (prefixWord ++ tailWord_1725013) baseStart_1725013 baseEnd_1725013 := by
    simpa [prefixWord, tailWord_1725013, baseEnd_1725013] using wordTrace_append hprefix tailTrace_1725013
  have hstable : (prefixWord ++ tailWord_1725013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725013).length < 2 ^ (prefixWord ++ tailWord_1725013).sum := by decide
  have hdescent : baseEnd_1725013 < baseStart_1725013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725024 : List Nat := [2, 1, 1, 3, 2, 1, 5, 6]
def baseStart_1725024 : Nat := 118140960795 + 1725024 * 2 ^ 59
def prefixEnd_1725024 : Nat := 4983230072969 + 3 ^ 40 * 1725024 * 2
def baseEnd_1725024 : Nat := 131224659635787269535817

theorem tailTrace_1725024 : CollatzResearch.WordTrace tailWord_1725024 prefixEnd_1725024 131224659635787269535817 := by
  unfold tailWord_1725024
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458397051270066744579063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41944529401693422326105417 31458397051270066744579063)
  ·
    refine ⟨47187595576905100116868595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31458397051270066744579063 47187595576905100116868595)
    ·
      refine ⟨70781393365357650175302893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47187595576905100116868595 70781393365357650175302893)
      ·
        refine ⟨26543022512009118815738585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70781393365357650175302893 26543022512009118815738585)
        ·
          refine ⟨19907266884006839111803939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26543022512009118815738585 19907266884006839111803939)
          ·
            refine ⟨29860900326010258667705909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907266884006839111803939 29860900326010258667705909)
            ·
              refine ⟨2799459405563461750097429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29860900326010258667705909 2799459405563461750097429)
              ·
                refine ⟨131224659635787269535817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2799459405563461750097429 131224659635787269535817)
                ·
                  rfl

theorem cell21_1725024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_1725024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725024 prefixEnd_1725024 := by exact prefixLift 1725024
  have htrace : WordTrace (prefixWord ++ tailWord_1725024) baseStart_1725024 baseEnd_1725024 := by
    simpa [prefixWord, tailWord_1725024, baseEnd_1725024] using wordTrace_append hprefix tailTrace_1725024
  have hstable : (prefixWord ++ tailWord_1725024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725024).length < 2 ^ (prefixWord ++ tailWord_1725024).sum := by decide
  have hdescent : baseEnd_1725024 < baseStart_1725024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725182 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1725182 : Nat := 118140960795 + 1725182 * 2 ^ 59
def prefixEnd_1725182 : Nat := 4983230072969 + 3 ^ 40 * 1725182 * 2
def baseEnd_1725182 : Nat := 393710036659988644973795

theorem tailTrace_1725182 : CollatzResearch.WordTrace tailWord_1725182 prefixEnd_1725182 393710036659988644973795 := by
  unfold tailWord_1725182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865319604495965809176225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41948371223978484315606533 7865319604495965809176225)
  ·
    refine ⟨5898989703371974356882169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7865319604495965809176225 5898989703371974356882169)
    ·
      refine ⟨4424242277528980767661627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5898989703371974356882169 4424242277528980767661627)
      ·
        refine ⟨6636363416293471151492441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4424242277528980767661627 6636363416293471151492441)
        ·
          refine ⟨4977272562220103363619331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6636363416293471151492441 4977272562220103363619331)
          ·
            refine ⟨7465908843330155045428997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977272562220103363619331 7465908843330155045428997)
            ·
              refine ⟨1399857908124404071017937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7465908843330155045428997 1399857908124404071017937)
              ·
                refine ⟨1049893431093303053263453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399857908124404071017937 1049893431093303053263453)
                ·
                  refine ⟨393710036659988644973795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049893431093303053263453 393710036659988644973795)
                  ·
                    rfl

theorem cell21_1725182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1725182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725182 prefixEnd_1725182 := by exact prefixLift 1725182
  have htrace : WordTrace (prefixWord ++ tailWord_1725182) baseStart_1725182 baseEnd_1725182 := by
    simpa [prefixWord, tailWord_1725182, baseEnd_1725182] using wordTrace_append hprefix tailTrace_1725182
  have hstable : (prefixWord ++ tailWord_1725182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725182).length < 2 ^ (prefixWord ++ tailWord_1725182).sum := by decide
  have hdescent : baseEnd_1725182 < baseStart_1725182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725221 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1725221 : Nat := 118140960795 + 1725221 * 2 ^ 59
def prefixEnd_1725221 : Nat := 4983230072969 + 3 ^ 40 * 1725221 * 2
def baseEnd_1725221 : Nat := 393718936991333243823715

theorem tailTrace_1725221 : CollatzResearch.WordTrace tailWord_1725221 prefixEnd_1725221 393718936991333243823715 := by
  unfold tailWord_1725221
  simp only [CollatzResearch.WordTrace]
  refine ⟨62923979282826436134079517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41949319521884290756053011 62923979282826436134079517)
  ·
    refine ⟨23596492231059913550279819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62923979282826436134079517 23596492231059913550279819)
    ·
      refine ⟨35394738346589870325419729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23596492231059913550279819 35394738346589870325419729)
      ·
        refine ⟨26546053759942402744064797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35394738346589870325419729 26546053759942402744064797)
        ·
          refine ⟨9954770159978401029024299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26546053759942402744064797 9954770159978401029024299)
          ·
            refine ⟨14932155239967601543536449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954770159978401029024299 14932155239967601543536449)
            ·
              refine ⟨11199116429975701157652337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14932155239967601543536449 11199116429975701157652337)
              ·
                refine ⟨8399337322481775868239253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11199116429975701157652337 8399337322481775868239253)
                ·
                  refine ⟨393718936991333243823715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8399337322481775868239253 393718936991333243823715)
                  ·
                    rfl

theorem cell21_1725221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1725221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725221 prefixEnd_1725221 := by exact prefixLift 1725221
  have htrace : WordTrace (prefixWord ++ tailWord_1725221) baseStart_1725221 baseEnd_1725221 := by
    simpa [prefixWord, tailWord_1725221, baseEnd_1725221] using wordTrace_append hprefix tailTrace_1725221
  have hstable : (prefixWord ++ tailWord_1725221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725221).length < 2 ^ (prefixWord ++ tailWord_1725221).sum := by decide
  have hdescent : baseEnd_1725221 < baseStart_1725221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725297 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1725297 : Nat := 118140960795 + 1725297 * 2 ^ 59
def prefixEnd_1725297 : Nat := 4983230072969 + 3 ^ 40 * 1725297 * 2
def baseEnd_1725297 : Nat := 393736281226774000556893

theorem tailTrace_1725297 : CollatzResearch.WordTrace tailWord_1725297 prefixEnd_1725297 393736281226774000556893 := by
  unfold tailWord_1725297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62926751230551101113846145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41951167487034067409230763 62926751230551101113846145)
  ·
    refine ⟨47195063422913325835384609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62926751230551101113846145 47195063422913325835384609)
    ·
      refine ⟨35396297567184994376538457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47195063422913325835384609 35396297567184994376538457)
      ·
        refine ⟨26547223175388745782403843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35396297567184994376538457 26547223175388745782403843)
        ·
          refine ⟨39820834763083118673605765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26547223175388745782403843 39820834763083118673605765)
          ·
            refine ⟨7466406518078084751301081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39820834763083118673605765 7466406518078084751301081)
            ·
              refine ⟨5599804888558563563475811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466406518078084751301081 5599804888558563563475811)
              ·
                refine ⟨8399707332837845345213717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599804888558563563475811 8399707332837845345213717)
                ·
                  refine ⟨393736281226774000556893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8399707332837845345213717 393736281226774000556893)
                  ·
                    rfl

theorem cell21_1725297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1725297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725297 prefixEnd_1725297 := by exact prefixLift 1725297
  have htrace : WordTrace (prefixWord ++ tailWord_1725297) baseStart_1725297 baseEnd_1725297 := by
    simpa [prefixWord, tailWord_1725297, baseEnd_1725297] using wordTrace_append hprefix tailTrace_1725297
  have hstable : (prefixWord ++ tailWord_1725297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725297).length < 2 ^ (prefixWord ++ tailWord_1725297).sum := by decide
  have hdescent : baseEnd_1725297 < baseStart_1725297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725311 : List Nat := [1, 1, 2, 2, 1, 1, 5, 8]
def baseStart_1725311 : Nat := 118140960795 + 1725311 * 2 ^ 59
def prefixEnd_1725311 : Nat := 4983230072969 + 3 ^ 40 * 1725311 * 2
def baseEnd_1725311 : Nat := 131246492072504362441177

theorem tailTrace_1725311 : CollatzResearch.WordTrace tailWord_1725311 prefixEnd_1725311 131246492072504362441177 := by
  unfold tailWord_1725311
  simp only [CollatzResearch.WordTrace]
  refine ⟨62927261852500381504855787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41951507901666921003237191 62927261852500381504855787)
  ·
    refine ⟨94390892778750572257283681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62927261852500381504855787 94390892778750572257283681)
    ·
      refine ⟨70793169584062929192962761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94390892778750572257283681 70793169584062929192962761)
      ·
        refine ⟨53094877188047196894722071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70793169584062929192962761 53094877188047196894722071)
        ·
          refine ⟨79642315782070795342083107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53094877188047196894722071 79642315782070795342083107)
          ·
            refine ⟨119463473673106193013124661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79642315782070795342083107 119463473673106193013124661)
            ·
              refine ⟨11199700656853705594980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119463473673106193013124661 11199700656853705594980437)
              ·
                refine ⟨131246492072504362441177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11199700656853705594980437 131246492072504362441177)
                ·
                  rfl

theorem cell21_1725311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_1725311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725311 prefixEnd_1725311 := by exact prefixLift 1725311
  have htrace : WordTrace (prefixWord ++ tailWord_1725311) baseStart_1725311 baseEnd_1725311 := by
    simpa [prefixWord, tailWord_1725311, baseEnd_1725311] using wordTrace_append hprefix tailTrace_1725311
  have hstable : (prefixWord ++ tailWord_1725311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725311).length < 2 ^ (prefixWord ++ tailWord_1725311).sum := by decide
  have hdescent : baseEnd_1725311 < baseStart_1725311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725351 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 3]
def baseStart_1725351 : Nat := 118140960795 + 1725351 * 2 ^ 59
def prefixEnd_1725351 : Nat := 4983230072969 + 3 ^ 40 * 1725351 * 2
def baseEnd_1725351 : Nat := 393748604762481906656783

theorem tailTrace_1725351 : CollatzResearch.WordTrace tailWord_1725351 prefixEnd_1725351 393748604762481906656783 := by
  unfold tailWord_1725351
  simp only [CollatzResearch.WordTrace]
  refine ⟨62928720772355468336311907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41952480514903645557541271 62928720772355468336311907)
  ·
    refine ⟨94393081158533202504467861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62928720772355468336311907 94393081158533202504467861)
    ·
      refine ⟨4424675679306243867396931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94393081158533202504467861 4424675679306243867396931)
      ·
        refine ⟨6637013518959365801095397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4424675679306243867396931 6637013518959365801095397)
        ·
          refine ⟨1244440034804881087705387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6637013518959365801095397 1244440034804881087705387)
          ·
            refine ⟨1866660052207321631558081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244440034804881087705387 1866660052207321631558081)
            ·
              refine ⟨1399995039155491223668561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866660052207321631558081 1399995039155491223668561)
              ·
                refine ⟨1049996279366618417751421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399995039155491223668561 1049996279366618417751421)
                ·
                  refine ⟨393748604762481906656783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049996279366618417751421 393748604762481906656783)
                  ·
                    rfl

theorem cell21_1725351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].length) (baseStart_1725351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725351 prefixEnd_1725351 := by exact prefixLift 1725351
  have htrace : WordTrace (prefixWord ++ tailWord_1725351) baseStart_1725351 baseEnd_1725351 := by
    simpa [prefixWord, tailWord_1725351, baseEnd_1725351] using wordTrace_append hprefix tailTrace_1725351
  have hstable : (prefixWord ++ tailWord_1725351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725351).length < 2 ^ (prefixWord ++ tailWord_1725351).sum := by decide
  have hdescent : baseEnd_1725351 < baseStart_1725351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725407 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_1725407 : Nat := 118140960795 + 1725407 * 2 ^ 59
def prefixEnd_1725407 : Nat := 4983230072969 + 3 ^ 40 * 1725407 * 2
def baseEnd_1725407 : Nat := 393761384725438253723335

theorem tailTrace_1725407 : CollatzResearch.WordTrace tailWord_1725407 prefixEnd_1725407 393761384725438253723335 := by
  unfold tailWord_1725407
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930763260152589900350475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41953842173435059933566983 62930763260152589900350475)
  ·
    refine ⟨94396144890228884850525713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62930763260152589900350475 94396144890228884850525713)
    ·
      refine ⟨70797108667671663637894285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94396144890228884850525713 70797108667671663637894285)
      ·
        refine ⟨26548915750376873864210357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70797108667671663637894285 26548915750376873864210357)
        ·
          refine ⟨2488960851597831924769721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26548915750376873864210357 2488960851597831924769721)
          ·
            refine ⟨1866720638698373943577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488960851597831924769721 1866720638698373943577291)
            ·
              refine ⟨2800080958047560915365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866720638698373943577291 2800080958047560915365937)
              ·
                refine ⟨2100060718535670686524453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800080958047560915365937 2100060718535670686524453)
                ·
                  refine ⟨393761384725438253723335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100060718535670686524453 393761384725438253723335)
                  ·
                    rfl

theorem cell21_1725407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_1725407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725407 prefixEnd_1725407 := by exact prefixLift 1725407
  have htrace : WordTrace (prefixWord ++ tailWord_1725407) baseStart_1725407 baseEnd_1725407 := by
    simpa [prefixWord, tailWord_1725407, baseEnd_1725407] using wordTrace_append hprefix tailTrace_1725407
  have hstable : (prefixWord ++ tailWord_1725407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725407).length < 2 ^ (prefixWord ++ tailWord_1725407).sum := by decide
  have hdescent : baseEnd_1725407 < baseStart_1725407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725452 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_1725452 : Nat := 118140960795 + 1725452 * 2 ^ 59
def prefixEnd_1725452 : Nat := 4983230072969 + 3 ^ 40 * 1725452 * 2
def baseEnd_1725452 : Nat := 393771654338528175473243

theorem tailTrace_1725452 : CollatzResearch.WordTrace tailWord_1725452 prefixEnd_1725452 393771654338528175473243 := by
  unfold tailWord_1725452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466202272494781292869305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41954936363326375057159073 31466202272494781292869305)
  ·
    refine ⟨23599651704371085969651979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31466202272494781292869305 23599651704371085969651979)
    ·
      refine ⟨35399477556556628954477969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23599651704371085969651979 35399477556556628954477969)
      ·
        refine ⟨26549608167417471715858477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35399477556556628954477969 26549608167417471715858477)
        ·
          refine ⟨9956103062781551893446929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26549608167417471715858477 9956103062781551893446929)
          ·
            refine ⟨7467077297086163920085197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9956103062781551893446929 7467077297086163920085197)
            ·
              refine ⟨2800153986407311470031949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7467077297086163920085197 2800153986407311470031949)
              ·
                refine ⟨1050057744902741801261981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800153986407311470031949 1050057744902741801261981)
                ·
                  refine ⟨393771654338528175473243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050057744902741801261981 393771654338528175473243)
                  ·
                    rfl

theorem cell21_1725452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_1725452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725452 prefixEnd_1725452 := by exact prefixLift 1725452
  have htrace : WordTrace (prefixWord ++ tailWord_1725452) baseStart_1725452 baseEnd_1725452 := by
    simpa [prefixWord, tailWord_1725452, baseEnd_1725452] using wordTrace_append hprefix tailTrace_1725452
  have hstable : (prefixWord ++ tailWord_1725452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725452).length < 2 ^ (prefixWord ++ tailWord_1725452).sum := by decide
  have hdescent : baseEnd_1725452 < baseStart_1725452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725469 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 5]
def baseStart_1725469 : Nat := 118140960795 + 1725469 * 2 ^ 59
def prefixEnd_1725469 : Nat := 4983230072969 + 3 ^ 40 * 1725469 * 2
def baseEnd_1725469 : Nat := 393775533970139923689875

theorem tailTrace_1725469 : CollatzResearch.WordTrace tailWord_1725469 prefixEnd_1725469 393775533970139923689875 := by
  unfold tailWord_1725469
  simp only [CollatzResearch.WordTrace]
  refine ⟨62933024585927974489107461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41955349723951982992738307 62933024585927974489107461)
  ·
    refine ⟨11799942109861495216707649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62933024585927974489107461 11799942109861495216707649)
    ·
      refine ⟨8849956582396121412530737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11799942109861495216707649 8849956582396121412530737)
      ·
        refine ⟨6637467436797091059398053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849956582396121412530737 6637467436797091059398053)
        ·
          refine ⟨1244525144399454573637135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6637467436797091059398053 1244525144399454573637135)
          ·
            refine ⟨1866787716599181860455703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244525144399454573637135 1866787716599181860455703)
            ·
              refine ⟨2800181574898772790683555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866787716599181860455703 2800181574898772790683555)
              ·
                refine ⟨4200272362348159186025333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800181574898772790683555 4200272362348159186025333)
                ·
                  refine ⟨393775533970139923689875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4200272362348159186025333 393775533970139923689875)
                  ·
                    rfl

theorem cell21_1725469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_1725469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725469 prefixEnd_1725469 := by exact prefixLift 1725469
  have htrace : WordTrace (prefixWord ++ tailWord_1725469) baseStart_1725469 baseEnd_1725469 := by
    simpa [prefixWord, tailWord_1725469, baseEnd_1725469] using wordTrace_append hprefix tailTrace_1725469
  have hstable : (prefixWord ++ tailWord_1725469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725469).length < 2 ^ (prefixWord ++ tailWord_1725469).sum := by decide
  have hdescent : baseEnd_1725469 < baseStart_1725469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725576 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_1725576 : Nat := 118140960795 + 1725576 * 2 ^ 59
def prefixEnd_1725576 : Nat := 4983230072969 + 3 ^ 40 * 1725576 * 2
def baseEnd_1725576 : Nat := 393799952827931515406323

theorem tailTrace_1725576 : CollatzResearch.WordTrace tailWord_1725576 prefixEnd_1725576 393799952827931515406323 := by
  unfold tailWord_1725576
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468463598270165881626291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41957951464360221175501721 31468463598270165881626291)
  ·
    refine ⟨47202695397405248822439437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31468463598270165881626291 47202695397405248822439437)
    ·
      refine ⟨17701010774026968308414789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47202695397405248822439437 17701010774026968308414789)
      ·
        refine ⟨3318939520130056557827773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17701010774026968308414789 3318939520130056557827773)
        ·
          refine ⟨1244602320048771209185415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3318939520130056557827773 1244602320048771209185415)
          ·
            refine ⟨1866903480073156813778123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244602320048771209185415 1866903480073156813778123)
            ·
              refine ⟨2800355220109735220667185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866903480073156813778123 2800355220109735220667185)
              ·
                refine ⟨2100266415082301415500389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800355220109735220667185 2100266415082301415500389)
                ·
                  refine ⟨393799952827931515406323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100266415082301415500389 393799952827931515406323)
                  ·
                    rfl

theorem cell21_1725576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_1725576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725576 prefixEnd_1725576 := by exact prefixLift 1725576
  have htrace : WordTrace (prefixWord ++ tailWord_1725576) baseStart_1725576 baseEnd_1725576 := by
    simpa [prefixWord, tailWord_1725576, baseEnd_1725576] using wordTrace_append hprefix tailTrace_1725576
  have hstable : (prefixWord ++ tailWord_1725576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725576).length < 2 ^ (prefixWord ++ tailWord_1725576).sum := by decide
  have hdescent : baseEnd_1725576 < baseStart_1725576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725587 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 3]
def baseStart_1725587 : Nat := 118140960795 + 1725587 * 2 ^ 59
def prefixEnd_1725587 : Nat := 4983230072969 + 3 ^ 40 * 1725587 * 2
def baseEnd_1725587 : Nat := 393802463177797940722967

theorem tailTrace_1725587 : CollatzResearch.WordTrace tailWord_1725587 prefixEnd_1725587 393802463177797940722967 := by
  unfold tailWord_1725587
  simp only [CollatzResearch.WordTrace]
  refine ⟨62937328399500480641903015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41958218933000320427935343 62937328399500480641903015)
  ·
    refine ⟨94405992599250720962854523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62937328399500480641903015 94405992599250720962854523)
    ·
      refine ⟨141608988898876081444281785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94405992599250720962854523 141608988898876081444281785)
      ·
        refine ⟨106206741674157061083211339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141608988898876081444281785 106206741674157061083211339)
        ·
          refine ⟨159310112511235591624817009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106206741674157061083211339 159310112511235591624817009)
          ·
            refine ⟨119482584383426693718612757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159310112511235591624817009 119482584383426693718612757)
            ·
              refine ⟨5600746142973126268059973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119482584383426693718612757 5600746142973126268059973)
              ·
                refine ⟨1050139901807461175261245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5600746142973126268059973 1050139901807461175261245)
                ·
                  refine ⟨393802463177797940722967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050139901807461175261245 393802463177797940722967)
                  ·
                    rfl

theorem cell21_1725587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].length) (baseStart_1725587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725587 prefixEnd_1725587 := by exact prefixLift 1725587
  have htrace : WordTrace (prefixWord ++ tailWord_1725587) baseStart_1725587 baseEnd_1725587 := by
    simpa [prefixWord, tailWord_1725587, baseEnd_1725587] using wordTrace_append hprefix tailTrace_1725587
  have hstable : (prefixWord ++ tailWord_1725587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725587).length < 2 ^ (prefixWord ++ tailWord_1725587).sum := by decide
  have hdescent : baseEnd_1725587 < baseStart_1725587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725632 : List Nat := [2, 1, 1, 2, 6, 2, 7]
def baseStart_1725632 : Nat := 118140960795 + 1725632 * 2 ^ 59
def prefixEnd_1725632 : Nat := 4983230072969 + 3 ^ 40 * 1725632 * 2
def baseEnd_1725632 : Nat := 43756970310098651385875

theorem tailTrace_1725632 : CollatzResearch.WordTrace tailWord_1725632 prefixEnd_1725632 43756970310098651385875 := by
  unfold tailWord_1725632
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469484842168726663645575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41959313122891635551527433 31469484842168726663645575)
  ·
    refine ⟨47204227263253089995468363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31469484842168726663645575 47204227263253089995468363)
    ·
      refine ⟨70806340894879634993202545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47204227263253089995468363 70806340894879634993202545)
      ·
        refine ⟨53104755671159726244901909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70806340894879634993202545 53104755671159726244901909)
        ·
          refine ⟨2489285422085612167729777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53104755671159726244901909 2489285422085612167729777)
          ·
            refine ⟨1866964066564209125797333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489285422085612167729777 1866964066564209125797333)
            ·
              refine ⟨43756970310098651385875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1866964066564209125797333 43756970310098651385875)
              ·
                rfl

theorem cell21_1725632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 7].length) (baseStart_1725632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725632 prefixEnd_1725632 := by exact prefixLift 1725632
  have htrace : WordTrace (prefixWord ++ tailWord_1725632) baseStart_1725632 baseEnd_1725632 := by
    simpa [prefixWord, tailWord_1725632, baseEnd_1725632] using wordTrace_append hprefix tailTrace_1725632
  have hstable : (prefixWord ++ tailWord_1725632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725632).length < 2 ^ (prefixWord ++ tailWord_1725632).sum := by decide
  have hdescent : baseEnd_1725632 < baseStart_1725632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725694 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1725694 : Nat := 118140960795 + 1725694 * 2 ^ 59
def prefixEnd_1725694 : Nat := 4983230072969 + 3 ^ 40 * 1725694 * 2
def baseEnd_1725694 : Nat := 393826882035589532439415

theorem tailTrace_1725694 : CollatzResearch.WordTrace tailWord_1725694 prefixEnd_1725694 393826882035589532439415 := by
  unfold tailWord_1725694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867653876264104739506017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41960820673408558610698757 7867653876264104739506017)
  ·
    refine ⟨5900740407198078554629513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7867653876264104739506017 5900740407198078554629513)
    ·
      refine ⟨4425555305398558915972135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5900740407198078554629513 4425555305398558915972135)
      ·
        refine ⟨6638332958097838373958203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425555305398558915972135 6638332958097838373958203)
        ·
          refine ⟨9957499437146757560937305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638332958097838373958203 9957499437146757560937305)
          ·
            refine ⟨7468124577860068170702979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957499437146757560937305 7468124577860068170702979)
            ·
              refine ⟨11202186866790102256054469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468124577860068170702979 11202186866790102256054469)
              ·
                refine ⟨2100410037523144173010213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11202186866790102256054469 2100410037523144173010213)
                ·
                  refine ⟨393826882035589532439415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100410037523144173010213 393826882035589532439415)
                  ·
                    rfl

theorem cell21_1725694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1725694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725694 prefixEnd_1725694 := by exact prefixLift 1725694
  have htrace : WordTrace (prefixWord ++ tailWord_1725694) baseStart_1725694 baseEnd_1725694 := by
    simpa [prefixWord, tailWord_1725694, baseEnd_1725694] using wordTrace_append hprefix tailTrace_1725694
  have hstable : (prefixWord ++ tailWord_1725694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725694).length < 2 ^ (prefixWord ++ tailWord_1725694).sum := by decide
  have hdescent : baseEnd_1725694 < baseStart_1725694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725697 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 3]
def baseStart_1725697 : Nat := 118140960795 + 1725697 * 2 ^ 59
def prefixEnd_1725697 : Nat := 4983230072969 + 3 ^ 40 * 1725697 * 2
def baseEnd_1725697 : Nat := 393827566676462193889409

theorem tailTrace_1725697 : CollatzResearch.WordTrace tailWord_1725697 prefixEnd_1725697 393827566676462193889409 := by
  unfold tailWord_1725697
  simp only [CollatzResearch.WordTrace]
  refine ⟨62941340429101969428407345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41960893619401312952271563 62941340429101969428407345)
  ·
    refine ⟨47206005321826477071305509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62941340429101969428407345 47206005321826477071305509)
    ·
      refine ⟨8851125997842464450869783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47206005321826477071305509 8851125997842464450869783)
      ·
        refine ⟨13276688996763696676304675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851125997842464450869783 13276688996763696676304675)
        ·
          refine ⟨19915033495145545014457013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276688996763696676304675 19915033495145545014457013)
          ·
            refine ⟨1867034390169894845105345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19915033495145545014457013 1867034390169894845105345)
            ·
              refine ⟨1400275792627421133829009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867034390169894845105345 1400275792627421133829009)
              ·
                refine ⟨1050206844470565850371757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400275792627421133829009 1050206844470565850371757)
                ·
                  refine ⟨393827566676462193889409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050206844470565850371757 393827566676462193889409)
                  ·
                    rfl

theorem cell21_1725697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_1725697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725697 prefixEnd_1725697 := by exact prefixLift 1725697
  have htrace : WordTrace (prefixWord ++ tailWord_1725697) baseStart_1725697 baseEnd_1725697 := by
    simpa [prefixWord, tailWord_1725697, baseEnd_1725697] using wordTrace_append hprefix tailTrace_1725697
  have hstable : (prefixWord ++ tailWord_1725697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725697).length < 2 ^ (prefixWord ++ tailWord_1725697).sum := by decide
  have hdescent : baseEnd_1725697 < baseStart_1725697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725708 : List Nat := [2, 2, 1, 2, 2, 5, 1, 6]
def baseStart_1725708 : Nat := 118140960795 + 1725708 * 2 ^ 59
def prefixEnd_1725708 : Nat := 4983230072969 + 3 ^ 40 * 1725708 * 2
def baseEnd_1725708 : Nat := 131276692342109539735351

theorem tailTrace_1725708 : CollatzResearch.WordTrace tailWord_1725708 prefixEnd_1725708 131276692342109539735351 := by
  unfold tailWord_1725708
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470870816031059153528889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41961161088041412204705185 31470870816031059153528889)
  ·
    refine ⟨23603153112023294365146667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31470870816031059153528889 23603153112023294365146667)
    ·
      refine ⟨35404729668034941547720001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603153112023294365146667 35404729668034941547720001)
      ·
        refine ⟨26553547251026206160790001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35404729668034941547720001 26553547251026206160790001)
        ·
          refine ⟨19915160438269654620592501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26553547251026206160790001 19915160438269654620592501)
          ·
            refine ⟨1867046291087780120680547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19915160438269654620592501 1867046291087780120680547)
            ·
              refine ⟨2800569436631670181020821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867046291087780120680547 2800569436631670181020821)
              ·
                refine ⟨131276692342109539735351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2800569436631670181020821 131276692342109539735351)
                ·
                  rfl

theorem cell21_1725708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_1725708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725708 prefixEnd_1725708 := by exact prefixLift 1725708
  have htrace : WordTrace (prefixWord ++ tailWord_1725708) baseStart_1725708 baseEnd_1725708 := by
    simpa [prefixWord, tailWord_1725708, baseEnd_1725708] using wordTrace_append hprefix tailTrace_1725708
  have hstable : (prefixWord ++ tailWord_1725708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725708).length < 2 ^ (prefixWord ++ tailWord_1725708).sum := by decide
  have hdescent : baseEnd_1725708 < baseStart_1725708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725722 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1725722 : Nat := 118140960795 + 1725722 * 2 ^ 59
def prefixEnd_1725722 : Nat := 4983230072969 + 3 ^ 40 * 1725722 * 2
def baseEnd_1725722 : Nat := 393833272017067705972691

theorem tailTrace_1725722 : CollatzResearch.WordTrace tailWord_1725722 prefixEnd_1725722 393833272017067705972691 := by
  unfold tailWord_1725722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15735563063502849674516855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41961501502674265798711613 15735563063502849674516855)
  ·
    refine ⟨23603344595254274511775283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15735563063502849674516855 23603344595254274511775283)
    ·
      refine ⟨35405016892881411767662925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603344595254274511775283 35405016892881411767662925)
      ·
        refine ⟨13276881334830529412873597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35405016892881411767662925 13276881334830529412873597)
        ·
          refine ⟨4978830500561448529827599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13276881334830529412873597 4978830500561448529827599)
          ·
            refine ⟨7468245750842172794741399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978830500561448529827599 7468245750842172794741399)
            ·
              refine ⟨11202368626263259192112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468245750842172794741399 11202368626263259192112099)
              ·
                refine ⟨16803552939394888788168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202368626263259192112099 16803552939394888788168149)
                ·
                  refine ⟨393833272017067705972691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16803552939394888788168149 393833272017067705972691)
                  ·
                    rfl

theorem cell21_1725722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1725722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725722 prefixEnd_1725722 := by exact prefixLift 1725722
  have htrace : WordTrace (prefixWord ++ tailWord_1725722) baseStart_1725722 baseEnd_1725722 := by
    simpa [prefixWord, tailWord_1725722, baseEnd_1725722] using wordTrace_append hprefix tailTrace_1725722
  have hstable : (prefixWord ++ tailWord_1725722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725722).length < 2 ^ (prefixWord ++ tailWord_1725722).sum := by decide
  have hdescent : baseEnd_1725722 < baseStart_1725722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725725 : List Nat := [1, 4, 2, 3, 1, 2, 3, 5]
def baseStart_1725725 : Nat := 118140960795 + 1725725 * 2 ^ 59
def prefixEnd_1725725 : Nat := 4983230072969 + 3 ^ 40 * 1725725 * 2
def baseEnd_1725725 : Nat := 131277985552646789140895

theorem tailTrace_1725725 : CollatzResearch.WordTrace tailWord_1725725 prefixEnd_1725725 131277985552646789140895 := by
  unfold tailWord_1725725
  simp only [CollatzResearch.WordTrace]
  refine ⟨62942361673000530210426629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41961574448667020140284419 62942361673000530210426629)
  ·
    refine ⟨11801692813687599414454993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62942361673000530210426629 11801692813687599414454993)
    ·
      refine ⟨8851269610265699560841245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11801692813687599414454993 8851269610265699560841245)
      ·
        refine ⟨3319226103849637335315467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8851269610265699560841245 3319226103849637335315467)
        ·
          refine ⟨4978839155774456002973201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319226103849637335315467 4978839155774456002973201)
          ·
            refine ⟨3734129366830842002229901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4978839155774456002973201 3734129366830842002229901)
            ·
              refine ⟨1400298512561565750836213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734129366830842002229901 1400298512561565750836213)
              ·
                refine ⟨131277985552646789140895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1400298512561565750836213 131277985552646789140895)
                ·
                  rfl

theorem cell21_1725725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].length) (baseStart_1725725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725725 prefixEnd_1725725 := by exact prefixLift 1725725
  have htrace : WordTrace (prefixWord ++ tailWord_1725725) baseStart_1725725 baseEnd_1725725 := by
    simpa [prefixWord, tailWord_1725725, baseEnd_1725725] using wordTrace_append hprefix tailTrace_1725725
  have hstable : (prefixWord ++ tailWord_1725725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725725).length < 2 ^ (prefixWord ++ tailWord_1725725).sum := by decide
  have hdescent : baseEnd_1725725 < baseStart_1725725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725953 : List Nat := [1, 2, 4, 1, 4, 2, 2, 5]
def baseStart_1725953 : Nat := 118140960795 + 1725953 * 2 ^ 59
def prefixEnd_1725953 : Nat := 4983230072969 + 3 ^ 40 * 1725953 * 2
def baseEnd_1725953 : Nat := 131295329788087545874073

theorem tailTrace_1725953 : CollatzResearch.WordTrace tailWord_1725953 prefixEnd_1725953 131295329788087545874073 := by
  unfold tailWord_1725953
  simp only [CollatzResearch.WordTrace]
  refine ⟨62950677516174525149726513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41967118344116350099817675 62950677516174525149726513)
  ·
    refine ⟨47213008137130893862294885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62950677516174525149726513 47213008137130893862294885)
    ·
      refine ⟨8852439025712042599180291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47213008137130893862294885 8852439025712042599180291)
      ·
        refine ⟨13278658538568063898770437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852439025712042599180291 13278658538568063898770437)
        ·
          refine ⟨2489748475981511981019457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13278658538568063898770437 2489748475981511981019457)
          ·
            refine ⟨1867311356986133985764593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489748475981511981019457 1867311356986133985764593)
            ·
              refine ⟨1400483517739600489323445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867311356986133985764593 1400483517739600489323445)
              ·
                refine ⟨131295329788087545874073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1400483517739600489323445 131295329788087545874073)
                ·
                  rfl

theorem cell21_1725953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].length) (baseStart_1725953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725953 prefixEnd_1725953 := by exact prefixLift 1725953
  have htrace : WordTrace (prefixWord ++ tailWord_1725953) baseStart_1725953 baseEnd_1725953 := by
    simpa [prefixWord, tailWord_1725953, baseEnd_1725953] using wordTrace_append hprefix tailTrace_1725953
  have hstable : (prefixWord ++ tailWord_1725953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725953).length < 2 ^ (prefixWord ++ tailWord_1725953).sum := by decide
  have hdescent : baseEnd_1725953 < baseStart_1725953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725981 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1725981 : Nat := 118140960795 + 1725981 * 2 ^ 59
def prefixEnd_1725981 : Nat := 4983230072969 + 3 ^ 40 * 1725981 * 2
def baseEnd_1725981 : Nat := 393892379345740811155495

theorem tailTrace_1725981 : CollatzResearch.WordTrace tailWord_1725981 prefixEnd_1725981 393892379345740811155495 := by
  unfold tailWord_1725981
  simp only [CollatzResearch.WordTrace]
  refine ⟨62951698760073085931745797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41967799173382057287830531 62951698760073085931745797)
  ·
    refine ⟨11803443517513703612202337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62951698760073085931745797 11803443517513703612202337)
    ·
      refine ⟨8852582638135277709151753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11803443517513703612202337 8852582638135277709151753)
      ·
        refine ⟨6639436978601458281863815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8852582638135277709151753 6639436978601458281863815)
        ·
          refine ⟨9959155467902187422795723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639436978601458281863815 9959155467902187422795723)
          ·
            refine ⟨14938733201853281134193585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9959155467902187422795723 14938733201853281134193585)
            ·
              refine ⟨11204049901389960850645189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14938733201853281134193585 11204049901389960850645189)
              ·
                refine ⟨2100759356510617659495973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11204049901389960850645189 2100759356510617659495973)
                ·
                  refine ⟨393892379345740811155495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100759356510617659495973 393892379345740811155495)
                  ·
                    rfl

theorem cell21_1725981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1725981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725981 prefixEnd_1725981 := by exact prefixLift 1725981
  have htrace : WordTrace (prefixWord ++ tailWord_1725981) baseStart_1725981 baseEnd_1725981 := by
    simpa [prefixWord, tailWord_1725981, baseEnd_1725981] using wordTrace_append hprefix tailTrace_1725981
  have hstable : (prefixWord ++ tailWord_1725981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725981).length < 2 ^ (prefixWord ++ tailWord_1725981).sum := by decide
  have hdescent : baseEnd_1725981 < baseStart_1725981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725998 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1725998 : Nat := 118140960795 + 1725998 * 2 ^ 59
def prefixEnd_1725998 : Nat := 4983230072969 + 3 ^ 40 * 1725998 * 2
def baseEnd_1725998 : Nat := 393896258977352559372127

theorem tailTrace_1725998 : CollatzResearch.WordTrace tailWord_1725998 prefixEnd_1725998 393896258977352559372127 := by
  unfold tailWord_1725998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869039850126437229389331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41968212534007665223409765 7869039850126437229389331)
  ·
    refine ⟨11803559775189655844083997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7869039850126437229389331 11803559775189655844083997)
    ·
      refine ⟨4426334915696120941531499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11803559775189655844083997 4426334915696120941531499)
      ·
        refine ⟨6639502373544181412297249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426334915696120941531499 6639502373544181412297249)
        ·
          refine ⟨4979626780158136059222937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639502373544181412297249 4979626780158136059222937)
          ·
            refine ⟨3734720085118602044417203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4979626780158136059222937 3734720085118602044417203)
            ·
              refine ⟨5602080127677903066625805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734720085118602044417203 5602080127677903066625805)
              ·
                refine ⟨2100780047879213649984677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5602080127677903066625805 2100780047879213649984677)
                ·
                  refine ⟨393896258977352559372127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100780047879213649984677 393896258977352559372127)
                  ·
                    rfl

theorem cell21_1725998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1725998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1725998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1725998 prefixEnd_1725998 := by exact prefixLift 1725998
  have htrace : WordTrace (prefixWord ++ tailWord_1725998) baseStart_1725998 baseEnd_1725998 := by
    simpa [prefixWord, tailWord_1725998, baseEnd_1725998] using wordTrace_append hprefix tailTrace_1725998
  have hstable : (prefixWord ++ tailWord_1725998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725998).length < 2 ^ (prefixWord ++ tailWord_1725998).sum := by decide
  have hdescent : baseEnd_1725998 < baseStart_1725998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726085 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1726085 : Nat := 118140960795 + 1726085 * 2 ^ 59
def prefixEnd_1726085 : Nat := 4983230072969 + 3 ^ 40 * 1726085 * 2
def baseEnd_1726085 : Nat := 393916113562659741421949

theorem tailTrace_1726085 : CollatzResearch.WordTrace tailWord_1726085 prefixEnd_1726085 393916113562659741421949 := by
  unfold tailWord_1726085
  simp only [CollatzResearch.WordTrace]
  refine ⟨62955491951696311693531709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41970327967797541129021139 62955491951696311693531709)
  ·
    refine ⟨23608309481886116885074391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62955491951696311693531709 23608309481886116885074391)
    ·
      refine ⟨35412464222829175327611587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23608309481886116885074391 35412464222829175327611587)
      ·
        refine ⟨53118696334243762991417381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35412464222829175327611587 53118696334243762991417381)
        ·
          refine ⟨9959755562670705560890759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53118696334243762991417381 9959755562670705560890759)
          ·
            refine ⟨14939633344006058341336139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9959755562670705560890759 14939633344006058341336139)
            ·
              refine ⟨22409450016009087512004209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14939633344006058341336139 22409450016009087512004209)
              ·
                refine ⟨16807087512006815634003157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22409450016009087512004209 16807087512006815634003157)
                ·
                  refine ⟨393916113562659741421949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16807087512006815634003157 393916113562659741421949)
                  ·
                    rfl

theorem cell21_1726085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1726085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726085 prefixEnd_1726085 := by exact prefixLift 1726085
  have htrace : WordTrace (prefixWord ++ tailWord_1726085) baseStart_1726085 baseEnd_1726085 := by
    simpa [prefixWord, tailWord_1726085, baseEnd_1726085] using wordTrace_append hprefix tailTrace_1726085
  have hstable : (prefixWord ++ tailWord_1726085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726085).length < 2 ^ (prefixWord ++ tailWord_1726085).sum := by decide
  have hdescent : baseEnd_1726085 < baseStart_1726085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726088 : List Nat := [2, 1, 3, 5, 1, 1, 8]
def baseStart_1726088 : Nat := 118140960795 + 1726088 * 2 ^ 59
def prefixEnd_1726088 : Nat := 4983230072969 + 3 ^ 40 * 1726088 * 2
def baseEnd_1726088 : Nat := 43768533133725822541327

theorem tailTrace_1726088 : CollatzResearch.WordTrace tailWord_1726088 prefixEnd_1726088 43768533133725822541327 := by
  unfold tailWord_1726088
  simp only [CollatzResearch.WordTrace]
  refine ⟨31477800685342721602945459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41970400913790295470593945 31477800685342721602945459)
  ·
    refine ⟨47216701028014082404418189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31477800685342721602945459 47216701028014082404418189)
    ·
      refine ⟨17706262885505280901656821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47216701028014082404418189 17706262885505280901656821)
      ·
        refine ⟨1659962145516120084530327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17706262885505280901656821 1659962145516120084530327)
        ·
          refine ⟨2489943218274180126795491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659962145516120084530327 2489943218274180126795491)
          ·
            refine ⟨3734914827411270190193237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489943218274180126795491 3734914827411270190193237)
            ·
              refine ⟨43768533133725822541327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3734914827411270190193237 43768533133725822541327)
              ·
                rfl

theorem cell21_1726088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 8].length) (baseStart_1726088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726088 prefixEnd_1726088 := by exact prefixLift 1726088
  have htrace : WordTrace (prefixWord ++ tailWord_1726088) baseStart_1726088 baseEnd_1726088 := by
    simpa [prefixWord, tailWord_1726088, baseEnd_1726088] using wordTrace_append hprefix tailTrace_1726088
  have hstable : (prefixWord ++ tailWord_1726088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726088).length < 2 ^ (prefixWord ++ tailWord_1726088).sum := by decide
  have hdescent : baseEnd_1726088 < baseStart_1726088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726164 : List Nat := [2, 4, 1, 3, 1, 2, 2, 6]
def baseStart_1726164 : Nat := 118140960795 + 1726164 * 2 ^ 59
def prefixEnd_1726164 : Nat := 4983230072969 + 3 ^ 40 * 1726164 * 2
def baseEnd_1726164 : Nat := 131311380812991053201707

theorem tailTrace_1726164 : CollatzResearch.WordTrace tailWord_1726164 prefixEnd_1726164 131311380812991053201707 := by
  unfold tailWord_1726164
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479186659205054092828773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41972248878940072123771697 31479186659205054092828773)
  ·
    refine ⟨5902347498600947642405395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31479186659205054092828773 5902347498600947642405395)
    ·
      refine ⟨8853521247901421463608093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902347498600947642405395 8853521247901421463608093)
      ·
        refine ⟨3320070467963033048853035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8853521247901421463608093 3320070467963033048853035)
        ·
          refine ⟨4980105701944549573279553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320070467963033048853035 4980105701944549573279553)
          ·
            refine ⟨3735079276458412179959665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980105701944549573279553 3735079276458412179959665)
            ·
              refine ⟨2801309457343809134969749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735079276458412179959665 2801309457343809134969749)
              ·
                refine ⟨131311380812991053201707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2801309457343809134969749 131311380812991053201707)
                ·
                  rfl

theorem cell21_1726164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_1726164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726164 prefixEnd_1726164 := by exact prefixLift 1726164
  have htrace : WordTrace (prefixWord ++ tailWord_1726164) baseStart_1726164 baseEnd_1726164 := by
    simpa [prefixWord, tailWord_1726164, baseEnd_1726164] using wordTrace_append hprefix tailTrace_1726164
  have hstable : (prefixWord ++ tailWord_1726164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726164).length < 2 ^ (prefixWord ++ tailWord_1726164).sum := by decide
  have hdescent : baseEnd_1726164 < baseStart_1726164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726212 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1726212 : Nat := 118140960795 + 1726212 * 2 ^ 59
def prefixEnd_1726212 : Nat := 4983230072969 + 3 ^ 40 * 1726212 * 2
def baseEnd_1726212 : Nat := 393945096692935742805023

theorem tailTrace_1726212 : CollatzResearch.WordTrace tailWord_1726212 prefixEnd_1726212 393945096692935742805023 := by
  unfold tailWord_1726212
  simp only [CollatzResearch.WordTrace]
  refine ⟨31480062011118106191702445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41973416014824141588936593 31480062011118106191702445)
  ·
    refine ⟨11805023254169289821888417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31480062011118106191702445 11805023254169289821888417)
    ·
      refine ⟨8853767440626967366416313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11805023254169289821888417 8853767440626967366416313)
      ·
        refine ⟨6640325580470225524812235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8853767440626967366416313 6640325580470225524812235)
        ·
          refine ⟨9960488370705338287218353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6640325580470225524812235 9960488370705338287218353)
          ·
            refine ⟨7470366278029003715413765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960488370705338287218353 7470366278029003715413765)
            ·
              refine ⟨1400693677130438196640081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7470366278029003715413765 1400693677130438196640081)
              ·
                refine ⟨1050520257847828647480061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400693677130438196640081 1050520257847828647480061)
                ·
                  refine ⟨393945096692935742805023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050520257847828647480061 393945096692935742805023)
                  ·
                    rfl

theorem cell21_1726212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1726212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726212 prefixEnd_1726212 := by exact prefixLift 1726212
  have htrace : WordTrace (prefixWord ++ tailWord_1726212) baseStart_1726212 baseEnd_1726212 := by
    simpa [prefixWord, tailWord_1726212, baseEnd_1726212] using wordTrace_append hprefix tailTrace_1726212
  have hstable : (prefixWord ++ tailWord_1726212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726212).length < 2 ^ (prefixWord ++ tailWord_1726212).sum := by decide
  have hdescent : baseEnd_1726212 < baseStart_1726212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726226 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1726226 : Nat := 118140960795 + 1726226 * 2 ^ 59
def prefixEnd_1726226 : Nat := 4983230072969 + 3 ^ 40 * 1726226 * 2
def baseEnd_1726226 : Nat := 393948291683674829571661

theorem tailTrace_1726226 : CollatzResearch.WordTrace tailWord_1726226 prefixEnd_1726226 393948291683674829571661 := by
  unfold tailWord_1726226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740158661046373193603633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41973756429456995182943021 15740158661046373193603633)
  ·
    refine ⟨11805118995784779895202725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15740158661046373193603633 11805118995784779895202725)
    ·
      refine ⟨2213459811709646230350511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11805118995784779895202725 2213459811709646230350511)
      ·
        refine ⟨3320189717564469345525767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213459811709646230350511 3320189717564469345525767)
        ·
          refine ⟨4980284576346704018288651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320189717564469345525767 4980284576346704018288651)
          ·
            refine ⟨7470426864520056027432977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980284576346704018288651 7470426864520056027432977)
            ·
              refine ⟨5602820148390042020574733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470426864520056027432977 5602820148390042020574733)
              ·
                refine ⟨2101057555646265757715525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5602820148390042020574733 2101057555646265757715525)
                ·
                  refine ⟨393948291683674829571661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101057555646265757715525 393948291683674829571661)
                  ·
                    rfl

theorem cell21_1726226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1726226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726226 prefixEnd_1726226 := by exact prefixLift 1726226
  have htrace : WordTrace (prefixWord ++ tailWord_1726226) baseStart_1726226 baseEnd_1726226 := by
    simpa [prefixWord, tailWord_1726226, baseEnd_1726226] using wordTrace_append hprefix tailTrace_1726226
  have hstable : (prefixWord ++ tailWord_1726226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726226).length < 2 ^ (prefixWord ++ tailWord_1726226).sum := by decide
  have hdescent : baseEnd_1726226 < baseStart_1726226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726282 : List Nat := [3, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1726282 : Nat := 118140960795 + 1726282 * 2 ^ 59
def prefixEnd_1726282 : Nat := 4983230072969 + 3 ^ 40 * 1726282 * 2
def baseEnd_1726282 : Nat := 131320357215543725546071

theorem tailTrace_1726282 : CollatzResearch.WordTrace tailWord_1726282 prefixEnd_1726282 131320357215543725546071 := by
  unfold tailWord_1726282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740669282995653584613275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41975118087988409558968733 15740669282995653584613275)
  ·
    refine ⟨23611003924493480376919913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15740669282995653584613275 23611003924493480376919913)
    ·
      refine ⟨17708252943370110282689935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23611003924493480376919913 17708252943370110282689935)
      ·
        refine ⟨26562379415055165424034903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17708252943370110282689935 26562379415055165424034903)
        ·
          refine ⟨39843569122582748136052355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26562379415055165424034903 39843569122582748136052355)
          ·
            refine ⟨59765353683874122204078533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39843569122582748136052355 59765353683874122204078533)
            ·
              refine ⟨11206003815726397913264725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59765353683874122204078533 11206003815726397913264725)
              ·
                refine ⟨131320357215543725546071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11206003815726397913264725 131320357215543725546071)
                ·
                  rfl

theorem cell21_1726282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1726282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726282 prefixEnd_1726282 := by exact prefixLift 1726282
  have htrace : WordTrace (prefixWord ++ tailWord_1726282) baseStart_1726282 baseEnd_1726282 := by
    simpa [prefixWord, tailWord_1726282, baseEnd_1726282] using wordTrace_append hprefix tailTrace_1726282
  have hstable : (prefixWord ++ tailWord_1726282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726282).length < 2 ^ (prefixWord ++ tailWord_1726282).sum := by decide
  have hdescent : baseEnd_1726282 < baseStart_1726282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726330 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1726330 : Nat := 118140960795 + 1726330 * 2 ^ 59
def prefixEnd_1726330 : Nat := 4983230072969 + 3 ^ 40 * 1726330 * 2
def baseEnd_1726330 : Nat := 393972025900593759838115

theorem tailTrace_1726330 : CollatzResearch.WordTrace tailWord_1726330 prefixEnd_1726330 393972025900593759838115 := by
  unfold tailWord_1726330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741106958952179634050111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41976285223872479024133629 15741106958952179634050111)
  ·
    refine ⟨23611660438428269451075167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15741106958952179634050111 23611660438428269451075167)
    ·
      refine ⟨35417490657642404176612751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23611660438428269451075167 35417490657642404176612751)
      ·
        refine ⟨53126235986463606264919127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35417490657642404176612751 53126235986463606264919127)
        ·
          refine ⟨79689353979695409397378691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53126235986463606264919127 79689353979695409397378691)
          ·
            refine ⟨119534030969543114096068037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79689353979695409397378691 119534030969543114096068037)
            ·
              refine ⟨22412630806789333893012757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119534030969543114096068037 22412630806789333893012757)
              ·
                refine ⟨1050592069068250026234973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22412630806789333893012757 1050592069068250026234973)
                ·
                  refine ⟨393972025900593759838115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050592069068250026234973 393972025900593759838115)
                  ·
                    rfl

theorem cell21_1726330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1726330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726330 prefixEnd_1726330 := by exact prefixLift 1726330
  have htrace : WordTrace (prefixWord ++ tailWord_1726330) baseStart_1726330 baseEnd_1726330 := by
    simpa [prefixWord, tailWord_1726330, baseEnd_1726330] using wordTrace_append hprefix tailTrace_1726330
  have hstable : (prefixWord ++ tailWord_1726330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726330).length < 2 ^ (prefixWord ++ tailWord_1726330).sum := by decide
  have hdescent : baseEnd_1726330 < baseStart_1726330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726420 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1726420 : Nat := 118140960795 + 1726420 * 2 ^ 59
def prefixEnd_1726420 : Nat := 4983230072969 + 3 ^ 40 * 1726420 * 2
def baseEnd_1726420 : Nat := 393992565126773603337931

theorem tailTrace_1726420 : CollatzResearch.WordTrace tailWord_1726420 prefixEnd_1726420 393992565126773603337931 := by
  unfold tailWord_1726420
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483855202741331953488357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41978473603655109271317809 31483855202741331953488357)
  ·
    refine ⟨5903222850513999741279067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31483855202741331953488357 5903222850513999741279067)
    ·
      refine ⟨8854834275770999611918601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903222850513999741279067 8854834275770999611918601)
      ·
        refine ⟨6641125706828249708938951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8854834275770999611918601 6641125706828249708938951)
        ·
          refine ⟨9961688560242374563408427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641125706828249708938951 9961688560242374563408427)
          ·
            refine ⟨14942532840363561845112641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961688560242374563408427 14942532840363561845112641)
            ·
              refine ⟨11206899630272671383834481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14942532840363561845112641 11206899630272671383834481)
              ·
                refine ⟨8405174722704503537875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11206899630272671383834481 8405174722704503537875861)
                ·
                  refine ⟨393992565126773603337931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8405174722704503537875861 393992565126773603337931)
                  ·
                    rfl

theorem cell21_1726420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1726420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726420 prefixEnd_1726420 := by exact prefixLift 1726420
  have htrace : WordTrace (prefixWord ++ tailWord_1726420) baseStart_1726420 baseEnd_1726420 := by
    simpa [prefixWord, tailWord_1726420, baseEnd_1726420] using wordTrace_append hprefix tailTrace_1726420
  have hstable : (prefixWord ++ tailWord_1726420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726420).length < 2 ^ (prefixWord ++ tailWord_1726420).sum := by decide
  have hdescent : baseEnd_1726420 < baseStart_1726420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726465 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1726465 : Nat := 118140960795 + 1726465 * 2 ^ 59
def prefixEnd_1726465 : Nat := 4983230072969 + 3 ^ 40 * 1726465 * 2
def baseEnd_1726465 : Nat := 394002834739863525087839

theorem tailTrace_1726465 : CollatzResearch.WordTrace tailWord_1726465 prefixEnd_1726465 394002834739863525087839 := by
  unfold tailWord_1726465
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969351690319636592364849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41979567793546424394909899 62969351690319636592364849)
  ·
    refine ⟨47227013767739727444273637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62969351690319636592364849 47227013767739727444273637)
    ·
      refine ⟨8855065081451198895801307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47227013767739727444273637 8855065081451198895801307)
      ·
        refine ⟨13282597622176798343701961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855065081451198895801307 13282597622176798343701961)
        ·
          refine ⟨9961948216632598757776471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13282597622176798343701961 9961948216632598757776471)
          ·
            refine ⟨14942922324948898136664707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961948216632598757776471 14942922324948898136664707)
            ·
              refine ⟨22414383487423347204997061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942922324948898136664707 22414383487423347204997061)
              ·
                refine ⟨4202696903891877600936949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22414383487423347204997061 4202696903891877600936949)
                ·
                  refine ⟨394002834739863525087839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202696903891877600936949 394002834739863525087839)
                  ·
                    rfl

theorem cell21_1726465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1726465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726465 prefixEnd_1726465 := by exact prefixLift 1726465
  have htrace : WordTrace (prefixWord ++ tailWord_1726465) baseStart_1726465 baseEnd_1726465 := by
    simpa [prefixWord, tailWord_1726465, baseEnd_1726465] using wordTrace_append hprefix tailTrace_1726465
  have hstable : (prefixWord ++ tailWord_1726465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726465).length < 2 ^ (prefixWord ++ tailWord_1726465).sum := by decide
  have hdescent : baseEnd_1726465 < baseStart_1726465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726468 : List Nat := [2, 3, 2, 4, 1, 1, 1, 7]
def baseStart_1726468 : Nat := 118140960795 + 1726468 * 2 ^ 59
def prefixEnd_1726468 : Nat := 4983230072969 + 3 ^ 40 * 1726468 * 2
def baseEnd_1726468 : Nat := 131334506460245395512611

theorem tailTrace_1726468 : CollatzResearch.WordTrace tailWord_1726468 prefixEnd_1726468 131334506460245395512611 := by
  unfold tailWord_1726468
  simp only [CollatzResearch.WordTrace]
  refine ⟨31484730554654384052362029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41979640739539178736482705 31484730554654384052362029)
  ·
    refine ⟨11806773957995394019635761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31484730554654384052362029 11806773957995394019635761)
    ·
      refine ⟨8855080468496545514726821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11806773957995394019635761 8855080468496545514726821)
      ·
        refine ⟨1660327587843102284011279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8855080468496545514726821 1660327587843102284011279)
        ·
          refine ⟨2490491381764653426016919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660327587843102284011279 2490491381764653426016919)
          ·
            refine ⟨3735737072646980139025379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490491381764653426016919 3735737072646980139025379)
            ·
              refine ⟨5603605608970470208538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735737072646980139025379 5603605608970470208538069)
              ·
                refine ⟨131334506460245395512611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5603605608970470208538069 131334506460245395512611)
                ·
                  rfl

theorem cell21_1726468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_1726468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726468 prefixEnd_1726468 := by exact prefixLift 1726468
  have htrace : WordTrace (prefixWord ++ tailWord_1726468) baseStart_1726468 baseEnd_1726468 := by
    simpa [prefixWord, tailWord_1726468, baseEnd_1726468] using wordTrace_append hprefix tailTrace_1726468
  have hstable : (prefixWord ++ tailWord_1726468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726468).length < 2 ^ (prefixWord ++ tailWord_1726468).sum := by decide
  have hdescent : baseEnd_1726468 < baseStart_1726468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726499 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 3]
def baseStart_1726499 : Nat := 118140960795 + 1726499 * 2 ^ 59
def prefixEnd_1726499 : Nat := 4983230072969 + 3 ^ 40 * 1726499 * 2
def baseEnd_1726499 : Nat := 394010594003087021521103

theorem tailTrace_1726499 : CollatzResearch.WordTrace tailWord_1726499 prefixEnd_1726499 394010594003087021521103 := by
  unfold tailWord_1726499
  simp only [CollatzResearch.WordTrace]
  refine ⟨62970591772196460399102551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41980394514797640266068367 62970591772196460399102551)
  ·
    refine ⟨94455887658294690598653827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62970591772196460399102551 94455887658294690598653827)
    ·
      refine ⟨141683831487442035897980741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94455887658294690598653827 141683831487442035897980741)
      ·
        refine ⟨26565718403895381730871389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141683831487442035897980741 26565718403895381730871389)
        ·
          refine ⟨9962144401460768149076771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26565718403895381730871389 9962144401460768149076771)
          ·
            refine ⟨14943216602191152223615157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962144401460768149076771 14943216602191152223615157)
            ·
              refine ⟨1400926556455420520963921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14943216602191152223615157 1400926556455420520963921)
              ·
                refine ⟨1050694917341565390722941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400926556455420520963921 1050694917341565390722941)
                ·
                  refine ⟨394010594003087021521103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050694917341565390722941 394010594003087021521103)
                  ·
                    rfl

theorem cell21_1726499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].length) (baseStart_1726499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726499 prefixEnd_1726499 := by exact prefixLift 1726499
  have htrace : WordTrace (prefixWord ++ tailWord_1726499) baseStart_1726499 baseEnd_1726499 := by
    simpa [prefixWord, tailWord_1726499, baseEnd_1726499] using wordTrace_append hprefix tailTrace_1726499
  have hstable : (prefixWord ++ tailWord_1726499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726499).length < 2 ^ (prefixWord ++ tailWord_1726499).sum := by decide
  have hdescent : baseEnd_1726499 < baseStart_1726499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726513 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 4]
def baseStart_1726513 : Nat := 118140960795 + 1726513 * 2 ^ 59
def prefixEnd_1726513 : Nat := 4983230072969 + 3 ^ 40 * 1726513 * 2
def baseEnd_1726513 : Nat := 394013788993826108287741

theorem tailTrace_1726513 : CollatzResearch.WordTrace tailWord_1726513 prefixEnd_1726513 394013788993826108287741 := by
  unfold tailWord_1726513
  simp only [CollatzResearch.WordTrace]
  refine ⟨62971102394145740790112193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41980734929430493860074795 62971102394145740790112193)
  ·
    refine ⟨47228326795609305592584145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62971102394145740790112193 47228326795609305592584145)
    ·
      refine ⟨35421245096706979194438109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47228326795609305592584145 35421245096706979194438109)
      ·
        refine ⟨13282966911265117197914291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35421245096706979194438109 13282966911265117197914291)
        ·
          refine ⟨19924450366897675796871437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13282966911265117197914291 19924450366897675796871437)
          ·
            refine ⟨7471668887586628423826789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19924450366897675796871437 7471668887586628423826789)
            ·
              refine ⟨1400937916422492829467523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7471668887586628423826789 1400937916422492829467523)
              ·
                refine ⟨2101406874633739244201285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400937916422492829467523 2101406874633739244201285)
                ·
                  refine ⟨394013788993826108287741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101406874633739244201285 394013788993826108287741)
                  ·
                    rfl

theorem cell21_1726513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_1726513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726513 prefixEnd_1726513 := by exact prefixLift 1726513
  have htrace : WordTrace (prefixWord ++ tailWord_1726513) baseStart_1726513 baseEnd_1726513 := by
    simpa [prefixWord, tailWord_1726513, baseEnd_1726513] using wordTrace_append hprefix tailTrace_1726513
  have hstable : (prefixWord ++ tailWord_1726513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726513).length < 2 ^ (prefixWord ++ tailWord_1726513).sum := by decide
  have hdescent : baseEnd_1726513 < baseStart_1726513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726550 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1726550 : Nat := 118140960795 + 1726550 * 2 ^ 59
def prefixEnd_1726550 : Nat := 4983230072969 + 3 ^ 40 * 1726550 * 2
def baseEnd_1726550 : Nat := 394022232897922266170999

theorem tailTrace_1726550 : CollatzResearch.WordTrace tailWord_1726550 prefixEnd_1726550 394022232897922266170999 := by
  unfold tailWord_1726550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935778243438231006825569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41981634596674464072806069 3935778243438231006825569)
  ·
    refine ⟨2951833682578673255119177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3935778243438231006825569 2951833682578673255119177)
    ·
      refine ⟨2213875261934004941339383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951833682578673255119177 2213875261934004941339383)
      ·
        refine ⟨3320812892901007412009075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213875261934004941339383 3320812892901007412009075)
        ·
          refine ⟨4981219339351511118013613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320812892901007412009075 4981219339351511118013613)
          ·
            refine ⟨1867957252256816669255105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4981219339351511118013613 1867957252256816669255105)
            ·
              refine ⟨1400967939192612501941329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867957252256816669255105 1400967939192612501941329)
              ·
                refine ⟨1050725954394459376455997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400967939192612501941329 1050725954394459376455997)
                ·
                  refine ⟨394022232897922266170999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050725954394459376455997 394022232897922266170999)
                  ·
                    rfl

theorem cell21_1726550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1726550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726550 prefixEnd_1726550 := by exact prefixLift 1726550
  have htrace : WordTrace (prefixWord ++ tailWord_1726550) baseStart_1726550 baseEnd_1726550 := by
    simpa [prefixWord, tailWord_1726550, baseEnd_1726550] using wordTrace_append hprefix tailTrace_1726550
  have hstable : (prefixWord ++ tailWord_1726550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726550).length < 2 ^ (prefixWord ++ tailWord_1726550).sum := by decide
  have hdescent : baseEnd_1726550 < baseStart_1726550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726572 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1726572 : Nat := 118140960795 + 1726572 * 2 ^ 59
def prefixEnd_1726572 : Nat := 4983230072969 + 3 ^ 40 * 1726572 * 2
def baseEnd_1726572 : Nat := 394027253597655116804287

theorem tailTrace_1726572 : CollatzResearch.WordTrace tailWord_1726572 prefixEnd_1726572 394027253597655116804287 := by
  unfold tailWord_1726572
  simp only [CollatzResearch.WordTrace]
  refine ⟨31486627150465996933254985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41982169533954662577673313 31486627150465996933254985)
  ·
    refine ⟨23614970362849497699941239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31486627150465996933254985 23614970362849497699941239)
    ·
      refine ⟨35422455544274246549911859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23614970362849497699941239 35422455544274246549911859)
      ·
        refine ⟨53133683316411369824867789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35422455544274246549911859 53133683316411369824867789)
        ·
          refine ⟨19925131243654263684325421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53133683316411369824867789 19925131243654263684325421)
          ·
            refine ⟨7471924216370348881622033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19925131243654263684325421 7471924216370348881622033)
            ·
              refine ⟨5603943162277761661216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471924216370348881622033 5603943162277761661216525)
              ·
                refine ⟨2101478685854160622956197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5603943162277761661216525 2101478685854160622956197)
                ·
                  refine ⟨394027253597655116804287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101478685854160622956197 394027253597655116804287)
                  ·
                    rfl

theorem cell21_1726572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1726572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726572 prefixEnd_1726572 := by exact prefixLift 1726572
  have htrace : WordTrace (prefixWord ++ tailWord_1726572) baseStart_1726572 baseEnd_1726572 := by
    simpa [prefixWord, tailWord_1726572, baseEnd_1726572] using wordTrace_append hprefix tailTrace_1726572
  have hstable : (prefixWord ++ tailWord_1726572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726572).length < 2 ^ (prefixWord ++ tailWord_1726572).sum := by decide
  have hdescent : baseEnd_1726572 < baseStart_1726572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726606 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1726606 : Nat := 118140960795 + 1726606 * 2 ^ 59
def prefixEnd_1726606 : Nat := 4983230072969 + 3 ^ 40 * 1726606 * 2
def baseEnd_1726606 : Nat := 394035012860878613237551

theorem tailTrace_1726606 : CollatzResearch.WordTrace tailWord_1726606 prefixEnd_1726606 394035012860878613237551 := by
  unfold tailWord_1726606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7871811797851102209155959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41982996255205878448831781 7871811797851102209155959)
  ·
    refine ⟨11807717696776653313733939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7871811797851102209155959 11807717696776653313733939)
    ·
      refine ⟨17711576545164979970600909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807717696776653313733939 17711576545164979970600909)
      ·
        refine ⟨6641841204436867488975341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17711576545164979970600909 6641841204436867488975341)
        ·
          refine ⟨2490690451663825308365753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6641841204436867488975341 2490690451663825308365753)
          ·
            refine ⟨1868017838747868981274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490690451663825308365753 1868017838747868981274315)
            ·
              refine ⟨2802026758121803471911473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868017838747868981274315 2802026758121803471911473)
              ·
                refine ⟨2101520068591352603933605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802026758121803471911473 2101520068591352603933605)
                ·
                  refine ⟨394035012860878613237551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101520068591352603933605 394035012860878613237551)
                  ·
                    rfl

theorem cell21_1726606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1726606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726606 prefixEnd_1726606 := by exact prefixLift 1726606
  have htrace : WordTrace (prefixWord ++ tailWord_1726606) baseStart_1726606 baseEnd_1726606 := by
    simpa [prefixWord, tailWord_1726606, baseEnd_1726606] using wordTrace_append hprefix tailTrace_1726606
  have hstable : (prefixWord ++ tailWord_1726606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726606).length < 2 ^ (prefixWord ++ tailWord_1726606).sum := by decide
  have hdescent : baseEnd_1726606 < baseStart_1726606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726668 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_1726668 : Nat := 118140960795 + 1726668 * 2 ^ 59
def prefixEnd_1726668 : Nat := 4983230072969 + 3 ^ 40 * 1726668 * 2
def baseEnd_1726668 : Nat := 394049162105580283204091

theorem tailTrace_1726668 : CollatzResearch.WordTrace tailWord_1726668 prefixEnd_1726668 394049162105580283204091 := by
  unfold tailWord_1726668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31488377854292101131002329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41984503805722801508003105 31488377854292101131002329)
  ·
    refine ⟨23616283390719075848251747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31488377854292101131002329 23616283390719075848251747)
    ·
      refine ⟨35424425086078613772377621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23616283390719075848251747 35424425086078613772377621)
      ·
        refine ⟨1660519925909935020580201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35424425086078613772377621 1660519925909935020580201)
        ·
          refine ⟨1245389944432451265435151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660519925909935020580201 1245389944432451265435151)
          ·
            refine ⟨1868084916648676898152727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245389944432451265435151 1868084916648676898152727)
            ·
              refine ⟨2802127374973015347229091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868084916648676898152727 2802127374973015347229091)
              ·
                refine ⟨4203191062459523020843637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802127374973015347229091 4203191062459523020843637)
                ·
                  refine ⟨394049162105580283204091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4203191062459523020843637 394049162105580283204091)
                  ·
                    rfl

theorem cell21_1726668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_1726668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726668 prefixEnd_1726668 := by exact prefixLift 1726668
  have htrace : WordTrace (prefixWord ++ tailWord_1726668) baseStart_1726668 baseEnd_1726668 := by
    simpa [prefixWord, tailWord_1726668, baseEnd_1726668] using wordTrace_append hprefix tailTrace_1726668
  have hstable : (prefixWord ++ tailWord_1726668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726668).length < 2 ^ (prefixWord ++ tailWord_1726668).sum := by decide
  have hdescent : baseEnd_1726668 < baseStart_1726668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726783 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_1726783 : Nat := 118140960795 + 1726783 * 2 ^ 59
def prefixEnd_1726783 : Nat := 4983230072969 + 3 ^ 40 * 1726783 * 2
def baseEnd_1726783 : Nat := 394075406672365638787189

theorem tailTrace_1726783 : CollatzResearch.WordTrace tailWord_1726783 prefixEnd_1726783 394075406672365638787189 := by
  unfold tailWord_1726783
  simp only [CollatzResearch.WordTrace]
  refine ⟨62980950103167576902441003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41987300068778384601627335 62980950103167576902441003)
  ·
    refine ⟨94471425154751365353661505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62980950103167576902441003 94471425154751365353661505)
    ·
      refine ⟨70853568866063524015246129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94471425154751365353661505 70853568866063524015246129)
      ·
        refine ⟨53140176649547643011434597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70853568866063524015246129 53140176649547643011434597)
        ·
          refine ⟨9963783121790183064643987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53140176649547643011434597 9963783121790183064643987)
          ·
            refine ⟨14945674682685274596965981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9963783121790183064643987 14945674682685274596965981)
            ·
              refine ⟨5604628006006977973862243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14945674682685274596965981 5604628006006977973862243)
              ·
                refine ⟨8406942009010466960793365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604628006006977973862243 8406942009010466960793365)
                ·
                  refine ⟨394075406672365638787189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8406942009010466960793365 394075406672365638787189)
                  ·
                    rfl

theorem cell21_1726783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_1726783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726783 prefixEnd_1726783 := by exact prefixLift 1726783
  have htrace : WordTrace (prefixWord ++ tailWord_1726783) baseStart_1726783 baseEnd_1726783 := by
    simpa [prefixWord, tailWord_1726783, baseEnd_1726783] using wordTrace_append hprefix tailTrace_1726783
  have hstable : (prefixWord ++ tailWord_1726783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726783).length < 2 ^ (prefixWord ++ tailWord_1726783).sum := by decide
  have hdescent : baseEnd_1726783 < baseStart_1726783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726845 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1726845 : Nat := 118140960795 + 1726845 * 2 ^ 59
def prefixEnd_1726845 : Nat := 4983230072969 + 3 ^ 40 * 1726845 * 2
def baseEnd_1726845 : Nat := 394089555917067308753729

theorem tailTrace_1726845 : CollatzResearch.WordTrace tailWord_1726845 prefixEnd_1726845 394089555917067308753729 := by
  unfold tailWord_1726845
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983211428942961491197989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41988807619295307660798659 62983211428942961491197989)
  ·
    refine ⟨11809352142926805279599623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62983211428942961491197989 11809352142926805279599623)
    ·
      refine ⟨17714028214390207919399435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11809352142926805279599623 17714028214390207919399435)
      ·
        refine ⟨26571042321585311879099153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17714028214390207919399435 26571042321585311879099153)
        ·
          refine ⟨19928281741188983909324365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26571042321585311879099153 19928281741188983909324365)
          ·
            refine ⟨7473105652945868965996637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19928281741188983909324365 7473105652945868965996637)
            ·
              refine ⟨2802414619854700862248739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7473105652945868965996637 2802414619854700862248739)
              ·
                refine ⟨4203621929782051293373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802414619854700862248739 4203621929782051293373109)
                ·
                  refine ⟨394089555917067308753729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4203621929782051293373109 394089555917067308753729)
                  ·
                    rfl

theorem cell21_1726845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1726845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726845 prefixEnd_1726845 := by exact prefixLift 1726845
  have htrace : WordTrace (prefixWord ++ tailWord_1726845) baseStart_1726845 baseEnd_1726845 := by
    simpa [prefixWord, tailWord_1726845, baseEnd_1726845] using wordTrace_append hprefix tailTrace_1726845
  have hstable : (prefixWord ++ tailWord_1726845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726845).length < 2 ^ (prefixWord ++ tailWord_1726845).sum := by decide
  have hdescent : baseEnd_1726845 < baseStart_1726845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726873 : List Nat := [1, 2, 1, 2, 1, 4, 1, 9]
def baseStart_1726873 : Nat := 118140960795 + 1726873 * 2 ^ 59
def prefixEnd_1726873 : Nat := 4983230072969 + 3 ^ 40 * 1726873 * 2
def baseEnd_1726873 : Nat := 131365315299515160762335

theorem tailTrace_1726873 : CollatzResearch.WordTrace tailWord_1726873 prefixEnd_1726873 131365315299515160762335 := by
  unfold tailWord_1726873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62984232672841522273217273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41989488448561014848811515 62984232672841522273217273)
  ·
    refine ⟨47238174504631141704912955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62984232672841522273217273 47238174504631141704912955)
    ·
      refine ⟨70857261756946712557369433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238174504631141704912955 70857261756946712557369433)
      ·
        refine ⟨53142946317710034418027075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70857261756946712557369433 53142946317710034418027075)
        ·
          refine ⟨79714419476565051627040613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53142946317710034418027075 79714419476565051627040613)
          ·
            refine ⟨14946453651855947180070115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79714419476565051627040613 14946453651855947180070115)
            ·
              refine ⟨22419680477783920770105173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946453651855947180070115 22419680477783920770105173)
              ·
                refine ⟨131365315299515160762335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22419680477783920770105173 131365315299515160762335)
                ·
                  rfl

theorem cell21_1726873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_1726873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726873 prefixEnd_1726873 := by exact prefixLift 1726873
  have htrace : WordTrace (prefixWord ++ tailWord_1726873) baseStart_1726873 baseEnd_1726873 := by
    simpa [prefixWord, tailWord_1726873, baseEnd_1726873] using wordTrace_append hprefix tailTrace_1726873
  have hstable : (prefixWord ++ tailWord_1726873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726873).length < 2 ^ (prefixWord ++ tailWord_1726873).sum := by decide
  have hdescent : baseEnd_1726873 < baseStart_1726873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726904 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_1726904 : Nat := 118140960795 + 1726904 * 2 ^ 59
def prefixEnd_1726904 : Nat := 4983230072969 + 3 ^ 40 * 1726904 * 2
def baseEnd_1726904 : Nat := 394103020520896317270275

theorem tailTrace_1726904 : CollatzResearch.WordTrace tailWord_1726904 prefixEnd_1726904 394103020520896317270275 := by
  unfold tailWord_1726904
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492681667864607283797883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41990242223819476378397177 31492681667864607283797883)
  ·
    refine ⟨47239022501796910925696825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31492681667864607283797883 47239022501796910925696825)
    ·
      refine ⟨35429266876347683194272619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47239022501796910925696825 35429266876347683194272619)
      ·
        refine ⟨53143900314521524791408929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35429266876347683194272619 53143900314521524791408929)
        ·
          refine ⟨39857925235891143593556697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53143900314521524791408929 39857925235891143593556697)
          ·
            refine ⟨29893443926918357695167523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39857925235891143593556697 29893443926918357695167523)
            ·
              refine ⟨44840165890377536542751285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29893443926918357695167523 44840165890377536542751285)
              ·
                refine ⟨4203765552222894050882933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44840165890377536542751285 4203765552222894050882933)
                ·
                  refine ⟨394103020520896317270275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4203765552222894050882933 394103020520896317270275)
                  ·
                    rfl

theorem cell21_1726904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_1726904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726904 prefixEnd_1726904 := by exact prefixLift 1726904
  have htrace : WordTrace (prefixWord ++ tailWord_1726904) baseStart_1726904 baseEnd_1726904 := by
    simpa [prefixWord, tailWord_1726904, baseEnd_1726904] using wordTrace_append hprefix tailTrace_1726904
  have hstable : (prefixWord ++ tailWord_1726904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726904).length < 2 ^ (prefixWord ++ tailWord_1726904).sum := by decide
  have hdescent : baseEnd_1726904 < baseStart_1726904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726938 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1726938 : Nat := 118140960795 + 1726938 * 2 ^ 59
def prefixEnd_1726938 : Nat := 4983230072969 + 3 ^ 40 * 1726938 * 2
def baseEnd_1726938 : Nat := 394110779784119813703539

theorem tailTrace_1726938 : CollatzResearch.WordTrace tailWord_1726938 prefixEnd_1726938 394110779784119813703539 := by
  unfold tailWord_1726938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15746650854401509593583367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41991068945070692249555645 15746650854401509593583367)
  ·
    refine ⟨23619976281602264390375051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15746650854401509593583367 23619976281602264390375051)
    ·
      refine ⟨35429964422403396585562577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23619976281602264390375051 35429964422403396585562577)
      ·
        refine ⟨26572473316802547439171933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35429964422403396585562577 26572473316802547439171933)
        ·
          refine ⟨9964677493800955289689475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26572473316802547439171933 9964677493800955289689475)
          ·
            refine ⟨14947016240701432934534213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964677493800955289689475 14947016240701432934534213)
            ·
              refine ⟨2802565545131518675225165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14947016240701432934534213 2802565545131518675225165)
              ·
                refine ⟨1050962079424319503209437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2802565545131518675225165 1050962079424319503209437)
                ·
                  refine ⟨394110779784119813703539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050962079424319503209437 394110779784119813703539)
                  ·
                    rfl

theorem cell21_1726938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1726938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726938 prefixEnd_1726938 := by exact prefixLift 1726938
  have htrace : WordTrace (prefixWord ++ tailWord_1726938) baseStart_1726938 baseEnd_1726938 := by
    simpa [prefixWord, tailWord_1726938, baseEnd_1726938] using wordTrace_append hprefix tailTrace_1726938
  have hstable : (prefixWord ++ tailWord_1726938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726938).length < 2 ^ (prefixWord ++ tailWord_1726938).sum := by decide
  have hdescent : baseEnd_1726938 < baseStart_1726938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726952 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_1726952 : Nat := 118140960795 + 1726952 * 2 ^ 59
def prefixEnd_1726952 : Nat := 4983230072969 + 3 ^ 40 * 1726952 * 2
def baseEnd_1726952 : Nat := 394113974774858900470177

theorem tailTrace_1726952 : CollatzResearch.WordTrace tailWord_1726952 prefixEnd_1726952 394113974774858900470177 := by
  unfold tailWord_1726952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493557019777659382671555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41991409359703545843562073 31493557019777659382671555)
  ·
    refine ⟨47240335529666489074007333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31493557019777659382671555 47240335529666489074007333)
    ·
      refine ⟨8857562911812466701376375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47240335529666489074007333 8857562911812466701376375)
      ·
        refine ⟨13286344367718700052064563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857562911812466701376375 13286344367718700052064563)
        ·
          refine ⟨19929516551578050078096845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286344367718700052064563 19929516551578050078096845)
          ·
            refine ⟨7473568706841768779286317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19929516551578050078096845 7473568706841768779286317)
            ·
              refine ⟨2802588265065663292232369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7473568706841768779286317 2802588265065663292232369)
              ·
                refine ⟨2101941198799247469174277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802588265065663292232369 2101941198799247469174277)
                ·
                  refine ⟨394113974774858900470177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101941198799247469174277 394113974774858900470177)
                  ·
                    rfl

theorem cell21_1726952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_1726952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726952 prefixEnd_1726952 := by exact prefixLift 1726952
  have htrace : WordTrace (prefixWord ++ tailWord_1726952) baseStart_1726952 baseEnd_1726952 := by
    simpa [prefixWord, tailWord_1726952, baseEnd_1726952] using wordTrace_append hprefix tailTrace_1726952
  have hstable : (prefixWord ++ tailWord_1726952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726952).length < 2 ^ (prefixWord ++ tailWord_1726952).sum := by decide
  have hdescent : baseEnd_1726952 < baseStart_1726952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726966 : List Nat := [5, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1726966 : Nat := 118140960795 + 1726966 * 2 ^ 59
def prefixEnd_1726966 : Nat := 4983230072969 + 3 ^ 40 * 1726966 * 2
def baseEnd_1726966 : Nat := 131372389921865995745605

theorem tailTrace_1726966 : CollatzResearch.WordTrace tailWord_1726966 prefixEnd_1726966 131372389921865995745605 := by
  unfold tailWord_1726966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936726541344037447272047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41991749774336399437568501 3936726541344037447272047)
  ·
    refine ⟨5905089812016056170908071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936726541344037447272047 5905089812016056170908071)
    ·
      refine ⟨8857634718024084256362107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905089812016056170908071 8857634718024084256362107)
      ·
        refine ⟨13286452077036126384543161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857634718024084256362107 13286452077036126384543161)
        ·
          refine ⟨9964839057777094788407371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286452077036126384543161 9964839057777094788407371)
          ·
            refine ⟨14947258586665642182611057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964839057777094788407371 14947258586665642182611057)
            ·
              refine ⟨11210443939999231636958293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947258586665642182611057 11210443939999231636958293)
              ·
                refine ⟨131372389921865995745605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11210443939999231636958293 131372389921865995745605)
                ·
                  rfl

theorem cell21_1726966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1726966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726966 prefixEnd_1726966 := by exact prefixLift 1726966
  have htrace : WordTrace (prefixWord ++ tailWord_1726966) baseStart_1726966 baseEnd_1726966 := by
    simpa [prefixWord, tailWord_1726966, baseEnd_1726966] using wordTrace_append hprefix tailTrace_1726966
  have hstable : (prefixWord ++ tailWord_1726966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726966).length < 2 ^ (prefixWord ++ tailWord_1726966).sum := by decide
  have hdescent : baseEnd_1726966 < baseStart_1726966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726989 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1726989 : Nat := 118140960795 + 1726989 * 2 ^ 59
def prefixEnd_1726989 : Nat := 4983230072969 + 3 ^ 40 * 1726989 * 2
def baseEnd_1726989 : Nat := 394122418678955058353435

theorem tailTrace_1726989 : CollatzResearch.WordTrace tailWord_1726989 prefixEnd_1726989 394122418678955058353435 := by
  unfold tailWord_1726989
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988463540421274084440021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41992309026947516056293347 62988463540421274084440021)
  ·
    refine ⟨1476292114228623611354063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62988463540421274084440021 1476292114228623611354063)
    ·
      refine ⟨2214438171342935417031095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476292114228623611354063 2214438171342935417031095)
      ·
        refine ⟨3321657257014403125546643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214438171342935417031095 3321657257014403125546643)
        ·
          refine ⟨4982485885521604688319965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321657257014403125546643 4982485885521604688319965)
          ·
            refine ⟨1868432207070601758119987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4982485885521604688319965 1868432207070601758119987)
            ·
              refine ⟨2802648310605902637179981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868432207070601758119987 2802648310605902637179981)
              ·
                refine ⟨1050993116477213488942493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2802648310605902637179981 1050993116477213488942493)
                ·
                  refine ⟨394122418678955058353435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050993116477213488942493 394122418678955058353435)
                  ·
                    rfl

theorem cell21_1726989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1726989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1726989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1726989 prefixEnd_1726989 := by exact prefixLift 1726989
  have htrace : WordTrace (prefixWord ++ tailWord_1726989) baseStart_1726989 baseEnd_1726989 := by
    simpa [prefixWord, tailWord_1726989, baseEnd_1726989] using wordTrace_append hprefix tailTrace_1726989
  have hstable : (prefixWord ++ tailWord_1726989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726989).length < 2 ^ (prefixWord ++ tailWord_1726989).sum := by decide
  have hdescent : baseEnd_1726989 < baseStart_1726989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727011 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_1727011 : Nat := 118140960795 + 1727011 * 2 ^ 59
def prefixEnd_1727011 : Nat := 4983230072969 + 3 ^ 40 * 1727011 * 2
def baseEnd_1727011 : Nat := 394127439378687908986723

theorem tailTrace_1727011 : CollatzResearch.WordTrace tailWord_1727011 prefixEnd_1727011 394127439378687908986723 := by
  unfold tailWord_1727011
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989265946341571841740887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41992843964227714561160591 62989265946341571841740887)
  ·
    refine ⟨94483898919512357762611331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62989265946341571841740887 94483898919512357762611331)
    ·
      refine ⟨141725848379268536643916997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94483898919512357762611331 141725848379268536643916997)
      ·
        refine ⟨26573596571112850620734437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141725848379268536643916997 26573596571112850620734437)
        ·
          refine ⟨4982549357083659491387707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26573596571112850620734437 4982549357083659491387707)
          ·
            refine ⟨7473824035625489237081561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982549357083659491387707 7473824035625489237081561)
            ·
              refine ⟨5605368026719116927811171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7473824035625489237081561 5605368026719116927811171)
              ·
                refine ⟨8408052040078675391716757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605368026719116927811171 8408052040078675391716757)
                ·
                  refine ⟨394127439378687908986723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8408052040078675391716757 394127439378687908986723)
                  ·
                    rfl

theorem cell21_1727011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_1727011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727011 prefixEnd_1727011 := by exact prefixLift 1727011
  have htrace : WordTrace (prefixWord ++ tailWord_1727011) baseStart_1727011 baseEnd_1727011 := by
    simpa [prefixWord, tailWord_1727011, baseEnd_1727011] using wordTrace_append hprefix tailTrace_1727011
  have hstable : (prefixWord ++ tailWord_1727011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727011).length < 2 ^ (prefixWord ++ tailWord_1727011).sum := by decide
  have hdescent : baseEnd_1727011 < baseStart_1727011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727025 : List Nat := [1, 2, 2, 3, 1, 1, 3, 8]
def baseStart_1727025 : Nat := 118140960795 + 1727025 * 2 ^ 59
def prefixEnd_1727025 : Nat := 4983230072969 + 3 ^ 40 * 1727025 * 2
def baseEnd_1727025 : Nat := 131376878123142331917787

theorem tailTrace_1727025 : CollatzResearch.WordTrace tailWord_1727025 prefixEnd_1727025 131376878123142331917787 := by
  unfold tailWord_1727025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989776568290852232750529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41993184378860568155167019 62989776568290852232750529)
  ·
    refine ⟨47242332426218139174562897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62989776568290852232750529 47242332426218139174562897)
    ·
      refine ⟨35431749319663604380922173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47242332426218139174562897 35431749319663604380922173)
      ·
        refine ⟨13286905994873851642845815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35431749319663604380922173 13286905994873851642845815)
        ·
          refine ⟨19930358992310777464268723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286905994873851642845815 19930358992310777464268723)
          ·
            refine ⟨29895538488466166196403085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19930358992310777464268723 29895538488466166196403085)
            ·
              refine ⟨11210826933174812323651157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29895538488466166196403085 11210826933174812323651157)
              ·
                refine ⟨131376878123142331917787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11210826933174812323651157 131376878123142331917787)
                ·
                  rfl

theorem cell21_1727025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_1727025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727025 prefixEnd_1727025 := by exact prefixLift 1727025
  have htrace : WordTrace (prefixWord ++ tailWord_1727025) baseStart_1727025 baseEnd_1727025 := by
    simpa [prefixWord, tailWord_1727025, baseEnd_1727025] using wordTrace_append hprefix tailTrace_1727025
  have hstable : (prefixWord ++ tailWord_1727025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727025).length < 2 ^ (prefixWord ++ tailWord_1727025).sum := by decide
  have hdescent : baseEnd_1727025 < baseStart_1727025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727087 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_1727087 : Nat := 118140960795 + 1727087 * 2 ^ 59
def prefixEnd_1727087 : Nat := 4983230072969 + 3 ^ 40 * 1727087 * 2
def baseEnd_1727087 : Nat := 394144783614128665719901

theorem tailTrace_1727087 : CollatzResearch.WordTrace tailWord_1727087 prefixEnd_1727087 394144783614128665719901 := by
  unfold tailWord_1727087
  simp only [CollatzResearch.WordTrace]
  refine ⟨62992037894066236821507515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41994691929377491214338343 62992037894066236821507515)
  ·
    refine ⟨94488056841099355232261273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62992037894066236821507515 94488056841099355232261273)
    ·
      refine ⟨70866042630824516424195955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94488056841099355232261273 70866042630824516424195955)
      ·
        refine ⟨106299063946236774636293933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70866042630824516424195955 106299063946236774636293933)
        ·
          refine ⟨39862148979838790488610225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106299063946236774636293933 39862148979838790488610225)
          ·
            refine ⟨29896611734879092866457669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39862148979838790488610225 29896611734879092866457669)
            ·
              refine ⟨5605614700289829912460813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29896611734879092866457669 5605614700289829912460813)
              ·
                refine ⟨2102105512608686217172805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5605614700289829912460813 2102105512608686217172805)
                ·
                  refine ⟨394144783614128665719901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102105512608686217172805 394144783614128665719901)
                  ·
                    rfl

theorem cell21_1727087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_1727087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727087 prefixEnd_1727087 := by exact prefixLift 1727087
  have htrace : WordTrace (prefixWord ++ tailWord_1727087) baseStart_1727087 baseEnd_1727087 := by
    simpa [prefixWord, tailWord_1727087, baseEnd_1727087] using wordTrace_append hprefix tailTrace_1727087
  have hstable : (prefixWord ++ tailWord_1727087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727087).length < 2 ^ (prefixWord ++ tailWord_1727087).sum := by decide
  have hdescent : baseEnd_1727087 < baseStart_1727087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727149 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1727149 : Nat := 118140960795 + 1727149 * 2 ^ 59
def prefixEnd_1727149 : Nat := 4983230072969 + 3 ^ 40 * 1727149 * 2
def baseEnd_1727149 : Nat := 394158932858830335686441

theorem tailTrace_1727149 : CollatzResearch.WordTrace tailWord_1727149 prefixEnd_1727149 394158932858830335686441 := by
  unfold tailWord_1727149
  simp only [CollatzResearch.WordTrace]
  refine ⟨62994299219841621410264501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41996199479894414273509667 62994299219841621410264501)
  ·
    refine ⟨5905715551860152007212297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62994299219841621410264501 5905715551860152007212297)
    ·
      refine ⟨4429286663895114005409223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5905715551860152007212297 4429286663895114005409223)
      ·
        refine ⟨6643929995842671008113835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4429286663895114005409223 6643929995842671008113835)
        ·
          refine ⟨9965894993764006512170753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643929995842671008113835 9965894993764006512170753)
          ·
            refine ⟨7474421245323004884128065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9965894993764006512170753 7474421245323004884128065)
            ·
              refine ⟨5605815933992253663096049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474421245323004884128065 5605815933992253663096049)
              ·
                refine ⟨4204361950494190247322037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605815933992253663096049 4204361950494190247322037)
                ·
                  refine ⟨394158932858830335686441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204361950494190247322037 394158932858830335686441)
                  ·
                    rfl

theorem cell21_1727149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1727149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727149 prefixEnd_1727149 := by exact prefixLift 1727149
  have htrace : WordTrace (prefixWord ++ tailWord_1727149) baseStart_1727149 baseEnd_1727149 := by
    simpa [prefixWord, tailWord_1727149, baseEnd_1727149] using wordTrace_append hprefix tailTrace_1727149
  have hstable : (prefixWord ++ tailWord_1727149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727149).length < 2 ^ (prefixWord ++ tailWord_1727149).sum := by decide
  have hdescent : baseEnd_1727149 < baseStart_1727149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727343 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_1727343 : Nat := 118140960795 + 1727343 * 2 ^ 59
def prefixEnd_1727343 : Nat := 4983230072969 + 3 ^ 40 * 1727343 * 2
def baseEnd_1727343 : Nat := 394203206301929109452711

theorem tailTrace_1727343 : CollatzResearch.WordTrace tailWord_1727343 prefixEnd_1727343 394203206301929109452711 := by
  unfold tailWord_1727343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001374981138792542826683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42000916654092528361884455 63001374981138792542826683)
  ·
    refine ⟨94502062471708188814240025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001374981138792542826683 94502062471708188814240025)
    ·
      refine ⟨70876546853781141610680019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94502062471708188814240025 70876546853781141610680019)
      ·
        refine ⟨106314820280671712416020029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70876546853781141610680019 106314820280671712416020029)
        ·
          refine ⟨39868057605251892156007511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106314820280671712416020029 39868057605251892156007511)
          ·
            refine ⟨59802086407877838234011267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39868057605251892156007511 59802086407877838234011267)
            ·
              refine ⟨89703129611816757351016901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59802086407877838234011267 89703129611816757351016901)
              ·
                refine ⟨16819336802215642003315669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89703129611816757351016901 16819336802215642003315669)
                ·
                  refine ⟨394203206301929109452711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16819336802215642003315669 394203206301929109452711)
                  ·
                    rfl

theorem cell21_1727343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_1727343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727343 prefixEnd_1727343 := by exact prefixLift 1727343
  have htrace : WordTrace (prefixWord ++ tailWord_1727343) baseStart_1727343 baseEnd_1727343 := by
    simpa [prefixWord, tailWord_1727343, baseEnd_1727343] using wordTrace_append hprefix tailTrace_1727343
  have hstable : (prefixWord ++ tailWord_1727343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727343).length < 2 ^ (prefixWord ++ tailWord_1727343).sum := by decide
  have hdescent : baseEnd_1727343 < baseStart_1727343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727414 : List Nat := [5, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1727414 : Nat := 118140960795 + 1727414 * 2 ^ 59
def prefixEnd_1727414 : Nat := 4983230072969 + 3 ^ 40 * 1727414 * 2
def baseEnd_1727414 : Nat := 131406469823082921256411

theorem tailTrace_1727414 : CollatzResearch.WordTrace tailWord_1727414 prefixEnd_1727414 131406469823082921256411 := by
  unfold tailWord_1727414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937747785242598229291331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42002643042587714445774197 3937747785242598229291331)
  ·
    refine ⟨5906621677863897343936997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937747785242598229291331 5906621677863897343936997)
    ·
      refine ⟨1107491564599480751988187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5906621677863897343936997 1107491564599480751988187)
      ·
        refine ⟨1661237346899221127982281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107491564599480751988187 1661237346899221127982281)
        ·
          refine ⟨1245928010174415845986711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661237346899221127982281 1245928010174415845986711)
          ·
            refine ⟨1868892015261623768980067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245928010174415845986711 1868892015261623768980067)
            ·
              refine ⟨2803338022892435653470101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868892015261623768980067 2803338022892435653470101)
              ·
                refine ⟨131406469823082921256411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2803338022892435653470101 131406469823082921256411)
                ·
                  rfl

theorem cell21_1727414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1727414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727414 prefixEnd_1727414 := by exact prefixLift 1727414
  have htrace : WordTrace (prefixWord ++ tailWord_1727414) baseStart_1727414 baseEnd_1727414 := by
    simpa [prefixWord, tailWord_1727414, baseEnd_1727414] using wordTrace_append hprefix tailTrace_1727414
  have hstable : (prefixWord ++ tailWord_1727414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727414).length < 2 ^ (prefixWord ++ tailWord_1727414).sum := by decide
  have hdescent : baseEnd_1727414 < baseStart_1727414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727436 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1727436 : Nat := 118140960795 + 1727436 * 2 ^ 59
def prefixEnd_1727436 : Nat := 4983230072969 + 3 ^ 40 * 1727436 * 2
def baseEnd_1727436 : Nat := 394224430168981614402521

theorem tailTrace_1727436 : CollatzResearch.WordTrace tailWord_1727436 prefixEnd_1727436 394224430168981614402521 := by
  unfold tailWord_1727436
  simp only [CollatzResearch.WordTrace]
  refine ⟨31502383484900934712981081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42003177979867912950641441 31502383484900934712981081)
  ·
    refine ⟨23626787613675701034735811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31502383484900934712981081 23626787613675701034735811)
    ·
      refine ⟨35440181420513551552103717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23626787613675701034735811 35440181420513551552103717)
      ·
        refine ⟨6645034016346290916019447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35440181420513551552103717 6645034016346290916019447)
        ·
          refine ⟨9967551024519436374029171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645034016346290916019447 9967551024519436374029171)
          ·
            refine ⟨14951326536779154561043757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9967551024519436374029171 14951326536779154561043757)
            ·
              refine ⟨5606747451292182960391409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14951326536779154561043757 5606747451292182960391409)
              ·
                refine ⟨4205060588469137220293557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606747451292182960391409 4205060588469137220293557)
                ·
                  refine ⟨394224430168981614402521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205060588469137220293557 394224430168981614402521)
                  ·
                    rfl

theorem cell21_1727436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1727436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727436 prefixEnd_1727436 := by exact prefixLift 1727436
  have htrace : WordTrace (prefixWord ++ tailWord_1727436) baseStart_1727436 baseEnd_1727436 := by
    simpa [prefixWord, tailWord_1727436, baseEnd_1727436] using wordTrace_append hprefix tailTrace_1727436
  have hstable : (prefixWord ++ tailWord_1727436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727436).length < 2 ^ (prefixWord ++ tailWord_1727436).sum := by decide
  have hdescent : baseEnd_1727436 < baseStart_1727436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727476 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1727476 : Nat := 118140960795 + 1727476 * 2 ^ 59
def prefixEnd_1727476 : Nat := 4983230072969 + 3 ^ 40 * 1727476 * 2
def baseEnd_1727476 : Nat := 394233558713950433735773

theorem tailTrace_1727476 : CollatzResearch.WordTrace tailWord_1727476 prefixEnd_1727476 394233558713950433735773 := by
  unfold tailWord_1727476
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503112944828478128709141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42004150593104637504945521 31503112944828478128709141)
  ·
    refine ⟨1476708419288834912283241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31503112944828478128709141 1476708419288834912283241)
    ·
      refine ⟨1107531314466626184212431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1476708419288834912283241 1107531314466626184212431)
      ·
        refine ⟨1661296971699939276318647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107531314466626184212431 1661296971699939276318647)
        ·
          refine ⟨2491945457549908914477971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661296971699939276318647 2491945457549908914477971)
          ·
            refine ⟨3737918186324863371716957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491945457549908914477971 3737918186324863371716957)
            ·
              refine ⟨1401719319871823764393859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3737918186324863371716957 1401719319871823764393859)
              ·
                refine ⟨2102578979807735646590789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401719319871823764393859 2102578979807735646590789)
                ·
                  refine ⟨394233558713950433735773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102578979807735646590789 394233558713950433735773)
                  ·
                    rfl

theorem cell21_1727476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1727476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727476 prefixEnd_1727476 := by exact prefixLift 1727476
  have htrace : WordTrace (prefixWord ++ tailWord_1727476) baseStart_1727476 baseEnd_1727476 := by
    simpa [prefixWord, tailWord_1727476, baseEnd_1727476] using wordTrace_append hprefix tailTrace_1727476
  have hstable : (prefixWord ++ tailWord_1727476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727476).length < 2 ^ (prefixWord ++ tailWord_1727476).sum := by decide
  have hdescent : baseEnd_1727476 < baseStart_1727476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727484 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1727484 : Nat := 118140960795 + 1727484 * 2 ^ 59
def prefixEnd_1727484 : Nat := 4983230072969 + 3 ^ 40 * 1727484 * 2
def baseEnd_1727484 : Nat := 394235384422944197602423

theorem tailTrace_1727484 : CollatzResearch.WordTrace tailWord_1727484 prefixEnd_1727484 394235384422944197602423 := by
  unfold tailWord_1727484
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503258836813986811854753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42004345115751982415806337 31503258836813986811854753)
  ·
    refine ⟨23627444127610490108891065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31503258836813986811854753 23627444127610490108891065)
    ·
      refine ⟨17720583095707867581668299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23627444127610490108891065 17720583095707867581668299)
      ·
        refine ⟨26580874643561801372502449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17720583095707867581668299 26580874643561801372502449)
        ·
          refine ⟨19935655982671351029376837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26580874643561801372502449 19935655982671351029376837)
          ·
            refine ⟨3737935496750878318008157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19935655982671351029376837 3737935496750878318008157)
            ·
              refine ⟨1401725811281579369253059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3737935496750878318008157 1401725811281579369253059)
              ·
                refine ⟨2102588716922369053879589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401725811281579369253059 2102588716922369053879589)
                ·
                  refine ⟨394235384422944197602423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102588716922369053879589 394235384422944197602423)
                  ·
                    rfl

theorem cell21_1727484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1727484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727484 prefixEnd_1727484 := by exact prefixLift 1727484
  have htrace : WordTrace (prefixWord ++ tailWord_1727484) baseStart_1727484 baseEnd_1727484 := by
    simpa [prefixWord, tailWord_1727484, baseEnd_1727484] using wordTrace_append hprefix tailTrace_1727484
  have hstable : (prefixWord ++ tailWord_1727484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727484).length < 2 ^ (prefixWord ++ tailWord_1727484).sum := by decide
  have hdescent : baseEnd_1727484 < baseStart_1727484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727498 : List Nat := [3, 1, 2, 2, 3, 1, 4, 5]
def baseStart_1727498 : Nat := 118140960795 + 1727498 * 2 ^ 59
def prefixEnd_1727498 : Nat := 4983230072969 + 3 ^ 40 * 1727498 * 2
def baseEnd_1727498 : Nat := 131412859804561094789687

theorem tailTrace_1727498 : CollatzResearch.WordTrace tailWord_1727498 prefixEnd_1727498 131412859804561094789687 := by
  unfold tailWord_1727498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15751757073894313503679787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42004685530384836009812765 15751757073894313503679787)
  ·
    refine ⟨23627635610841470255519681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15751757073894313503679787 23627635610841470255519681)
    ·
      refine ⟨17720726708131102691639761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23627635610841470255519681 17720726708131102691639761)
      ·
        refine ⟨13290545031098327018729821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17720726708131102691639761 13290545031098327018729821)
        ·
          refine ⟨4983954386661872632023683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13290545031098327018729821 4983954386661872632023683)
          ·
            refine ⟨7475931579992808948035525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983954386661872632023683 7475931579992808948035525)
            ·
              refine ⟨1401737171248651677756661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7475931579992808948035525 1401737171248651677756661)
              ·
                refine ⟨131412859804561094789687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401737171248651677756661 131412859804561094789687)
                ·
                  rfl

theorem cell21_1727498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_1727498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727498 prefixEnd_1727498 := by exact prefixLift 1727498
  have htrace : WordTrace (prefixWord ++ tailWord_1727498) baseStart_1727498 baseEnd_1727498 := by
    simpa [prefixWord, tailWord_1727498, baseEnd_1727498] using wordTrace_append hprefix tailTrace_1727498
  have hstable : (prefixWord ++ tailWord_1727498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727498).length < 2 ^ (prefixWord ++ tailWord_1727498).sum := by decide
  have hdescent : baseEnd_1727498 < baseStart_1727498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727574 : List Nat := [5, 2, 2, 1, 11]
def baseStart_1727574 : Nat := 118140960795 + 1727574 * 2 ^ 59
def prefixEnd_1727574 : Nat := 4983230072969 + 3 ^ 40 * 1727574 * 2
def baseEnd_1727574 : Nat := 4867357082087951124719

theorem tailTrace_1727574 : CollatzResearch.WordTrace tailWord_1727574 prefixEnd_1727574 4867357082087951124719 := by
  unfold tailWord_1727574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938112515206369937155361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42006533495534612662990517 3938112515206369937155361)
  ·
    refine ⟨2953584386404777452866521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3938112515206369937155361 2953584386404777452866521)
    ·
      refine ⟨2215188289803583089649891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953584386404777452866521 2215188289803583089649891)
      ·
        refine ⟨3322782434705374634474837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215188289803583089649891 3322782434705374634474837)
        ·
          refine ⟨4867357082087951124719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3322782434705374634474837 4867357082087951124719)
          ·
            rfl

theorem cell21_1727574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 11].length) (baseStart_1727574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727574 prefixEnd_1727574 := by exact prefixLift 1727574
  have htrace : WordTrace (prefixWord ++ tailWord_1727574) baseStart_1727574 baseEnd_1727574 := by
    simpa [prefixWord, tailWord_1727574, baseEnd_1727574] using wordTrace_append hprefix tailTrace_1727574
  have hstable : (prefixWord ++ tailWord_1727574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727574).length < 2 ^ (prefixWord ++ tailWord_1727574).sum := by decide
  have hdescent : baseEnd_1727574 < baseStart_1727574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727616 : List Nat := [2, 1, 1, 2, 1, 3, 2, 9]
def baseStart_1727616 : Nat := 118140960795 + 1727616 * 2 ^ 59
def prefixEnd_1727616 : Nat := 4983230072969 + 3 ^ 40 * 1727616 * 2
def baseEnd_1727616 : Nat := 131421836207113767134051

theorem tailTrace_1727616 : CollatzResearch.WordTrace tailWord_1727616 prefixEnd_1727616 131421836207113767134051 := by
  unfold tailWord_1727616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31505666054574880083757351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42007554739433173445009801 31505666054574880083757351)
  ·
    refine ⟨47258499081862320125636027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31505666054574880083757351 47258499081862320125636027)
    ·
      refine ⟨70887748622793480188454041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47258499081862320125636027 70887748622793480188454041)
      ·
        refine ⟨53165811467095110141340531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70887748622793480188454041 53165811467095110141340531)
        ·
          refine ⟨79748717200642665212010797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53165811467095110141340531 79748717200642665212010797)
          ·
            refine ⟨29905768950240999454504049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79748717200642665212010797 29905768950240999454504049)
            ·
              refine ⟨22429326712680749590878037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29905768950240999454504049 22429326712680749590878037)
              ·
                refine ⟨131421836207113767134051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22429326712680749590878037 131421836207113767134051)
                ·
                  rfl

theorem cell21_1727616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_1727616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727616 prefixEnd_1727616 := by exact prefixLift 1727616
  have htrace : WordTrace (prefixWord ++ tailWord_1727616) baseStart_1727616 baseEnd_1727616 := by
    simpa [prefixWord, tailWord_1727616, baseEnd_1727616] using wordTrace_append hprefix tailTrace_1727616
  have hstable : (prefixWord ++ tailWord_1727616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727616).length < 2 ^ (prefixWord ++ tailWord_1727616).sum := by decide
  have hdescent : baseEnd_1727616 < baseStart_1727616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727698 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1727698 : Nat := 118140960795 + 1727698 * 2 ^ 59
def prefixEnd_1727698 : Nat := 4983230072969 + 3 ^ 40 * 1727698 * 2
def baseEnd_1727698 : Nat := 394284222138527381035319

theorem tailTrace_1727698 : CollatzResearch.WordTrace tailWord_1727698 prefixEnd_1727698 394284222138527381035319 := by
  unfold tailWord_1727698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15753580723713172042999937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42009548596568458781333165 15753580723713172042999937)
  ·
    refine ⟨11815185542784879032249953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15753580723713172042999937 11815185542784879032249953)
    ·
      refine ⟨8861389157088659274187465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815185542784879032249953 8861389157088659274187465)
      ·
        refine ⟨6646041867816494455640599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8861389157088659274187465 6646041867816494455640599)
        ·
          refine ⟨9969062801724741683460899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646041867816494455640599 9969062801724741683460899)
          ·
            refine ⟨14953594202587112525191349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969062801724741683460899 14953594202587112525191349)
            ·
              refine ⟨1401899456492541799236689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14953594202587112525191349 1401899456492541799236689)
              ·
                refine ⟨1051424592369406349427517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401899456492541799236689 1051424592369406349427517)
                ·
                  refine ⟨394284222138527381035319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051424592369406349427517 394284222138527381035319)
                  ·
                    rfl

theorem cell21_1727698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1727698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727698 prefixEnd_1727698 := by exact prefixLift 1727698
  have htrace : WordTrace (prefixWord ++ tailWord_1727698) baseStart_1727698 baseEnd_1727698 := by
    simpa [prefixWord, tailWord_1727698, baseEnd_1727698] using wordTrace_append hprefix tailTrace_1727698
  have hstable : (prefixWord ++ tailWord_1727698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727698).length < 2 ^ (prefixWord ++ tailWord_1727698).sum := by decide
  have hdescent : baseEnd_1727698 < baseStart_1727698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727712 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_1727712 : Nat := 118140960795 + 1727712 * 2 ^ 59
def prefixEnd_1727712 : Nat := 4983230072969 + 3 ^ 40 * 1727712 * 2
def baseEnd_1727712 : Nat := 394287417129266467801957

theorem tailTrace_1727712 : CollatzResearch.WordTrace tailWord_1727712 prefixEnd_1727712 394287417129266467801957 := by
  unfold tailWord_1727712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507416758400984281504695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42009889011201312375339593 31507416758400984281504695)
  ·
    refine ⟨47261125137601476422257043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31507416758400984281504695 47261125137601476422257043)
    ·
      refine ⟨70891687706402214633385565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47261125137601476422257043 70891687706402214633385565)
      ·
        refine ⟨26584382889900830487519587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70891687706402214633385565 26584382889900830487519587)
        ·
          refine ⟨39876574334851245731279381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26584382889900830487519587 39876574334851245731279381)
          ·
            refine ⟨1869214421946152143653721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39876574334851245731279381 1869214421946152143653721)
            ·
              refine ⟨1401910816459614107740291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869214421946152143653721 1401910816459614107740291)
              ·
                refine ⟨2102866224689421161610437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401910816459614107740291 2102866224689421161610437)
                ·
                  refine ⟨394287417129266467801957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102866224689421161610437 394287417129266467801957)
                  ·
                    rfl

theorem cell21_1727712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_1727712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727712 prefixEnd_1727712 := by exact prefixLift 1727712
  have htrace : WordTrace (prefixWord ++ tailWord_1727712) baseStart_1727712 baseEnd_1727712 := by
    simpa [prefixWord, tailWord_1727712, baseEnd_1727712] using wordTrace_append hprefix tailTrace_1727712
  have hstable : (prefixWord ++ tailWord_1727712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727712).length < 2 ^ (prefixWord ++ tailWord_1727712).sum := by decide
  have hdescent : baseEnd_1727712 < baseStart_1727712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727774 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1727774 : Nat := 118140960795 + 1727774 * 2 ^ 59
def prefixEnd_1727774 : Nat := 4983230072969 + 3 ^ 40 * 1727774 * 2
def baseEnd_1727774 : Nat := 394301566373968137768497

theorem tailTrace_1727774 : CollatzResearch.WordTrace tailWord_1727774 prefixEnd_1727774 394301566373968137768497 := by
  unfold tailWord_1727774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877136855322169143970797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42011396561718235434510917 7877136855322169143970797)
  ·
    refine ⟨2953926320745813428989049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7877136855322169143970797 2953926320745813428989049)
    ·
      refine ⟨2215444740559360071741787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953926320745813428989049 2215444740559360071741787)
      ·
        refine ⟨3323167110839040107612681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215444740559360071741787 3323167110839040107612681)
        ·
          refine ⟨2492375333129280080709511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323167110839040107612681 2492375333129280080709511)
          ·
            refine ⟨3738562999693920121064267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492375333129280080709511 3738562999693920121064267)
            ·
              refine ⟨5607844499540880181596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738562999693920121064267 5607844499540880181596401)
              ·
                refine ⟨4205883374655660136197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607844499540880181596401 4205883374655660136197301)
                ·
                  refine ⟨394301566373968137768497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205883374655660136197301 394301566373968137768497)
                  ·
                    rfl

theorem cell21_1727774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1727774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727774 prefixEnd_1727774 := by exact prefixLift 1727774
  have htrace : WordTrace (prefixWord ++ tailWord_1727774) baseStart_1727774 baseEnd_1727774 := by
    simpa [prefixWord, tailWord_1727774, baseEnd_1727774] using wordTrace_append hprefix tailTrace_1727774
  have hstable : (prefixWord ++ tailWord_1727774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727774).length < 2 ^ (prefixWord ++ tailWord_1727774).sum := by decide
  have hdescent : baseEnd_1727774 < baseStart_1727774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727805 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1727805 : Nat := 118140960795 + 1727805 * 2 ^ 59
def prefixEnd_1727805 : Nat := 4983230072969 + 3 ^ 40 * 1727805 * 2
def baseEnd_1727805 : Nat := 394308640996318972751767

theorem tailTrace_1727805 : CollatzResearch.WordTrace tailWord_1727805 prefixEnd_1727805 394308640996318972751767 := by
  unfold tailWord_1727805
  simp only [CollatzResearch.WordTrace]
  refine ⟨63018225505465045446144869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42012150336976696964096579 63018225505465045446144869)
  ·
    refine ⟨11815917282274696021152163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63018225505465045446144869 11815917282274696021152163)
    ·
      refine ⟨17723875923412044031728245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11815917282274696021152163 17723875923412044031728245)
      ·
        refine ⟨1661613367819879127974523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17723875923412044031728245 1661613367819879127974523)
        ·
          refine ⟨2492420051729818691961785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661613367819879127974523 2492420051729818691961785)
          ·
            refine ⟨1869315038797364018971339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492420051729818691961785 1869315038797364018971339)
            ·
              refine ⟨2803972558196046028457009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869315038797364018971339 2803972558196046028457009)
              ·
                refine ⟨2102979418647034521342757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803972558196046028457009 2102979418647034521342757)
                ·
                  refine ⟨394308640996318972751767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102979418647034521342757 394308640996318972751767)
                  ·
                    rfl

theorem cell21_1727805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1727805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727805 prefixEnd_1727805 := by exact prefixLift 1727805
  have htrace : WordTrace (prefixWord ++ tailWord_1727805) baseStart_1727805 baseEnd_1727805 := by
    simpa [prefixWord, tailWord_1727805, baseEnd_1727805] using wordTrace_append hprefix tailTrace_1727805
  have hstable : (prefixWord ++ tailWord_1727805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727805).length < 2 ^ (prefixWord ++ tailWord_1727805).sum := by decide
  have hdescent : baseEnd_1727805 < baseStart_1727805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727881 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 4]
def baseStart_1727881 : Nat := 118140960795 + 1727881 * 2 ^ 59
def prefixEnd_1727881 : Nat := 4983230072969 + 3 ^ 40 * 1727881 * 2
def baseEnd_1727881 : Nat := 394325985231759729484945

theorem tailTrace_1727881 : CollatzResearch.WordTrace tailWord_1727881 prefixEnd_1727881 394325985231759729484945 := by
  unfold tailWord_1727881
  simp only [CollatzResearch.WordTrace]
  refine ⟨63020997453189710425911497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42013998302126473617274331 63020997453189710425911497)
  ·
    refine ⟨47265748089892282819433623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63020997453189710425911497 47265748089892282819433623)
    ·
      refine ⟨70898622134838424229150435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47265748089892282819433623 70898622134838424229150435)
      ·
        refine ⟨106347933202257636343725653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70898622134838424229150435 106347933202257636343725653)
        ·
          refine ⟨1246264842213956675903035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 106347933202257636343725653 1246264842213956675903035)
          ·
            refine ⟨1869397263320935013854553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246264842213956675903035 1869397263320935013854553)
            ·
              refine ⟨1402047947490701260390915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869397263320935013854553 1402047947490701260390915)
              ·
                refine ⟨2103071921236051890586373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402047947490701260390915 2103071921236051890586373)
                ·
                  refine ⟨394325985231759729484945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103071921236051890586373 394325985231759729484945)
                  ·
                    rfl

theorem cell21_1727881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_1727881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727881 prefixEnd_1727881 := by exact prefixLift 1727881
  have htrace : WordTrace (prefixWord ++ tailWord_1727881) baseStart_1727881 baseEnd_1727881 := by
    simpa [prefixWord, tailWord_1727881, baseEnd_1727881] using wordTrace_append hprefix tailTrace_1727881
  have hstable : (prefixWord ++ tailWord_1727881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727881).length < 2 ^ (prefixWord ++ tailWord_1727881).sum := by decide
  have hdescent : baseEnd_1727881 < baseStart_1727881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727982 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1727982 : Nat := 118140960795 + 1727982 * 2 ^ 59
def prefixEnd_1727982 : Nat := 4983230072969 + 3 ^ 40 * 1727982 * 2
def baseEnd_1727982 : Nat := 394349034807805998301405

theorem tailTrace_1727982 : CollatzResearch.WordTrace tailWord_1727982 prefixEnd_1727982 394349034807805998301405 := by
  unfold tailWord_1727982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878085153227975584417275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42016454150549203116892133 7878085153227975584417275)
  ·
    refine ⟨11817127729841963376625913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878085153227975584417275 11817127729841963376625913)
    ·
      refine ⟨8862845797381472532469435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11817127729841963376625913 8862845797381472532469435)
      ·
        refine ⟨13294268696072208798704153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862845797381472532469435 13294268696072208798704153)
        ·
          refine ⟨9970701522054156599028115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13294268696072208798704153 9970701522054156599028115)
          ·
            refine ⟨14956052283081234898542173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970701522054156599028115 14956052283081234898542173)
            ·
              refine ⟨5608519606155463086953315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14956052283081234898542173 5608519606155463086953315)
              ·
                refine ⟨8412779409233194630429973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608519606155463086953315 8412779409233194630429973)
                ·
                  refine ⟨394349034807805998301405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8412779409233194630429973 394349034807805998301405)
                  ·
                    rfl

theorem cell21_1727982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1727982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1727982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1727982 prefixEnd_1727982 := by exact prefixLift 1727982
  have htrace : WordTrace (prefixWord ++ tailWord_1727982) baseStart_1727982 baseEnd_1727982 := by
    simpa [prefixWord, tailWord_1727982, baseEnd_1727982] using wordTrace_append hprefix tailTrace_1727982
  have hstable : (prefixWord ++ tailWord_1727982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727982).length < 2 ^ (prefixWord ++ tailWord_1727982).sum := by decide
  have hdescent : baseEnd_1727982 < baseStart_1727982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728058 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1728058 : Nat := 118140960795 + 1728058 * 2 ^ 59
def prefixEnd_1728058 : Nat := 4983230072969 + 3 ^ 40 * 1728058 * 2
def baseEnd_1728058 : Nat := 394366379043246755034583

theorem tailTrace_1728058 : CollatzResearch.WordTrace tailWord_1728058 prefixEnd_1728058 394366379043246755034583 := by
  unfold tailWord_1728058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756863293387117413776207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42018302115698979770069885 15756863293387117413776207)
  ·
    refine ⟨23635294940080676120664311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15756863293387117413776207 23635294940080676120664311)
    ·
      refine ⟨35452942410121014180996467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23635294940080676120664311 35452942410121014180996467)
      ·
        refine ⟨53179413615181521271494701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35452942410121014180996467 53179413615181521271494701)
        ·
          refine ⟨19942280105693070476810513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53179413615181521271494701 19942280105693070476810513)
          ·
            refine ⟨14956710079269802857607885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19942280105693070476810513 14956710079269802857607885)
            ·
              refine ⟨5608766279726176071602957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14956710079269802857607885 5608766279726176071602957)
              ·
                refine ⟨2103287354897316026851109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608766279726176071602957 2103287354897316026851109)
                ·
                  refine ⟨394366379043246755034583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103287354897316026851109 394366379043246755034583)
                  ·
                    rfl

theorem cell21_1728058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1728058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728058 prefixEnd_1728058 := by exact prefixLift 1728058
  have htrace : WordTrace (prefixWord ++ tailWord_1728058) baseStart_1728058 baseEnd_1728058 := by
    simpa [prefixWord, tailWord_1728058, baseEnd_1728058] using wordTrace_append hprefix tailTrace_1728058
  have hstable : (prefixWord ++ tailWord_1728058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728058).length < 2 ^ (prefixWord ++ tailWord_1728058).sum := by decide
  have hdescent : baseEnd_1728058 < baseStart_1728058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728151 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_1728151 : Nat := 118140960795 + 1728151 * 2 ^ 59
def prefixEnd_1728151 : Nat := 4983230072969 + 3 ^ 40 * 1728151 * 2
def baseEnd_1728151 : Nat := 394387602910299259984393

theorem tailTrace_1728151 : CollatzResearch.WordTrace tailWord_1728151 prefixEnd_1728151 394387602910299259984393 := by
  unfold tailWord_1728151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030845162211546538240307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42020563441474364358826871 63030845162211546538240307)
  ·
    refine ⟨94546267743317319807360461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63030845162211546538240307 94546267743317319807360461)
    ·
      refine ⟨35454850403743994927760173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94546267743317319807360461 35454850403743994927760173)
      ·
        refine ⟨13295568901403998097910065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35454850403743994927760173 13295568901403998097910065)
        ·
          refine ⟨9971676676052998573432549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13295568901403998097910065 9971676676052998573432549)
          ·
            refine ⟨1869689376759937232518603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9971676676052998573432549 1869689376759937232518603)
            ·
              refine ⟨2804534065139905848777905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869689376759937232518603 2804534065139905848777905)
              ·
                refine ⟨2103400548854929386583429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804534065139905848777905 2103400548854929386583429)
                ·
                  refine ⟨394387602910299259984393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103400548854929386583429 394387602910299259984393)
                  ·
                    rfl

theorem cell21_1728151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_1728151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728151 prefixEnd_1728151 := by exact prefixLift 1728151
  have htrace : WordTrace (prefixWord ++ tailWord_1728151) baseStart_1728151 baseEnd_1728151 := by
    simpa [prefixWord, tailWord_1728151, baseEnd_1728151] using wordTrace_append hprefix tailTrace_1728151
  have hstable : (prefixWord ++ tailWord_1728151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728151).length < 2 ^ (prefixWord ++ tailWord_1728151).sum := by decide
  have hdescent : baseEnd_1728151 < baseStart_1728151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728182 : List Nat := [5, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1728182 : Nat := 118140960795 + 1728182 * 2 ^ 59
def prefixEnd_1728182 : Nat := 4983230072969 + 3 ^ 40 * 1728182 * 2
def baseEnd_1728182 : Nat := 131464892510883364989221

theorem tailTrace_1728182 : CollatzResearch.WordTrace tailWord_1728182 prefixEnd_1728182 131464892510883364989221 := by
  unfold tailWord_1728182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939498489068702427038675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42021317216732825888412533 3939498489068702427038675)
  ·
    refine ⟨5909247733603053640558013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3939498489068702427038675 5909247733603053640558013)
    ·
      refine ⟨2215967900101145115209255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5909247733603053640558013 2215967900101145115209255)
      ·
        refine ⟨3323951850151717672813883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215967900101145115209255 3323951850151717672813883)
        ·
          refine ⟨4985927775227576509220825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323951850151717672813883 4985927775227576509220825)
          ·
            refine ⟨3739445831420682381915619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4985927775227576509220825 3739445831420682381915619)
            ·
              refine ⟨5609168747131023572873429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739445831420682381915619 5609168747131023572873429)
              ·
                refine ⟨131464892510883364989221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5609168747131023572873429 131464892510883364989221)
                ·
                  rfl

theorem cell21_1728182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1728182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728182 prefixEnd_1728182 := by exact prefixLift 1728182
  have htrace : WordTrace (prefixWord ++ tailWord_1728182) baseStart_1728182 baseEnd_1728182 := by
    simpa [prefixWord, tailWord_1728182, baseEnd_1728182] using wordTrace_append hprefix tailTrace_1728182
  have hstable : (prefixWord ++ tailWord_1728182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728182).length < 2 ^ (prefixWord ++ tailWord_1728182).sum := by decide
  have hdescent : baseEnd_1728182 < baseStart_1728182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728210 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1728210 : Nat := 118140960795 + 1728210 * 2 ^ 59
def prefixEnd_1728210 : Nat := 4983230072969 + 3 ^ 40 * 1728210 * 2
def baseEnd_1728210 : Nat := 394401067514128268500939

theorem tailTrace_1728210 : CollatzResearch.WordTrace tailWord_1728210 prefixEnd_1728210 394401067514128268500939 := by
  unfold tailWord_1728210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758249267249449903659521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42021998045998533076425389 15758249267249449903659521)
  ·
    refine ⟨11818686950437087427744641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15758249267249449903659521 11818686950437087427744641)
    ·
      refine ⟨8864015212827815570808481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11818686950437087427744641 8864015212827815570808481)
      ·
        refine ⟨6648011409620861678106361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8864015212827815570808481 6648011409620861678106361)
        ·
          refine ⟨4986008557215646258579771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648011409620861678106361 4986008557215646258579771)
          ·
            refine ⟨7479012835823469387869657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986008557215646258579771 7479012835823469387869657)
            ·
              refine ⟨5609259626867602040902243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7479012835823469387869657 5609259626867602040902243)
              ·
                refine ⟨8413889440301403061353365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609259626867602040902243 8413889440301403061353365)
                ·
                  refine ⟨394401067514128268500939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8413889440301403061353365 394401067514128268500939)
                  ·
                    rfl

theorem cell21_1728210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1728210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728210 prefixEnd_1728210 := by exact prefixLift 1728210
  have htrace : WordTrace (prefixWord ++ tailWord_1728210) baseStart_1728210 baseEnd_1728210 := by
    simpa [prefixWord, tailWord_1728210, baseEnd_1728210] using wordTrace_append hprefix tailTrace_1728210
  have hstable : (prefixWord ++ tailWord_1728210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728210).length < 2 ^ (prefixWord ++ tailWord_1728210).sum := by decide
  have hdescent : baseEnd_1728210 < baseStart_1728210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728227 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_1728227 : Nat := 118140960795 + 1728227 * 2 ^ 59
def prefixEnd_1728227 : Nat := 4983230072969 + 3 ^ 40 * 1728227 * 2
def baseEnd_1728227 : Nat := 394404947145740016717571

theorem tailTrace_1728227 : CollatzResearch.WordTrace tailWord_1728227 prefixEnd_1728227 394404947145740016717571 := by
  unfold tailWord_1728227
  simp only [CollatzResearch.WordTrace]
  refine ⟨63033617109936211518006935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42022411406624141012004623 63033617109936211518006935)
  ·
    refine ⟨94550425664904317277010403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63033617109936211518006935 94550425664904317277010403)
    ·
      refine ⟨141825638497356475915515605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94550425664904317277010403 141825638497356475915515605)
      ·
        refine ⟨3324038402281792404269897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 141825638497356475915515605 3324038402281792404269897)
        ·
          refine ⟨2493028801711344303202423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324038402281792404269897 2493028801711344303202423)
          ·
            refine ⟨3739543202567016454803635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493028801711344303202423 3739543202567016454803635)
            ·
              refine ⟨5609314803850524682205453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739543202567016454803635 5609314803850524682205453)
              ·
                refine ⟨2103493051443946755827045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5609314803850524682205453 2103493051443946755827045)
                ·
                  refine ⟨394404947145740016717571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103493051443946755827045 394404947145740016717571)
                  ·
                    rfl

theorem cell21_1728227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_1728227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728227 prefixEnd_1728227 := by exact prefixLift 1728227
  have htrace : WordTrace (prefixWord ++ tailWord_1728227) baseStart_1728227 baseEnd_1728227 := by
    simpa [prefixWord, tailWord_1728227, baseEnd_1728227] using wordTrace_append hprefix tailTrace_1728227
  have hstable : (prefixWord ++ tailWord_1728227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728227).length < 2 ^ (prefixWord ++ tailWord_1728227).sum := by decide
  have hdescent : baseEnd_1728227 < baseStart_1728227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728469 : List Nat := [1, 3, 2, 3, 2, 2, 3, 5]
def baseStart_1728469 : Nat := 118140960795 + 1728469 * 2 ^ 59
def prefixEnd_1728469 : Nat := 4983230072969 + 3 ^ 40 * 1728469 * 2
def baseEnd_1728469 : Nat := 131486724947600457894581

theorem tailTrace_1728469 : CollatzResearch.WordTrace tailWord_1728469 prefixEnd_1728469 131486724947600457894581 := by
  unfold tailWord_1728469
  simp only [CollatzResearch.WordTrace]
  refine ⟨63042443575059486848316461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42028295716706324565544307 63042443575059486848316461)
  ·
    refine ⟨23640916340647307568118673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63042443575059486848316461 23640916340647307568118673)
    ·
      refine ⟨17730687255485480676089005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23640916340647307568118673 17730687255485480676089005)
      ·
        refine ⟨6649007720807055253533377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17730687255485480676089005 6649007720807055253533377)
        ·
          refine ⟨4986755790605291440150033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6649007720807055253533377 4986755790605291440150033)
          ·
            refine ⟨3740066842953968580112525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986755790605291440150033 3740066842953968580112525)
            ·
              refine ⟨1402525066107738217542197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740066842953968580112525 1402525066107738217542197)
              ·
                refine ⟨131486724947600457894581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1402525066107738217542197 131486724947600457894581)
                ·
                  rfl

theorem cell21_1728469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].length) (baseStart_1728469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728469 prefixEnd_1728469 := by exact prefixLift 1728469
  have htrace : WordTrace (prefixWord ++ tailWord_1728469) baseStart_1728469 baseEnd_1728469 := by
    simpa [prefixWord, tailWord_1728469, baseEnd_1728469] using wordTrace_append hprefix tailTrace_1728469
  have hstable : (prefixWord ++ tailWord_1728469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728469).length < 2 ^ (prefixWord ++ tailWord_1728469).sum := by decide
  have hdescent : baseEnd_1728469 < baseStart_1728469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728545 : List Nat := [1, 2, 3, 2, 5, 1, 7]
def baseStart_1728545 : Nat := 118140960795 + 1728545 * 2 ^ 59
def prefixEnd_1728545 : Nat := 4983230072969 + 3 ^ 40 * 1728545 * 2
def baseEnd_1728545 : Nat := 43830835453138014490769

theorem tailTrace_1728545 : CollatzResearch.WordTrace tailWord_1728545 prefixEnd_1728545 43830835453138014490769 := by
  unfold tailWord_1728545
  simp only [CollatzResearch.WordTrace]
  refine ⟨63045215522784151828083089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42030143681856101218722059 63045215522784151828083089)
  ·
    refine ⟨47283911642088113871062317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63045215522784151828083089 47283911642088113871062317)
    ·
      refine ⟨17731466865783042701648369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47283911642088113871062317 17731466865783042701648369)
      ·
        refine ⟨13298600149337282026236277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17731466865783042701648369 13298600149337282026236277)
        ·
          refine ⟨1246743764000370189959651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13298600149337282026236277 1246743764000370189959651)
          ·
            refine ⟨1870115646000555284939477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246743764000370189959651 1870115646000555284939477)
            ·
              refine ⟨43830835453138014490769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1870115646000555284939477 43830835453138014490769)
              ·
                rfl

theorem cell21_1728545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 7].length) (baseStart_1728545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728545 prefixEnd_1728545 := by exact prefixLift 1728545
  have htrace : WordTrace (prefixWord ++ tailWord_1728545) baseStart_1728545 baseEnd_1728545 := by
    simpa [prefixWord, tailWord_1728545, baseEnd_1728545] using wordTrace_append hprefix tailTrace_1728545
  have hstable : (prefixWord ++ tailWord_1728545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728545).length < 2 ^ (prefixWord ++ tailWord_1728545).sum := by decide
  have hdescent : baseEnd_1728545 < baseStart_1728545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728632 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_1728632 : Nat := 118140960795 + 1728632 * 2 ^ 59
def prefixEnd_1728632 : Nat := 4983230072969 + 3 ^ 40 * 1728632 * 2
def baseEnd_1728632 : Nat := 394497373663549312466743

theorem tailTrace_1728632 : CollatzResearch.WordTrace tailWord_1728632 prefixEnd_1728632 394497373663549312466743 := by
  unfold tailWord_1728632
  simp only [CollatzResearch.WordTrace]
  refine ⟨31524194336734482843250075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42032259115645977124333433 31524194336734482843250075)
  ·
    refine ⟨47286291505101724264875113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31524194336734482843250075 47286291505101724264875113)
    ·
      refine ⟨35464718628826293198656335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47286291505101724264875113 35464718628826293198656335)
      ·
        refine ⟨53197077943239439797984503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35464718628826293198656335 53197077943239439797984503)
        ·
          refine ⟨79795616914859159696976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53197077943239439797984503 79795616914859159696976755)
          ·
            refine ⟨119693425372288739545465133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79795616914859159696976755 119693425372288739545465133)
            ·
              refine ⟨44885034514608277329549425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119693425372288739545465133 44885034514608277329549425)
              ·
                refine ⟨33663775885956207997162069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44885034514608277329549425 33663775885956207997162069)
                ·
                  refine ⟨394497373663549312466743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33663775885956207997162069 394497373663549312466743)
                  ·
                    rfl

theorem cell21_1728632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_1728632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728632 prefixEnd_1728632 := by exact prefixLift 1728632
  have htrace : WordTrace (prefixWord ++ tailWord_1728632) baseStart_1728632 baseEnd_1728632 := by
    simpa [prefixWord, tailWord_1728632, baseEnd_1728632] using wordTrace_append hprefix tailTrace_1728632
  have hstable : (prefixWord ++ tailWord_1728632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728632).length < 2 ^ (prefixWord ++ tailWord_1728632).sum := by decide
  have hdescent : baseEnd_1728632 < baseStart_1728632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728666 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1728666 : Nat := 118140960795 + 1728666 * 2 ^ 59
def prefixEnd_1728666 : Nat := 4983230072969 + 3 ^ 40 * 1728666 * 2
def baseEnd_1728666 : Nat := 394505132926772808900007

theorem tailTrace_1728666 : CollatzResearch.WordTrace tailWord_1728666 prefixEnd_1728666 394505132926772808900007 := by
  unfold tailWord_1728666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762407188836447373309463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42033085836897192995491901 15762407188836447373309463)
  ·
    refine ⟨23643610783254671059964195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15762407188836447373309463 23643610783254671059964195)
    ·
      refine ⟨35465416174882006589946293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643610783254671059964195 35465416174882006589946293)
      ·
        refine ⟨3324882766395188117807465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35465416174882006589946293 3324882766395188117807465)
        ·
          refine ⟨2493662074796391088355599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324882766395188117807465 2493662074796391088355599)
          ·
            refine ⟨3740493112194586632533399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493662074796391088355599 3740493112194586632533399)
            ·
              refine ⟨5610739668291879948800099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740493112194586632533399 5610739668291879948800099)
              ·
                refine ⟨8416109502437819923200149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610739668291879948800099 8416109502437819923200149)
                ·
                  refine ⟨394505132926772808900007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8416109502437819923200149 394505132926772808900007)
                  ·
                    rfl

theorem cell21_1728666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1728666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728666 prefixEnd_1728666 := by exact prefixLift 1728666
  have htrace : WordTrace (prefixWord ++ tailWord_1728666) baseStart_1728666 baseEnd_1728666 := by
    simpa [prefixWord, tailWord_1728666, baseEnd_1728666] using wordTrace_append hprefix tailTrace_1728666
  have hstable : (prefixWord ++ tailWord_1728666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728666).length < 2 ^ (prefixWord ++ tailWord_1728666).sum := by decide
  have hdescent : baseEnd_1728666 < baseStart_1728666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728801 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_1728801 : Nat := 118140960795 + 1728801 * 2 ^ 59
def prefixEnd_1728801 : Nat := 4983230072969 + 3 ^ 40 * 1728801 * 2
def baseEnd_1728801 : Nat := 394535941766042574149731

theorem tailTrace_1728801 : CollatzResearch.WordTrace tailWord_1728801 prefixEnd_1728801 394535941766042574149731 := by
  unfold tailWord_1728801
  simp only [CollatzResearch.WordTrace]
  refine ⟨63054552609856707549402257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42036368406571138366268171 63054552609856707549402257)
  ·
    refine ⟨47290914457392530662051693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63054552609856707549402257 47290914457392530662051693)
    ·
      refine ⟨17734092921522198998269385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47290914457392530662051693 17734092921522198998269385)
      ·
        refine ⟨13300569691141649248702039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17734092921522198998269385 13300569691141649248702039)
        ·
          refine ⟨19950854536712473873053059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13300569691141649248702039 19950854536712473873053059)
          ·
            refine ⟨29926281805068710809579589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19950854536712473873053059 29926281805068710809579589)
            ·
              refine ⟨5611177838450383276796173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29926281805068710809579589 5611177838450383276796173)
              ·
                refine ⟨2104191689418893728798565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5611177838450383276796173 2104191689418893728798565)
                ·
                  refine ⟨394535941766042574149731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104191689418893728798565 394535941766042574149731)
                  ·
                    rfl

theorem cell21_1728801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_1728801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728801 prefixEnd_1728801 := by exact prefixLift 1728801
  have htrace : WordTrace (prefixWord ++ tailWord_1728801) baseStart_1728801 baseEnd_1728801 := by
    simpa [prefixWord, tailWord_1728801, baseEnd_1728801] using wordTrace_append hprefix tailTrace_1728801
  have hstable : (prefixWord ++ tailWord_1728801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728801).length < 2 ^ (prefixWord ++ tailWord_1728801).sum := by decide
  have hdescent : baseEnd_1728801 < baseStart_1728801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728807 : List Nat := [1, 1, 8, 1, 1, 1, 3, 5]
def baseStart_1728807 : Nat := 118140960795 + 1728807 * 2 ^ 59
def prefixEnd_1728807 : Nat := 4983230072969 + 3 ^ 40 * 1728807 * 2
def baseEnd_1728807 : Nat := 131512437015929299016573

theorem tailTrace_1728807 : CollatzResearch.WordTrace tailWord_1728807 prefixEnd_1728807 131512437015929299016573 := by
  unfold tailWord_1728807
  simp only [CollatzResearch.WordTrace]
  refine ⟨63054771447834970574120675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42036514298556647049413783 63054771447834970574120675)
  ·
    refine ⟨94582157171752455861181013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63054771447834970574120675 94582157171752455861181013)
    ·
      refine ⟨1108384654356474092123215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 94582157171752455861181013 1108384654356474092123215)
      ·
        refine ⟨1662576981534711138184823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108384654356474092123215 1662576981534711138184823)
        ·
          refine ⟨2493865472302066707277235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662576981534711138184823 2493865472302066707277235)
          ·
            refine ⟨3740798208453100060915853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493865472302066707277235 3740798208453100060915853)
            ·
              refine ⟨1402799328169912522843445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740798208453100060915853 1402799328169912522843445)
              ·
                refine ⟨131512437015929299016573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1402799328169912522843445 131512437015929299016573)
                ·
                  rfl

theorem cell21_1728807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].length) (baseStart_1728807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728807 prefixEnd_1728807 := by exact prefixLift 1728807
  have htrace : WordTrace (prefixWord ++ tailWord_1728807) baseStart_1728807 baseEnd_1728807 := by
    simpa [prefixWord, tailWord_1728807, baseEnd_1728807] using wordTrace_append hprefix tailTrace_1728807
  have hstable : (prefixWord ++ tailWord_1728807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728807).length < 2 ^ (prefixWord ++ tailWord_1728807).sum := by decide
  have hdescent : baseEnd_1728807 < baseStart_1728807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728880 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_1728880 : Nat := 118140960795 + 1728880 * 2 ^ 59
def prefixEnd_1728880 : Nat := 4983230072969 + 3 ^ 40 * 1728880 * 2
def baseEnd_1728880 : Nat := 394553970642355992332903

theorem tailTrace_1728880 : CollatzResearch.WordTrace tailWord_1728880 prefixEnd_1728880 394553970642355992332903 := by
  unfold tailWord_1728880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31528716988285252020764047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42038289317713669361018729 31528716988285252020764047)
  ·
    refine ⟨47293075482427878031146071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31528716988285252020764047 47293075482427878031146071)
    ·
      refine ⟨70939613223641817046719107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47293075482427878031146071 70939613223641817046719107)
      ·
        refine ⟨106409419835462725570078661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70939613223641817046719107 106409419835462725570078661)
        ·
          refine ⟨19951766219149261044389749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106409419835462725570078661 19951766219149261044389749)
          ·
            refine ⟨1870478083045243222911539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19951766219149261044389749 1870478083045243222911539)
            ·
              refine ⟨2805717124567864834367309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870478083045243222911539 2805717124567864834367309)
              ·
                refine ⟨1052143921712949312887741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805717124567864834367309 1052143921712949312887741)
                ·
                  refine ⟨394553970642355992332903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052143921712949312887741 394553970642355992332903)
                  ·
                    rfl

theorem cell21_1728880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_1728880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728880 prefixEnd_1728880 := by exact prefixLift 1728880
  have htrace : WordTrace (prefixWord ++ tailWord_1728880) baseStart_1728880 baseEnd_1728880 := by
    simpa [prefixWord, tailWord_1728880, baseEnd_1728880] using wordTrace_append hprefix tailTrace_1728880
  have hstable : (prefixWord ++ tailWord_1728880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728880).length < 2 ^ (prefixWord ++ tailWord_1728880).sum := by decide
  have hdescent : baseEnd_1728880 < baseStart_1728880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728891 : List Nat := [1, 1, 1, 1, 1, 9, 7]
def baseStart_1728891 : Nat := 118140960795 + 1728891 * 2 ^ 59
def prefixEnd_1728891 : Nat := 4983230072969 + 3 ^ 40 * 1728891 * 2
def baseEnd_1728891 : Nat := 43839608999135824183283

theorem tailTrace_1728891 : CollatzResearch.WordTrace tailWord_1728891 prefixEnd_1728891 43839608999135824183283 := by
  unfold tailWord_1728891
  simp only [CollatzResearch.WordTrace]
  refine ⟨63057835179530652920178527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42038556786353768613452351 63057835179530652920178527)
  ·
    refine ⟨94586752769295979380267791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63057835179530652920178527 94586752769295979380267791)
    ·
      refine ⟨141880129153943969070401687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94586752769295979380267791 141880129153943969070401687)
      ·
        refine ⟨212820193730915953605602531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141880129153943969070401687 212820193730915953605602531)
        ·
          refine ⟨319230290596373930408403797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212820193730915953605602531 319230290596373930408403797)
          ·
            refine ⟨1870489983963128498486741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 319230290596373930408403797 1870489983963128498486741)
            ·
              refine ⟨43839608999135824183283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1870489983963128498486741 43839608999135824183283)
              ·
                rfl

theorem cell21_1728891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 7].length) (baseStart_1728891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728891 prefixEnd_1728891 := by exact prefixLift 1728891
  have htrace : WordTrace (prefixWord ++ tailWord_1728891) baseStart_1728891 baseEnd_1728891 := by
    simpa [prefixWord, tailWord_1728891, baseEnd_1728891] using wordTrace_append hprefix tailTrace_1728891
  have hstable : (prefixWord ++ tailWord_1728891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728891).length < 2 ^ (prefixWord ++ tailWord_1728891).sum := by decide
  have hdescent : baseEnd_1728891 < baseStart_1728891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728897 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 3]
def baseStart_1728897 : Nat := 118140960795 + 1728897 * 2 ^ 59
def prefixEnd_1728897 : Nat := 4983230072969 + 3 ^ 40 * 1728897 * 2
def baseEnd_1728897 : Nat := 394557850273967740549535

theorem tailTrace_1728897 : CollatzResearch.WordTrace tailWord_1728897 prefixEnd_1728897 394557850273967740549535 := by
  unfold tailWord_1728897
  simp only [CollatzResearch.WordTrace]
  refine ⟨63058054017508915944896945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42038702678339277296597963 63058054017508915944896945)
  ·
    refine ⟨47293540513131686958672709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63058054017508915944896945 47293540513131686958672709)
    ·
      refine ⟨8867538846212191304751133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47293540513131686958672709 8867538846212191304751133)
      ·
        refine ⟨3325327067329571739281675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8867538846212191304751133 3325327067329571739281675)
        ·
          refine ⟨4987990600994357608922513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325327067329571739281675 4987990600994357608922513)
          ·
            refine ⟨3740992950745768206691885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987990600994357608922513 3740992950745768206691885)
            ·
              refine ⟨1402872356529663077509457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740992950745768206691885 1402872356529663077509457)
              ·
                refine ⟨1052154267397247308132093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402872356529663077509457 1052154267397247308132093)
                ·
                  refine ⟨394557850273967740549535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052154267397247308132093 394557850273967740549535)
                  ·
                    rfl

theorem cell21_1728897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_1728897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728897 prefixEnd_1728897 := by exact prefixLift 1728897
  have htrace : WordTrace (prefixWord ++ tailWord_1728897) baseStart_1728897 baseEnd_1728897 := by
    simpa [prefixWord, tailWord_1728897, baseEnd_1728897] using wordTrace_append hprefix tailTrace_1728897
  have hstable : (prefixWord ++ tailWord_1728897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728897).length < 2 ^ (prefixWord ++ tailWord_1728897).sum := by decide
  have hdescent : baseEnd_1728897 < baseStart_1728897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728948 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1728948 : Nat := 118140960795 + 1728948 * 2 ^ 59
def prefixEnd_1728948 : Nat := 4983230072969 + 3 ^ 40 * 1728948 * 2
def baseEnd_1728948 : Nat := 394569489168802985199431

theorem tailTrace_1728948 : CollatzResearch.WordTrace tailWord_1728948 prefixEnd_1728948 394569489168802985199431 := by
  unfold tailWord_1728948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529957070162075827501749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42039942760216101103335665 31529957070162075827501749)
  ·
    refine ⟨2955933475327694608828289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31529957070162075827501749 2955933475327694608828289)
    ·
      refine ⟨2216950106495770956621217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2955933475327694608828289 2216950106495770956621217)
      ·
        refine ⟨1662712579871828217465913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216950106495770956621217 1662712579871828217465913)
        ·
          refine ⟨1247034434903871163099435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1662712579871828217465913 1247034434903871163099435)
          ·
            refine ⟨1870551652355806744649153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247034434903871163099435 1870551652355806744649153)
            ·
              refine ⟨1402913739266855058486865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870551652355806744649153 1402913739266855058486865)
              ·
                refine ⟨1052185304450141293865149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402913739266855058486865 1052185304450141293865149)
                ·
                  refine ⟨394569489168802985199431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052185304450141293865149 394569489168802985199431)
                  ·
                    rfl

theorem cell21_1728948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1728948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728948 prefixEnd_1728948 := by exact prefixLift 1728948
  have htrace : WordTrace (prefixWord ++ tailWord_1728948) baseStart_1728948 baseEnd_1728948 := by
    simpa [prefixWord, tailWord_1728948, baseEnd_1728948] using wordTrace_append hprefix tailTrace_1728948
  have hstable : (prefixWord ++ tailWord_1728948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728948).length < 2 ^ (prefixWord ++ tailWord_1728948).sum := by decide
  have hdescent : baseEnd_1728948 < baseStart_1728948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728953 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_1728953 : Nat := 118140960795 + 1728953 * 2 ^ 59
def prefixEnd_1728953 : Nat := 4983230072969 + 3 ^ 40 * 1728953 * 2
def baseEnd_1728953 : Nat := 394570630236924087616087

theorem tailTrace_1728953 : CollatzResearch.WordTrace tailWord_1728953 prefixEnd_1728953 394570630236924087616087 := by
  unfold tailWord_1728953
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060096505306037508935513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42040064336870691672623675 63060096505306037508935513)
  ·
    refine ⟨47295072378979528131701635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63060096505306037508935513 47295072378979528131701635)
    ·
      refine ⟨70942608568469292197552453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47295072378979528131701635 70942608568469292197552453)
      ·
        refine ⟨13301739106587992287041085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70942608568469292197552453 13301739106587992287041085)
        ·
          refine ⟨4988152164970497107640407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13301739106587992287041085 4988152164970497107640407)
          ·
            refine ⟨7482228247455745661460611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988152164970497107640407 7482228247455745661460611)
            ·
              refine ⟨11223342371183618492190917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482228247455745661460611 11223342371183618492190917)
              ·
                refine ⟨2104376694596928467285797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11223342371183618492190917 2104376694596928467285797)
                ·
                  refine ⟨394570630236924087616087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104376694596928467285797 394570630236924087616087)
                  ·
                    rfl

theorem cell21_1728953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_1728953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728953 prefixEnd_1728953 := by exact prefixLift 1728953
  have htrace : WordTrace (prefixWord ++ tailWord_1728953) baseStart_1728953 baseEnd_1728953 := by
    simpa [prefixWord, tailWord_1728953, baseEnd_1728953] using wordTrace_append hprefix tailTrace_1728953
  have hstable : (prefixWord ++ tailWord_1728953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728953).length < 2 ^ (prefixWord ++ tailWord_1728953).sum := by decide
  have hdescent : baseEnd_1728953 < baseStart_1728953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728956 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_1728956 : Nat := 118140960795 + 1728956 * 2 ^ 59
def prefixEnd_1728956 : Nat := 4983230072969 + 3 ^ 40 * 1728956 * 2
def baseEnd_1728956 : Nat := 394571314877796749066081

theorem tailTrace_1728956 : CollatzResearch.WordTrace tailWord_1728956 prefixEnd_1728956 394571314877796749066081 := by
  unfold tailWord_1728956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530102962147584510647361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42040137282863446014196481 31530102962147584510647361)
  ·
    refine ⟨23647577221610688382985521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31530102962147584510647361 23647577221610688382985521)
    ·
      refine ⟨17735682916208016287239141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23647577221610688382985521 17735682916208016287239141)
      ·
        refine ⟨3325440546789003053857339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17735682916208016287239141 3325440546789003053857339)
        ·
          refine ⟨4988160820183504580786009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325440546789003053857339 4988160820183504580786009)
          ·
            refine ⟨3741120615137628435589507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4988160820183504580786009 3741120615137628435589507)
            ·
              refine ⟨5611680922706442653384261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741120615137628435589507 5611680922706442653384261)
              ·
                refine ⟨1052190173007457997509549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5611680922706442653384261 1052190173007457997509549)
                ·
                  refine ⟨394571314877796749066081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052190173007457997509549 394571314877796749066081)
                  ·
                    rfl

theorem cell21_1728956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_1728956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728956 prefixEnd_1728956 := by exact prefixLift 1728956
  have htrace : WordTrace (prefixWord ++ tailWord_1728956) baseStart_1728956 baseEnd_1728956 := by
    simpa [prefixWord, tailWord_1728956, baseEnd_1728956] using wordTrace_append hprefix tailTrace_1728956
  have hstable : (prefixWord ++ tailWord_1728956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728956).length < 2 ^ (prefixWord ++ tailWord_1728956).sum := by decide
  have hdescent : baseEnd_1728956 < baseStart_1728956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728967 : List Nat := [1, 1, 4, 1, 1, 4, 3, 6]
def baseStart_1728967 : Nat := 118140960795 + 1728967 * 2 ^ 59
def prefixEnd_1728967 : Nat := 4983230072969 + 3 ^ 40 * 1728967 * 2
def baseEnd_1728967 : Nat := 131524608409221058127575

theorem tailTrace_1728967 : CollatzResearch.WordTrace tailWord_1728967 prefixEnd_1728967 131524608409221058127575 := by
  unfold tailWord_1728967
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060607127255317899945155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42040404751503545266630103 63060607127255317899945155)
  ·
    refine ⟨94590910690882976849917733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63060607127255317899945155 94590910690882976849917733)
    ·
      refine ⟨17735795754540558159359575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94590910690882976849917733 17735795754540558159359575)
      ·
        refine ⟨26603693631810837239039363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735795754540558159359575 26603693631810837239039363)
        ·
          refine ⟨39905540447716255858559045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26603693631810837239039363 39905540447716255858559045)
          ·
            refine ⟨7482288833946797973479821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39905540447716255858559045 7482288833946797973479821)
            ·
              refine ⟨2805858312730049240054933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7482288833946797973479821 2805858312730049240054933)
              ·
                refine ⟨131524608409221058127575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2805858312730049240054933 131524608409221058127575)
                ·
                  rfl

theorem cell21_1728967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_1728967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1728967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1728967 prefixEnd_1728967 := by exact prefixLift 1728967
  have htrace : WordTrace (prefixWord ++ tailWord_1728967) baseStart_1728967 baseEnd_1728967 := by
    simpa [prefixWord, tailWord_1728967, baseEnd_1728967] using wordTrace_append hprefix tailTrace_1728967
  have hstable : (prefixWord ++ tailWord_1728967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728967).length < 2 ^ (prefixWord ++ tailWord_1728967).sum := by decide
  have hdescent : baseEnd_1728967 < baseStart_1728967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729074 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1729074 : Nat := 118140960795 + 1729074 * 2 ^ 59
def prefixEnd_1729074 : Nat := 4983230072969 + 3 ^ 40 * 1729074 * 2
def baseEnd_1729074 : Nat := 394598244085454766099173

theorem tailTrace_1729074 : CollatzResearch.WordTrace tailWord_1729074 prefixEnd_1729074 394598244085454766099173 := by
  unfold tailWord_1729074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766127434466918793522569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42043006491911783449393517 15766127434466918793522569)
  ·
    refine ⟨11824595575850189095141927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15766127434466918793522569 11824595575850189095141927)
    ·
      refine ⟨17736893363775283642712891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824595575850189095141927 17736893363775283642712891)
      ·
        refine ⟨26605340045662925464069337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17736893363775283642712891 26605340045662925464069337)
        ·
          refine ⟨19954005034247194098052003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26605340045662925464069337 19954005034247194098052003)
          ·
            refine ⟨29931007551370791147078005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19954005034247194098052003 29931007551370791147078005)
            ·
              refine ⟨2806031957941011670038563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29931007551370791147078005 2806031957941011670038563)
              ·
                refine ⟨4209047936911517505057845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806031957941011670038563 4209047936911517505057845)
                ·
                  refine ⟨394598244085454766099173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4209047936911517505057845 394598244085454766099173)
                  ·
                    rfl

theorem cell21_1729074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1729074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729074 prefixEnd_1729074 := by exact prefixLift 1729074
  have htrace : WordTrace (prefixWord ++ tailWord_1729074) baseStart_1729074 baseEnd_1729074 := by
    simpa [prefixWord, tailWord_1729074, baseEnd_1729074] using wordTrace_append hprefix tailTrace_1729074
  have hstable : (prefixWord ++ tailWord_1729074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729074).length < 2 ^ (prefixWord ++ tailWord_1729074).sum := by decide
  have hdescent : baseEnd_1729074 < baseStart_1729074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729125 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 3]
def baseStart_1729125 : Nat := 118140960795 + 1729125 * 2 ^ 59
def prefixEnd_1729125 : Nat := 4983230072969 + 3 ^ 40 * 1729125 * 2
def baseEnd_1729125 : Nat := 394609882980290010749069

theorem tailTrace_1729125 : CollatzResearch.WordTrace tailWord_1729125 prefixEnd_1729125 394609882980290010749069 := by
  unfold tailWord_1729125
  simp only [CollatzResearch.WordTrace]
  refine ⟨63066369860682910884196829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42044246573788607256131219 63066369860682910884196829)
  ·
    refine ⟨23649888697756091581573811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63066369860682910884196829 23649888697756091581573811)
    ·
      refine ⟨35474833046634137372360717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23649888697756091581573811 35474833046634137372360717)
      ·
        refine ⟨13303062392487801514635269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35474833046634137372360717 13303062392487801514635269)
        ·
          refine ⟨2494324198591462783994113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13303062392487801514635269 2494324198591462783994113)
          ·
            refine ⟨1870743148943597087995585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494324198591462783994113 1870743148943597087995585)
            ·
              refine ⟨1403057361707697815996689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870743148943597087995585 1403057361707697815996689)
              ·
                refine ⟨1052293021280773361997517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403057361707697815996689 1052293021280773361997517)
                ·
                  refine ⟨394609882980290010749069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052293021280773361997517 394609882980290010749069)
                  ·
                    rfl

theorem cell21_1729125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_1729125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729125 prefixEnd_1729125 := by exact prefixLift 1729125
  have htrace : WordTrace (prefixWord ++ tailWord_1729125) baseStart_1729125 baseEnd_1729125 := by
    simpa [prefixWord, tailWord_1729125, baseEnd_1729125] using wordTrace_append hprefix tailTrace_1729125
  have hstable : (prefixWord ++ tailWord_1729125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729125).length < 2 ^ (prefixWord ++ tailWord_1729125).sum := by decide
  have hdescent : baseEnd_1729125 < baseStart_1729125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729136 : List Nat := [2, 1, 1, 1, 7, 2, 1, 6]
def baseStart_1729136 : Nat := 118140960795 + 1729136 * 2 ^ 59
def prefixEnd_1729136 : Nat := 4983230072969 + 3 ^ 40 * 1729136 * 2
def baseEnd_1729136 : Nat := 131537464443385478688571

theorem tailTrace_1729136 : CollatzResearch.WordTrace tailWord_1729136 prefixEnd_1729136 131537464443385478688571 := by
  unfold tailWord_1729136
  simp only [CollatzResearch.WordTrace]
  refine ⟨31533385531821529881423631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42044514042428706508564841 31533385531821529881423631)
  ·
    refine ⟨47300078297732294822135447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31533385531821529881423631 47300078297732294822135447)
    ·
      refine ⟨70950117446598442233203171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47300078297732294822135447 70950117446598442233203171)
      ·
        refine ⟨106425176169897663349804757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70950117446598442233203171 106425176169897663349804757)
        ·
          refine ⟨2494340066481976484761049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 106425176169897663349804757 2494340066481976484761049)
          ·
            refine ⟨1870755049861482363570787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494340066481976484761049 1870755049861482363570787)
            ·
              refine ⟨2806132574792223545356181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870755049861482363570787 2806132574792223545356181)
              ·
                refine ⟨131537464443385478688571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806132574792223545356181 131537464443385478688571)
                ·
                  rfl

theorem cell21_1729136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_1729136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729136 prefixEnd_1729136 := by exact prefixLift 1729136
  have htrace : WordTrace (prefixWord ++ tailWord_1729136) baseStart_1729136 baseEnd_1729136 := by
    simpa [prefixWord, tailWord_1729136, baseEnd_1729136] using wordTrace_append hprefix tailTrace_1729136
  have hstable : (prefixWord ++ tailWord_1729136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729136).length < 2 ^ (prefixWord ++ tailWord_1729136).sum := by decide
  have hdescent : baseEnd_1729136 < baseStart_1729136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729181 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1729181 : Nat := 118140960795 + 1729181 * 2 ^ 59
def prefixEnd_1729181 : Nat := 4983230072969 + 3 ^ 40 * 1729181 * 2
def baseEnd_1729181 : Nat := 394622662943246357815621

theorem tailTrace_1729181 : CollatzResearch.WordTrace tailWord_1729181 prefixEnd_1729181 394622662943246357815621 := by
  unfold tailWord_1729181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63068412348480032448235397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42045608232320021632156931 63068412348480032448235397)
  ·
    refine ⟨11825327315340006084044137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63068412348480032448235397 11825327315340006084044137)
    ·
      refine ⟨8868995486505004563033103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11825327315340006084044137 8868995486505004563033103)
      ·
        refine ⟨13303493229757506844549655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8868995486505004563033103 13303493229757506844549655)
        ·
          refine ⟨19955239844636260266824483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13303493229757506844549655 19955239844636260266824483)
          ·
            refine ⟨29932859766954390400236725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19955239844636260266824483 29932859766954390400236725)
            ·
              refine ⟨2806205603151974100022193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29932859766954390400236725 2806205603151974100022193)
              ·
                refine ⟨2104654202363980575016645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806205603151974100022193 2104654202363980575016645)
                ·
                  refine ⟨394622662943246357815621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104654202363980575016645 394622662943246357815621)
                  ·
                    rfl

theorem cell21_1729181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1729181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729181 prefixEnd_1729181 := by exact prefixLift 1729181
  have htrace : WordTrace (prefixWord ++ tailWord_1729181) baseStart_1729181 baseEnd_1729181 := by
    simpa [prefixWord, tailWord_1729181, baseEnd_1729181] using wordTrace_append hprefix tailTrace_1729181
  have hstable : (prefixWord ++ tailWord_1729181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729181).length < 2 ^ (prefixWord ++ tailWord_1729181).sum := by decide
  have hdescent : baseEnd_1729181 < baseStart_1729181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729229 : List Nat := [1, 6, 2, 1, 2, 2, 7]
def baseStart_1729229 : Nat := 118140960795 + 1729229 * 2 ^ 59
def prefixEnd_1729229 : Nat := 4983230072969 + 3 ^ 40 * 1729229 * 2
def baseEnd_1729229 : Nat := 43848179688578771223947

theorem tailTrace_1729229 : CollatzResearch.WordTrace tailWord_1729229 prefixEnd_1729229 43848179688578771223947 := by
  unfold tailWord_1729229
  simp only [CollatzResearch.WordTrace]
  refine ⟨63070163052306136645982741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42046775368204091097321827 63070163052306136645982741)
  ·
    refine ⟨2956413893076850155280441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63070163052306136645982741 2956413893076850155280441)
    ·
      refine ⟨2217310419807637616460331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956413893076850155280441 2217310419807637616460331)
      ·
        refine ⟨3325965629711456424690497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217310419807637616460331 3325965629711456424690497)
        ·
          refine ⟨2494474222283592318517873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325965629711456424690497 2494474222283592318517873)
          ·
            refine ⟨1870855666712694238888405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494474222283592318517873 1870855666712694238888405)
            ·
              refine ⟨43848179688578771223947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1870855666712694238888405 43848179688578771223947)
              ·
                rfl

theorem cell21_1729229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 7].length) (baseStart_1729229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729229 prefixEnd_1729229 := by exact prefixLift 1729229
  have htrace : WordTrace (prefixWord ++ tailWord_1729229) baseStart_1729229 baseEnd_1729229 := by
    simpa [prefixWord, tailWord_1729229, baseEnd_1729229] using wordTrace_append hprefix tailTrace_1729229
  have hstable : (prefixWord ++ tailWord_1729229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729229).length < 2 ^ (prefixWord ++ tailWord_1729229).sum := by decide
  have hdescent : baseEnd_1729229 < baseStart_1729229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729240 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_1729240 : Nat := 118140960795 + 1729240 * 2 ^ 59
def prefixEnd_1729240 : Nat := 4983230072969 + 3 ^ 40 * 1729240 * 2
def baseEnd_1729240 : Nat := 394636127547075366332167

theorem tailTrace_1729240 : CollatzResearch.WordTrace tailWord_1729240 prefixEnd_1729240 394636127547075366332167 := by
  unfold tailWord_1729240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31535282127633142762316587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42047042836844190349755449 31535282127633142762316587)
  ·
    refine ⟨47302923191449714143474881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31535282127633142762316587 47302923191449714143474881)
    ·
      refine ⟨35477192393587285607606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47302923191449714143474881 35477192393587285607606161)
      ·
        refine ⟨26607894295190464205704621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35477192393587285607606161 26607894295190464205704621)
        ·
          refine ⟨9977960360696424077139233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26607894295190464205704621 9977960360696424077139233)
          ·
            refine ⟨7483470270522318057854425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9977960360696424077139233 7483470270522318057854425)
            ·
              refine ⟨5612602702891738543390819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483470270522318057854425 5612602702891738543390819)
              ·
                refine ⟨8418904054337607815086229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612602702891738543390819 8418904054337607815086229)
                ·
                  refine ⟨394636127547075366332167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8418904054337607815086229 394636127547075366332167)
                  ·
                    rfl

theorem cell21_1729240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_1729240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729240 prefixEnd_1729240 := by exact prefixLift 1729240
  have htrace : WordTrace (prefixWord ++ tailWord_1729240) baseStart_1729240 baseEnd_1729240 := by
    simpa [prefixWord, tailWord_1729240, baseEnd_1729240] using wordTrace_append hprefix tailTrace_1729240
  have hstable : (prefixWord ++ tailWord_1729240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729240).length < 2 ^ (prefixWord ++ tailWord_1729240).sum := by decide
  have hdescent : baseEnd_1729240 < baseStart_1729240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729257 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 4]
def baseStart_1729257 : Nat := 118140960795 + 1729257 * 2 ^ 59
def prefixEnd_1729257 : Nat := 4983230072969 + 3 ^ 40 * 1729257 * 2
def baseEnd_1729257 : Nat := 394640007178687114548799

theorem tailTrace_1729257 : CollatzResearch.WordTrace tailWord_1729257 prefixEnd_1729257 394640007178687114548799 := by
  unfold tailWord_1729257
  simp only [CollatzResearch.WordTrace]
  refine ⟨63071184296204697428002025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42047456197469798285334683 63071184296204697428002025)
  ·
    refine ⟨47303388222153523071001519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63071184296204697428002025 47303388222153523071001519)
    ·
      refine ⟨70955082333230284606502279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47303388222153523071001519 70955082333230284606502279)
      ·
        refine ⟨106432623499845426909753419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70955082333230284606502279 106432623499845426909753419)
        ·
          refine ⟨159648935249768140364630129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106432623499845426909753419 159648935249768140364630129)
          ·
            refine ⟨119736701437326105273472597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159648935249768140364630129 119736701437326105273472597)
            ·
              refine ⟨1403164469968665296173507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 119736701437326105273472597 1403164469968665296173507)
              ·
                refine ⟨2104746704952997944260261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403164469968665296173507 2104746704952997944260261)
                ·
                  refine ⟨394640007178687114548799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104746704952997944260261 394640007178687114548799)
                  ·
                    rfl

theorem cell21_1729257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_1729257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729257 prefixEnd_1729257 := by exact prefixLift 1729257
  have htrace : WordTrace (prefixWord ++ tailWord_1729257) baseStart_1729257 baseEnd_1729257 := by
    simpa [prefixWord, tailWord_1729257, baseEnd_1729257] using wordTrace_append hprefix tailTrace_1729257
  have hstable : (prefixWord ++ tailWord_1729257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729257).length < 2 ^ (prefixWord ++ tailWord_1729257).sum := by decide
  have hdescent : baseEnd_1729257 < baseStart_1729257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729426 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1729426 : Nat := 118140960795 + 1729426 * 2 ^ 59
def prefixEnd_1729426 : Nat := 4983230072969 + 3 ^ 40 * 1729426 * 2
def baseEnd_1729426 : Nat := 394678575281180376231787

theorem tailTrace_1729426 : CollatzResearch.WordTrace tailWord_1729426 prefixEnd_1729426 394678575281180376231787 := by
  unfold tailWord_1729426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769337058148109822726033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42051565488394959527269421 15769337058148109822726033)
  ·
    refine ⟨11827002793611082367044525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15769337058148109822726033 11827002793611082367044525)
    ·
      refine ⟨4435126047604155887641697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11827002793611082367044525 4435126047604155887641697)
      ·
        refine ⟨3326344535703116915731273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4435126047604155887641697 3326344535703116915731273)
        ·
          refine ⟨2494758401777337686798455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3326344535703116915731273 2494758401777337686798455)
          ·
            refine ⟨3742137602666006530197683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494758401777337686798455 3742137602666006530197683)
            ·
              refine ⟨5613206403999009795296525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742137602666006530197683 5613206403999009795296525)
              ·
                refine ⟨2104952401499628673236197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613206403999009795296525 2104952401499628673236197)
                ·
                  refine ⟨394678575281180376231787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104952401499628673236197 394678575281180376231787)
                  ·
                    rfl

theorem cell21_1729426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1729426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729426 prefixEnd_1729426 := by exact prefixLift 1729426
  have htrace : WordTrace (prefixWord ++ tailWord_1729426) baseStart_1729426 baseEnd_1729426 := by
    simpa [prefixWord, tailWord_1729426, baseEnd_1729426] using wordTrace_append hprefix tailTrace_1729426
  have hstable : (prefixWord ++ tailWord_1729426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729426).length < 2 ^ (prefixWord ++ tailWord_1729426).sum := by decide
  have hdescent : baseEnd_1729426 < baseStart_1729426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729437 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1729437 : Nat := 118140960795 + 1729437 * 2 ^ 59
def prefixEnd_1729437 : Nat := 4983230072969 + 3 ^ 40 * 1729437 * 2
def baseEnd_1729437 : Nat := 394681085631046801548431

theorem tailTrace_1729437 : CollatzResearch.WordTrace tailWord_1729437 prefixEnd_1729437 394681085631046801548431 := by
  unfold tailWord_1729437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077749435552588169554565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42051832957035058779703043 63077749435552588169554565)
  ·
    refine ⟨11827078019166110281791481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63077749435552588169554565 11827078019166110281791481)
    ·
      refine ⟨8870308514374582711343611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11827078019166110281791481 8870308514374582711343611)
      ·
        refine ⟨13305462771561874067015417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870308514374582711343611 13305462771561874067015417)
        ·
          refine ⟨9979097078671405550261563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13305462771561874067015417 9979097078671405550261563)
          ·
            refine ⟨14968645618007108325392345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979097078671405550261563 14968645618007108325392345)
            ·
              refine ⟨11226484213505331244044259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14968645618007108325392345 11226484213505331244044259)
              ·
                refine ⟨16839726320257996866066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226484213505331244044259 16839726320257996866066389)
                ·
                  refine ⟨394681085631046801548431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16839726320257996866066389 394681085631046801548431)
                  ·
                    rfl

theorem cell21_1729437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1729437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729437 prefixEnd_1729437 := by exact prefixLift 1729437
  have htrace : WordTrace (prefixWord ++ tailWord_1729437) baseStart_1729437 baseEnd_1729437 := by
    simpa [prefixWord, tailWord_1729437, baseEnd_1729437] using wordTrace_append hprefix tailTrace_1729437
  have hstable : (prefixWord ++ tailWord_1729437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729437).length < 2 ^ (prefixWord ++ tailWord_1729437).sum := by decide
  have hdescent : baseEnd_1729437 < baseStart_1729437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729564 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_1729564 : Nat := 118140960795 + 1729564 * 2 ^ 59
def prefixEnd_1729564 : Nat := 4983230072969 + 3 ^ 40 * 1729564 * 2
def baseEnd_1729564 : Nat := 394710068761322802931505

theorem tailTrace_1729564 : CollatzResearch.WordTrace tailWord_1729564 prefixEnd_1729564 394710068761322802931505 := by
  unfold tailWord_1729564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541190753046244429713873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42054921004061659239618497 31541190753046244429713873)
  ·
    refine ⟨23655893064784683322285405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31541190753046244429713873 23655893064784683322285405)
    ·
      refine ⟨8870959899294256245857027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23655893064784683322285405 8870959899294256245857027)
      ·
        refine ⟨13306439848941384368785541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870959899294256245857027 13306439848941384368785541)
        ·
          refine ⟨2494957471676509569147289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13306439848941384368785541 2494957471676509569147289)
          ·
            refine ⟨1871218103757382176860467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494957471676509569147289 1871218103757382176860467)
            ·
              refine ⟨2806827155636073265290701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871218103757382176860467 2806827155636073265290701)
              ·
                refine ⟨1052560183363527474484013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2806827155636073265290701 1052560183363527474484013)
                ·
                  refine ⟨394710068761322802931505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052560183363527474484013 394710068761322802931505)
                  ·
                    rfl

theorem cell21_1729564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_1729564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729564 prefixEnd_1729564 := by exact prefixLift 1729564
  have htrace : WordTrace (prefixWord ++ tailWord_1729564) baseStart_1729564 baseEnd_1729564 := by
    simpa [prefixWord, tailWord_1729564, baseEnd_1729564] using wordTrace_append hprefix tailTrace_1729564
  have hstable : (prefixWord ++ tailWord_1729564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729564).length < 2 ^ (prefixWord ++ tailWord_1729564).sum := by decide
  have hdescent : baseEnd_1729564 < baseStart_1729564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729575 : List Nat := [1, 1, 7, 1, 1, 1, 9]
def baseStart_1729575 : Nat := 118140960795 + 1729575 * 2 ^ 59
def prefixEnd_1729575 : Nat := 4983230072969 + 3 ^ 40 * 1729575 * 2
def baseEnd_1729575 : Nat := 43856953234576580916461

theorem tailTrace_1729575 : CollatzResearch.WordTrace tailWord_1729575 prefixEnd_1729575 43856953234576580916461 := by
  unfold tailWord_1729575
  simp only [CollatzResearch.WordTrace]
  refine ⟨63082782709052637738078179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42055188472701758492052119 63082782709052637738078179)
  ·
    refine ⟨94624174063578956607117269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63082782709052637738078179 94624174063578956607117269)
    ·
      refine ⟨2217754079615131795479311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 94624174063578956607117269 2217754079615131795479311)
      ·
        refine ⟨3326631119422697693218967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217754079615131795479311 3326631119422697693218967)
        ·
          refine ⟨4989946679134046539828451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326631119422697693218967 4989946679134046539828451)
          ·
            refine ⟨7484920018701069809742677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989946679134046539828451 7484920018701069809742677)
            ·
              refine ⟨43856953234576580916461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7484920018701069809742677 43856953234576580916461)
              ·
                rfl

theorem cell21_1729575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 9].length) (baseStart_1729575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729575 prefixEnd_1729575 := by exact prefixLift 1729575
  have htrace : WordTrace (prefixWord ++ tailWord_1729575) baseStart_1729575 baseEnd_1729575 := by
    simpa [prefixWord, tailWord_1729575, baseEnd_1729575] using wordTrace_append hprefix tailTrace_1729575
  have hstable : (prefixWord ++ tailWord_1729575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729575).length < 2 ^ (prefixWord ++ tailWord_1729575).sum := by decide
  have hdescent : baseEnd_1729575 < baseStart_1729575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729640 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_1729640 : Nat := 118140960795 + 1729640 * 2 ^ 59
def prefixEnd_1729640 : Nat := 4983230072969 + 3 ^ 40 * 1729640 * 2
def baseEnd_1729640 : Nat := 394727412996763559664683

theorem tailTrace_1729640 : CollatzResearch.WordTrace tailWord_1729640 prefixEnd_1729640 394727412996763559664683 := by
  unfold tailWord_1729640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31542576726908576919597187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42056768969211435892796249 31542576726908576919597187)
  ·
    refine ⟨47313865090362865379395781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31542576726908576919597187 47313865090362865379395781)
    ·
      refine ⟨8871349704443037258636709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47313865090362865379395781 8871349704443037258636709)
      ·
        refine ⟨1663378069583069485994383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8871349704443037258636709 1663378069583069485994383)
        ·
          refine ⟨2495067104374604228991575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663378069583069485994383 2495067104374604228991575)
          ·
            refine ⟨3742600656561906343487363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495067104374604228991575 3742600656561906343487363)
            ·
              refine ⟨5613900984842859515231045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742600656561906343487363 5613900984842859515231045)
              ·
                refine ⟨1052606434658036159105821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5613900984842859515231045 1052606434658036159105821)
                ·
                  refine ⟨394727412996763559664683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052606434658036159105821 394727412996763559664683)
                  ·
                    rfl

theorem cell21_1729640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_1729640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729640 prefixEnd_1729640 := by exact prefixLift 1729640
  have htrace : WordTrace (prefixWord ++ tailWord_1729640) baseStart_1729640 baseEnd_1729640 := by
    simpa [prefixWord, tailWord_1729640, baseEnd_1729640] using wordTrace_append hprefix tailTrace_1729640
  have hstable : (prefixWord ++ tailWord_1729640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729640).length < 2 ^ (prefixWord ++ tailWord_1729640).sum := by decide
  have hdescent : baseEnd_1729640 < baseStart_1729640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729665 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1729665 : Nat := 118140960795 + 1729665 * 2 ^ 59
def prefixEnd_1729665 : Nat := 4983230072969 + 3 ^ 40 * 1729665 * 2
def baseEnd_1729665 : Nat := 394733118337369071747965

theorem tailTrace_1729665 : CollatzResearch.WordTrace tailWord_1729665 prefixEnd_1729665 394733118337369071747965 := by
  unfold tailWord_1729665
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086065278726583108854449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42057376852484388739236299 63086065278726583108854449)
  ·
    refine ⟨47314548959044937331640837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63086065278726583108854449 47314548959044937331640837)
    ·
      refine ⟨8871477929820925749682657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47314548959044937331640837 8871477929820925749682657)
      ·
        refine ⟨6653608447365694312261993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871477929820925749682657 6653608447365694312261993)
        ·
          refine ⟨4990206335524270734196495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653608447365694312261993 4990206335524270734196495)
          ·
            refine ⟨7485309503286406101294743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990206335524270734196495 7485309503286406101294743)
            ·
              refine ⟨11227964254929609151942115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485309503286406101294743 11227964254929609151942115)
              ·
                refine ⟨16841946382394413727913173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227964254929609151942115 16841946382394413727913173)
                ·
                  refine ⟨394733118337369071747965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16841946382394413727913173 394733118337369071747965)
                  ·
                    rfl

theorem cell21_1729665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1729665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729665 prefixEnd_1729665 := by exact prefixLift 1729665
  have htrace : WordTrace (prefixWord ++ tailWord_1729665) baseStart_1729665 baseEnd_1729665 := by
    simpa [prefixWord, tailWord_1729665, baseEnd_1729665] using wordTrace_append hprefix tailTrace_1729665
  have hstable : (prefixWord ++ tailWord_1729665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729665).length < 2 ^ (prefixWord ++ tailWord_1729665).sum := by decide
  have hdescent : baseEnd_1729665 < baseStart_1729665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729772 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1729772 : Nat := 118140960795 + 1729772 * 2 ^ 59
def prefixEnd_1729772 : Nat := 4983230072969 + 3 ^ 40 * 1729772 * 2
def baseEnd_1729772 : Nat := 394757537195160663464413

theorem tailTrace_1729772 : CollatzResearch.WordTrace tailWord_1729772 prefixEnd_1729772 394757537195160663464413 := by
  unfold tailWord_1729772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31544983944669470191499785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42059978592892626921999713 31544983944669470191499785)
  ·
    refine ⟨23658737958502102643624839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31544983944669470191499785 23658737958502102643624839)
    ·
      refine ⟨35488106937753153965437259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658737958502102643624839 35488106937753153965437259)
      ·
        refine ⟨53232160406629730948155889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35488106937753153965437259 53232160406629730948155889)
        ·
          refine ⟨39924120304972298211116917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53232160406629730948155889 39924120304972298211116917)
          ·
            refine ⟨3742886278591152957292211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39924120304972298211116917 3742886278591152957292211)
            ·
              refine ⟨5614329417886729435938317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742886278591152957292211 5614329417886729435938317)
              ·
                refine ⟨2105373531707523538476869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5614329417886729435938317 2105373531707523538476869)
                ·
                  refine ⟨394757537195160663464413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105373531707523538476869 394757537195160663464413)
                  ·
                    rfl

theorem cell21_1729772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1729772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729772 prefixEnd_1729772 := by exact prefixLift 1729772
  have htrace : WordTrace (prefixWord ++ tailWord_1729772) baseStart_1729772 baseEnd_1729772 := by
    simpa [prefixWord, tailWord_1729772, baseEnd_1729772] using wordTrace_append hprefix tailTrace_1729772
  have hstable : (prefixWord ++ tailWord_1729772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729772).length < 2 ^ (prefixWord ++ tailWord_1729772).sum := by decide
  have hdescent : baseEnd_1729772 < baseStart_1729772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729834 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1729834 : Nat := 118140960795 + 1729834 * 2 ^ 59
def prefixEnd_1729834 : Nat := 4983230072969 + 3 ^ 40 * 1729834 * 2
def baseEnd_1729834 : Nat := 394771686439862333430953

theorem tailTrace_1729834 : CollatzResearch.WordTrace tailWord_1729834 prefixEnd_1729834 394771686439862333430953 := by
  unfold tailWord_1729834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773057303778581242939139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42061486143409549981171037 15773057303778581242939139)
  ·
    refine ⟨23659585955667871864408709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15773057303778581242939139 23659585955667871864408709)
    ·
      refine ⟨4436172366687725974576633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23659585955667871864408709 4436172366687725974576633)
      ·
        refine ⟨3327129275015794480932475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4436172366687725974576633 3327129275015794480932475)
        ·
          refine ⟨4990693912523691721398713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327129275015794480932475 4990693912523691721398713)
          ·
            refine ⟨3743020434392768791049035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990693912523691721398713 3743020434392768791049035)
            ·
              refine ⟨5614530651589153186573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743020434392768791049035 5614530651589153186573553)
              ·
                refine ⟨4210897988691864889930165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5614530651589153186573553 4210897988691864889930165)
                ·
                  refine ⟨394771686439862333430953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210897988691864889930165 394771686439862333430953)
                  ·
                    rfl

theorem cell21_1729834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1729834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729834 prefixEnd_1729834 := by exact prefixLift 1729834
  have htrace : WordTrace (prefixWord ++ tailWord_1729834) baseStart_1729834 baseEnd_1729834 := by
    simpa [prefixWord, tailWord_1729834, baseEnd_1729834] using wordTrace_append hprefix tailTrace_1729834
  have hstable : (prefixWord ++ tailWord_1729834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729834).length < 2 ^ (prefixWord ++ tailWord_1729834).sum := by decide
  have hdescent : baseEnd_1729834 < baseStart_1729834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729896 : List Nat := [2, 1, 4, 2, 3, 2, 2, 5]
def baseStart_1729896 : Nat := 118140960795 + 1729896 * 2 ^ 59
def prefixEnd_1729896 : Nat := 4983230072969 + 3 ^ 40 * 1729896 * 2
def baseEnd_1729896 : Nat := 131595278561521334465831

theorem tailTrace_1729896 : CollatzResearch.WordTrace tailWord_1729896 prefixEnd_1729896 131595278561521334465831 := by
  unfold tailWord_1729896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547245270444854780256771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42062993693926473040342361 31547245270444854780256771)
  ·
    refine ⟨47320867905667282170385157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31547245270444854780256771 47320867905667282170385157)
    ·
      refine ⟨8872662732312615406947217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47320867905667282170385157 8872662732312615406947217)
      ·
        refine ⟨6654497049234461555210413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8872662732312615406947217 6654497049234461555210413)
        ·
          refine ⟨2495436393462923083203905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6654497049234461555210413 2495436393462923083203905)
          ·
            refine ⟨1871577295097192312402929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495436393462923083203905 1871577295097192312402929)
            ·
              refine ⟨1403682971322894234302197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871577295097192312402929 1403682971322894234302197)
              ·
                refine ⟨131595278561521334465831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1403682971322894234302197 131595278561521334465831)
                ·
                  rfl

theorem cell21_1729896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_1729896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729896 prefixEnd_1729896 := by exact prefixLift 1729896
  have htrace : WordTrace (prefixWord ++ tailWord_1729896) baseStart_1729896 baseEnd_1729896 := by
    simpa [prefixWord, tailWord_1729896, baseEnd_1729896] using wordTrace_append hprefix tailTrace_1729896
  have hstable : (prefixWord ++ tailWord_1729896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729896).length < 2 ^ (prefixWord ++ tailWord_1729896).sum := by decide
  have hdescent : baseEnd_1729896 < baseStart_1729896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729927 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 3]
def baseStart_1729927 : Nat := 118140960795 + 1729927 * 2 ^ 59
def prefixEnd_1729927 : Nat := 4983230072969 + 3 ^ 40 * 1729927 * 2
def baseEnd_1729927 : Nat := 394792910306914838380763

theorem tailTrace_1729927 : CollatzResearch.WordTrace tailWord_1729927 prefixEnd_1729927 394792910306914838380763 := by
  unfold tailWord_1729927
  simp only [CollatzResearch.WordTrace]
  refine ⟨63095621203777401854892035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42063747469184934569928023 63095621203777401854892035)
  ·
    refine ⟨94643431805666102782338053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63095621203777401854892035 94643431805666102782338053)
    ·
      refine ⟨17745643463562394271688385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94643431805666102782338053 17745643463562394271688385)
      ·
        refine ⟨13309232597671795703766289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17745643463562394271688385 13309232597671795703766289)
        ·
          refine ⟨9981924448253846777824717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13309232597671795703766289 9981924448253846777824717)
          ·
            refine ⟨3743221668095192541684269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9981924448253846777824717 3743221668095192541684269)
            ·
              refine ⟨1403708125535697203131601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3743221668095192541684269 1403708125535697203131601)
              ·
                refine ⟨1052781094151772902348701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403708125535697203131601 1052781094151772902348701)
                ·
                  refine ⟨394792910306914838380763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052781094151772902348701 394792910306914838380763)
                  ·
                    rfl

theorem cell21_1729927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].length) (baseStart_1729927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729927 prefixEnd_1729927 := by exact prefixLift 1729927
  have htrace : WordTrace (prefixWord ++ tailWord_1729927) baseStart_1729927 baseEnd_1729927 := by
    simpa [prefixWord, tailWord_1729927, baseEnd_1729927] using wordTrace_append hprefix tailTrace_1729927
  have hstable : (prefixWord ++ tailWord_1729927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729927).length < 2 ^ (prefixWord ++ tailWord_1729927).sum := by decide
  have hdescent : baseEnd_1729927 < baseStart_1729927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729952 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_1729952 : Nat := 118140960795 + 1729952 * 2 ^ 59
def prefixEnd_1729952 : Nat := 4983230072969 + 3 ^ 40 * 1729952 * 2
def baseEnd_1729952 : Nat := 394798615647520350464045

theorem tailTrace_1729952 : CollatzResearch.WordTrace tailWord_1729952 prefixEnd_1729952 394798615647520350464045 := by
  unfold tailWord_1729952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31548266514343415562276055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42064355352457887416368073 31548266514343415562276055)
  ·
    refine ⟨47322399771515123343414083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31548266514343415562276055 47322399771515123343414083)
    ·
      refine ⟨70983599657272685015121125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47322399771515123343414083 70983599657272685015121125)
      ·
        refine ⟨13309424935738628440335211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70983599657272685015121125 13309424935738628440335211)
        ·
          refine ⟨19964137403607942660502817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309424935738628440335211 19964137403607942660502817)
          ·
            refine ⟨14973103052705956995377113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19964137403607942660502817 14973103052705956995377113)
            ·
              refine ⟨11229827289529467746532835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14973103052705956995377113 11229827289529467746532835)
              ·
                refine ⟨16844740934294201619799253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229827289529467746532835 16844740934294201619799253)
                ·
                  refine ⟨394798615647520350464045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16844740934294201619799253 394798615647520350464045)
                  ·
                    rfl

theorem cell21_1729952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_1729952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1729952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1729952 prefixEnd_1729952 := by exact prefixLift 1729952
  have htrace : WordTrace (prefixWord ++ tailWord_1729952) baseStart_1729952 baseEnd_1729952 := by
    simpa [prefixWord, tailWord_1729952, baseEnd_1729952] using wordTrace_append hprefix tailTrace_1729952
  have hstable : (prefixWord ++ tailWord_1729952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729952).length < 2 ^ (prefixWord ++ tailWord_1729952).sum := by decide
  have hdescent : baseEnd_1729952 < baseStart_1729952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730045 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1730045 : Nat := 118140960795 + 1730045 * 2 ^ 59
def prefixEnd_1730045 : Nat := 4983230072969 + 3 ^ 40 * 1730045 * 2
def baseEnd_1730045 : Nat := 394819839514572855413855

theorem tailTrace_1730045 : CollatzResearch.WordTrace tailWord_1730045 prefixEnd_1730045 394819839514572855413855 := by
  unfold tailWord_1730045
  simp only [CollatzResearch.WordTrace]
  refine ⟨63099925017349908007687589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42066616678233272005125059 63099925017349908007687589)
  ·
    refine ⟨11831235940753107751441423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63099925017349908007687589 11831235940753107751441423)
    ·
      refine ⟨17746853911129661627162135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11831235940753107751441423 17746853911129661627162135)
      ·
        refine ⟨26620280866694492440743203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17746853911129661627162135 26620280866694492440743203)
        ·
          refine ⟨39930421300041738661114805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26620280866694492440743203 39930421300041738661114805)
          ·
            refine ⟨3743476996878912999479513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39930421300041738661114805 3743476996878912999479513)
            ·
              refine ⟨2807607747659184749609635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3743476996878912999479513 2807607747659184749609635)
              ·
                refine ⟨4211411621488777124414453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807607747659184749609635 4211411621488777124414453)
                ·
                  refine ⟨394819839514572855413855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4211411621488777124414453 394819839514572855413855)
                  ·
                    rfl

theorem cell21_1730045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1730045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730045 prefixEnd_1730045 := by exact prefixLift 1730045
  have htrace : WordTrace (prefixWord ++ tailWord_1730045) baseStart_1730045 baseEnd_1730045 := by
    simpa [prefixWord, tailWord_1730045, baseEnd_1730045] using wordTrace_append hprefix tailTrace_1730045
  have hstable : (prefixWord ++ tailWord_1730045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730045).length < 2 ^ (prefixWord ++ tailWord_1730045).sum := by decide
  have hdescent : baseEnd_1730045 < baseStart_1730045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730149 : List Nat := [1, 3, 1, 3, 3, 10]
def baseStart_1730149 : Nat := 118140960795 + 1730149 * 2 ^ 59
def prefixEnd_1730149 : Nat := 4983230072969 + 3 ^ 40 * 1730149 * 2
def baseEnd_1730149 : Nat := 14623836064129325395567

theorem tailTrace_1730149 : CollatzResearch.WordTrace tailWord_1730149 prefixEnd_1730149 14623836064129325395567 := by
  unfold tailWord_1730149
  simp only [CollatzResearch.WordTrace]
  refine ⟨63103718208973133769473501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42069145472648755846315667 63103718208973133769473501)
  ·
    refine ⟨23663894328364925163552563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63103718208973133769473501 23663894328364925163552563)
    ·
      refine ⟨35495841492547387745328845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23663894328364925163552563 35495841492547387745328845)
      ·
        refine ⟨13310940559705270404498317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35495841492547387745328845 13310940559705270404498317)
        ·
          refine ⟨4991602709889476401686869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13310940559705270404498317 4991602709889476401686869)
          ·
            refine ⟨14623836064129325395567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4991602709889476401686869 14623836064129325395567)
            ·
              rfl

theorem cell21_1730149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 10].length) (baseStart_1730149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730149 prefixEnd_1730149 := by exact prefixLift 1730149
  have htrace : WordTrace (prefixWord ++ tailWord_1730149) baseStart_1730149 baseEnd_1730149 := by
    simpa [prefixWord, tailWord_1730149, baseEnd_1730149] using wordTrace_append hprefix tailTrace_1730149
  have hstable : (prefixWord ++ tailWord_1730149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730149).length < 2 ^ (prefixWord ++ tailWord_1730149).sum := by decide
  have hdescent : baseEnd_1730149 < baseStart_1730149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730152 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_1730152 : Nat := 118140960795 + 1730152 * 2 ^ 59
def prefixEnd_1730152 : Nat := 4983230072969 + 3 ^ 40 * 1730152 * 2
def baseEnd_1730152 : Nat := 394844258372364447130303

theorem tailTrace_1730152 : CollatzResearch.WordTrace tailWord_1730152 prefixEnd_1730152 394844258372364447130303 := by
  unfold tailWord_1730152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31551913813981132640916355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42069218418641510187888473 31551913813981132640916355)
  ·
    refine ⟨47327870720971698961374533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31551913813981132640916355 47327870720971698961374533)
    ·
      refine ⟨8873975760182193555257725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47327870720971698961374533 8873975760182193555257725)
      ·
        refine ⟨3327740910068322583221647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8873975760182193555257725 3327740910068322583221647)
        ·
          refine ⟨4991611365102483874832471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327740910068322583221647 4991611365102483874832471)
          ·
            refine ⟨7487417047653725812248707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991611365102483874832471 7487417047653725812248707)
            ·
              refine ⟨11231125571480588718373061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487417047653725812248707 11231125571480588718373061)
              ·
                refine ⟨2105836044652610384694949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11231125571480588718373061 2105836044652610384694949)
                ·
                  refine ⟨394844258372364447130303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105836044652610384694949 394844258372364447130303)
                  ·
                    rfl

theorem cell21_1730152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_1730152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730152 prefixEnd_1730152 := by exact prefixLift 1730152
  have htrace : WordTrace (prefixWord ++ tailWord_1730152) baseStart_1730152 baseEnd_1730152 := by
    simpa [prefixWord, tailWord_1730152, baseEnd_1730152] using wordTrace_append hprefix tailTrace_1730152
  have hstable : (prefixWord ++ tailWord_1730152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730152).length < 2 ^ (prefixWord ++ tailWord_1730152).sum := by decide
  have hdescent : baseEnd_1730152 < baseStart_1730152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730279 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 4]
def baseStart_1730279 : Nat := 118140960795 + 1730279 * 2 ^ 59
def prefixEnd_1730279 : Nat := 4983230072969 + 3 ^ 40 * 1730279 * 2
def baseEnd_1730279 : Nat := 394873241502640448513377

theorem tailTrace_1730279 : CollatzResearch.WordTrace tailWord_1730279 prefixEnd_1730279 394873241502640448513377 := by
  unfold tailWord_1730279
  simp only [CollatzResearch.WordTrace]
  refine ⟨63108459698502165971705891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42072306465668110647803927 63108459698502165971705891)
  ·
    refine ⟨94662689547753248957558837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63108459698502165971705891 94662689547753248957558837)
    ·
      refine ⟨8874627145101867089771141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94662689547753248957558837 8874627145101867089771141)
      ·
        refine ⟨1663992589706600079332089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8874627145101867089771141 1663992589706600079332089)
        ·
          refine ⟨1247994442279950059499067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1663992589706600079332089 1247994442279950059499067)
          ·
            refine ⟨1871991663419925089248601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247994442279950059499067 1871991663419925089248601)
            ·
              refine ⟨1403993747564943816936451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871991663419925089248601 1403993747564943816936451)
              ·
                refine ⟨2105990621347415725404677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403993747564943816936451 2105990621347415725404677)
                ·
                  refine ⟨394873241502640448513377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105990621347415725404677 394873241502640448513377)
                  ·
                    rfl

theorem cell21_1730279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].length) (baseStart_1730279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730279 prefixEnd_1730279 := by exact prefixLift 1730279
  have htrace : WordTrace (prefixWord ++ tailWord_1730279) baseStart_1730279 baseEnd_1730279 := by
    simpa [prefixWord, tailWord_1730279, baseEnd_1730279] using wordTrace_append hprefix tailTrace_1730279
  have hstable : (prefixWord ++ tailWord_1730279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730279).length < 2 ^ (prefixWord ++ tailWord_1730279).sum := by decide
  have hdescent : baseEnd_1730279 < baseStart_1730279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730287 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_1730287 : Nat := 118140960795 + 1730287 * 2 ^ 59
def prefixEnd_1730287 : Nat := 4983230072969 + 3 ^ 40 * 1730287 * 2
def baseEnd_1730287 : Nat := 394875067211634212380027

theorem tailTrace_1730287 : CollatzResearch.WordTrace tailWord_1730287 prefixEnd_1730287 394875067211634212380027 := by
  unfold tailWord_1730287
  simp only [CollatzResearch.WordTrace]
  refine ⟨63108751482473183337997115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42072500988315455558664743 63108751482473183337997115)
  ·
    refine ⟨94663127223709775006995673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63108751482473183337997115 94663127223709775006995673)
    ·
      refine ⟨70997345417782331255246755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94663127223709775006995673 70997345417782331255246755)
      ·
        refine ⟨106496018126673496882870133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70997345417782331255246755 106496018126673496882870133)
        ·
          refine ⟨9984001699375640332769075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106496018126673496882870133 9984001699375640332769075)
          ·
            refine ⟨14976002549063460499153613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984001699375640332769075 14976002549063460499153613)
            ·
              refine ⟨5616000955898797687182605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14976002549063460499153613 5616000955898797687182605)
              ·
                refine ⟨2106000358462049132693477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5616000955898797687182605 2106000358462049132693477)
                ·
                  refine ⟨394875067211634212380027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106000358462049132693477 394875067211634212380027)
                  ·
                    rfl

theorem cell21_1730287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_1730287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730287 prefixEnd_1730287 := by exact prefixLift 1730287
  have htrace : WordTrace (prefixWord ++ tailWord_1730287) baseStart_1730287 baseEnd_1730287 := by
    simpa [prefixWord, tailWord_1730287, baseEnd_1730287] using wordTrace_append hprefix tailTrace_1730287
  have hstable : (prefixWord ++ tailWord_1730287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730287).length < 2 ^ (prefixWord ++ tailWord_1730287).sum := by decide
  have hdescent : baseEnd_1730287 < baseStart_1730287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730310 : List Nat := [6, 2, 2, 1, 2, 8]
def baseStart_1730310 : Nat := 118140960795 + 1730310 * 2 ^ 59
def prefixEnd_1730310 : Nat := 4983230072969 + 3 ^ 40 * 1730310 * 2
def baseEnd_1730310 : Nat := 14625196893518195685061

theorem tailTrace_1730310 : CollatzResearch.WordTrace tailWord_1730310 prefixEnd_1730310 14625196893518195685061 := by
  unfold tailWord_1730310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972174698793433070815137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42073060240926572177389589 1972174698793433070815137)
  ·
    refine ⟨1479131024095074803111353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1972174698793433070815137 1479131024095074803111353)
    ·
      refine ⟨1109348268071306102333515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479131024095074803111353 1109348268071306102333515)
      ·
        refine ⟨1664022402106959153500273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109348268071306102333515 1664022402106959153500273)
        ·
          refine ⟨1248016801580219365125205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664022402106959153500273 1248016801580219365125205)
          ·
            refine ⟨14625196893518195685061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1248016801580219365125205 14625196893518195685061)
            ·
              rfl

theorem cell21_1730310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 8].length) (baseStart_1730310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730310 prefixEnd_1730310 := by exact prefixLift 1730310
  have htrace : WordTrace (prefixWord ++ tailWord_1730310) baseStart_1730310 baseEnd_1730310 := by
    simpa [prefixWord, tailWord_1730310, baseEnd_1730310] using wordTrace_append hprefix tailTrace_1730310
  have hstable : (prefixWord ++ tailWord_1730310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730310).length < 2 ^ (prefixWord ++ tailWord_1730310).sum := by decide
  have hdescent : baseEnd_1730310 < baseStart_1730310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730332 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1730332 : Nat := 118140960795 + 1730332 * 2 ^ 59
def prefixEnd_1730332 : Nat := 4983230072969 + 3 ^ 40 * 1730332 * 2
def baseEnd_1730332 : Nat := 394885336824724134129935

theorem tailTrace_1730332 : CollatzResearch.WordTrace tailWord_1730332 prefixEnd_1730332 394885336824724134129935 := by
  unfold tailWord_1730332
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555196383655078011692625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42073595178206770682256833 31555196383655078011692625)
  ·
    refine ⟨23666397287741308508769469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31555196383655078011692625 23666397287741308508769469)
    ·
      refine ⟨8874898982902990690788551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23666397287741308508769469 8874898982902990690788551)
      ·
        refine ⟨13312348474354486036182827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8874898982902990690788551 13312348474354486036182827)
        ·
          refine ⟨19968522711531729054274241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312348474354486036182827 19968522711531729054274241)
          ·
            refine ⟨14976392033648796790705681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19968522711531729054274241 14976392033648796790705681)
            ·
              refine ⟨11232294025236597593029261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14976392033648796790705681 11232294025236597593029261)
              ·
                refine ⟨4212110259463724097385973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11232294025236597593029261 4212110259463724097385973)
                ·
                  refine ⟨394885336824724134129935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212110259463724097385973 394885336824724134129935)
                  ·
                    rfl

theorem cell21_1730332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1730332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730332 prefixEnd_1730332 := by exact prefixLift 1730332
  have htrace : WordTrace (prefixWord ++ tailWord_1730332) baseStart_1730332 baseEnd_1730332 := by
    simpa [prefixWord, tailWord_1730332, baseEnd_1730332] using wordTrace_append hprefix tailTrace_1730332
  have hstable : (prefixWord ++ tailWord_1730332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730332).length < 2 ^ (prefixWord ++ tailWord_1730332).sum := by decide
  have hdescent : baseEnd_1730332 < baseStart_1730332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730366 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1730366 : Nat := 118140960795 + 1730366 * 2 ^ 59
def prefixEnd_1730366 : Nat := 4983230072969 + 3 ^ 40 * 1730366 * 2
def baseEnd_1730366 : Nat := 394893096087947630563199

theorem tailTrace_1730366 : CollatzResearch.WordTrace tailWord_1730366 prefixEnd_1730366 394893096087947630563199 := by
  unfold tailWord_1730366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888954106148372478765369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42074421899457986553415301 7888954106148372478765369)
  ·
    refine ⟨5916715579611279359074027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7888954106148372478765369 5916715579611279359074027)
    ·
      refine ⟨8875073369416919038611041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916715579611279359074027 8875073369416919038611041)
      ·
        refine ⟨6656305027062689278958281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8875073369416919038611041 6656305027062689278958281)
        ·
          refine ⟨4992228770297016959218711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6656305027062689278958281 4992228770297016959218711)
          ·
            refine ⟨7488343155445525438828067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992228770297016959218711 7488343155445525438828067)
            ·
              refine ⟨11232514733168288158242101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488343155445525438828067 11232514733168288158242101)
              ·
                refine ⟨1053048256234527014835197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11232514733168288158242101 1053048256234527014835197)
                ·
                  refine ⟨394893096087947630563199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053048256234527014835197 394893096087947630563199)
                  ·
                    rfl

theorem cell21_1730366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1730366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730366 prefixEnd_1730366 := by exact prefixLift 1730366
  have htrace : WordTrace (prefixWord ++ tailWord_1730366) baseStart_1730366 baseEnd_1730366 := by
    simpa [prefixWord, tailWord_1730366, baseEnd_1730366] using wordTrace_append hprefix tailTrace_1730366
  have hstable : (prefixWord ++ tailWord_1730366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730366).length < 2 ^ (prefixWord ++ tailWord_1730366).sum := by decide
  have hdescent : baseEnd_1730366 < baseStart_1730366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730408 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_1730408 : Nat := 118140960795 + 1730408 * 2 ^ 59
def prefixEnd_1730408 : Nat := 4983230072969 + 3 ^ 40 * 1730408 * 2
def baseEnd_1730408 : Nat := 394902681060164890863113

theorem tailTrace_1730408 : CollatzResearch.WordTrace tailWord_1730408 prefixEnd_1730408 394902681060164890863113 := by
  unfold tailWord_1730408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31556582357517410501575939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42075443143356547335434585 31556582357517410501575939)
  ·
    refine ⟨47334873536276115752363909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31556582357517410501575939 47334873536276115752363909)
    ·
      refine ⟨8875288788051771703568233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47334873536276115752363909 8875288788051771703568233)
      ·
        refine ⟨6656466591038828777676175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8875288788051771703568233 6656466591038828777676175)
        ·
          refine ⟨9984699886558243166514263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656466591038828777676175 9984699886558243166514263)
          ·
            refine ⟨14977049829837364749771395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984699886558243166514263 14977049829837364749771395)
            ·
              refine ⟨22465574744756047124657093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14977049829837364749771395 22465574744756047124657093)
              ·
                refine ⟨4212295264641758835873205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22465574744756047124657093 4212295264641758835873205)
                ·
                  refine ⟨394902681060164890863113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212295264641758835873205 394902681060164890863113)
                  ·
                    rfl

theorem cell21_1730408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_1730408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730408 prefixEnd_1730408 := by exact prefixLift 1730408
  have htrace : WordTrace (prefixWord ++ tailWord_1730408) baseStart_1730408 baseEnd_1730408 := by
    simpa [prefixWord, tailWord_1730408, baseEnd_1730408] using wordTrace_append hprefix tailTrace_1730408
  have hstable : (prefixWord ++ tailWord_1730408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730408).length < 2 ^ (prefixWord ++ tailWord_1730408).sum := by decide
  have hdescent : baseEnd_1730408 < baseStart_1730408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730442 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1730442 : Nat := 118140960795 + 1730442 * 2 ^ 59
def prefixEnd_1730442 : Nat := 4983230072969 + 3 ^ 40 * 1730442 * 2
def baseEnd_1730442 : Nat := 394910440323388387296377

theorem tailTrace_1730442 : CollatzResearch.WordTrace tailWord_1730442 prefixEnd_1730442 394910440323388387296377 := by
  unfold tailWord_1730442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15778601199227911202472395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42076269864607763206593053 15778601199227911202472395)
  ·
    refine ⟨23667901798841866803708593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15778601199227911202472395 23667901798841866803708593)
    ·
      refine ⟨17750926349131400102781445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23667901798841866803708593 17750926349131400102781445)
      ·
        refine ⟨3328298690462137519271521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17750926349131400102781445 3328298690462137519271521)
        ·
          refine ⟨2496224017846603139453641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328298690462137519271521 2496224017846603139453641)
          ·
            refine ⟨1872168013384952354590231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496224017846603139453641 1872168013384952354590231)
            ·
              refine ⟨2808252020077428531885347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872168013384952354590231 2808252020077428531885347)
              ·
                refine ⟨4212378030116142797828021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808252020077428531885347 4212378030116142797828021)
                ·
                  refine ⟨394910440323388387296377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212378030116142797828021 394910440323388387296377)
                  ·
                    rfl

theorem cell21_1730442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1730442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730442 prefixEnd_1730442 := by exact prefixLift 1730442
  have htrace : WordTrace (prefixWord ++ tailWord_1730442) baseStart_1730442 baseEnd_1730442 := by
    simpa [prefixWord, tailWord_1730442, baseEnd_1730442] using wordTrace_append hprefix tailTrace_1730442
  have hstable : (prefixWord ++ tailWord_1730442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730442).length < 2 ^ (prefixWord ++ tailWord_1730442).sum := by decide
  have hdescent : baseEnd_1730442 < baseStart_1730442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730453 : List Nat := [1, 3, 2, 1, 1, 3, 4, 6]
def baseStart_1730453 : Nat := 118140960795 + 1730453 * 2 ^ 59
def prefixEnd_1730453 : Nat := 4983230072969 + 3 ^ 40 * 1730453 * 2
def baseEnd_1730453 : Nat := 131637650224418270871007

theorem tailTrace_1730453 : CollatzResearch.WordTrace tailWord_1730453 prefixEnd_1730453 131637650224418270871007 := by
  unfold tailWord_1730453
  simp only [CollatzResearch.WordTrace]
  refine ⟨63114805999871793688540013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42076537333247862459026675 63114805999871793688540013)
  ·
    refine ⟨23668052249951922633202505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63114805999871793688540013 23668052249951922633202505)
    ·
      refine ⟨17751039187463941974901879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23668052249951922633202505 17751039187463941974901879)
      ·
        refine ⟨26626558781195912962352819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17751039187463941974901879 26626558781195912962352819)
        ·
          refine ⟨39939838171793869443529229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626558781195912962352819 39939838171793869443529229)
          ·
            refine ⟨14977439314422701041323461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39939838171793869443529229 14977439314422701041323461)
            ·
              refine ⟨2808269871454256445248149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14977439314422701041323461 2808269871454256445248149)
              ·
                refine ⟨131637650224418270871007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2808269871454256445248149 131637650224418270871007)
                ·
                  rfl

theorem cell21_1730453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_1730453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730453 prefixEnd_1730453 := by exact prefixLift 1730453
  have htrace : WordTrace (prefixWord ++ tailWord_1730453) baseStart_1730453 baseEnd_1730453 := by
    simpa [prefixWord, tailWord_1730453, baseEnd_1730453] using wordTrace_append hprefix tailTrace_1730453
  have hstable : (prefixWord ++ tailWord_1730453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730453).length < 2 ^ (prefixWord ++ tailWord_1730453).sum := by decide
  have hdescent : baseEnd_1730453 < baseStart_1730453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730467 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_1730467 : Nat := 118140960795 + 1730467 * 2 ^ 59
def prefixEnd_1730467 : Nat := 4983230072969 + 3 ^ 40 * 1730467 * 2
def baseEnd_1730467 : Nat := 394916145663993899379659

theorem tailTrace_1730467 : CollatzResearch.WordTrace tailWord_1730467 prefixEnd_1730467 394916145663993899379659 := by
  unfold tailWord_1730467
  simp only [CollatzResearch.WordTrace]
  refine ⟨63115316621821074079549655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42076877747880716053033103 63115316621821074079549655)
  ·
    refine ⟨94672974932731611119324483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63115316621821074079549655 94672974932731611119324483)
    ·
      refine ⟨142009462399097416678986725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94672974932731611119324483 142009462399097416678986725)
      ·
        refine ⟨26626774199830765627310011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142009462399097416678986725 26626774199830765627310011)
        ·
          refine ⟨39940161299746148440965017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626774199830765627310011 39940161299746148440965017)
          ·
            refine ⟨29955120974809611330723763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39940161299746148440965017 29955120974809611330723763)
            ·
              refine ⟨44932681462214416996085645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29955120974809611330723763 44932681462214416996085645)
              ·
                refine ⟨16849755548330406373532117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44932681462214416996085645 16849755548330406373532117)
                ·
                  refine ⟨394916145663993899379659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16849755548330406373532117 394916145663993899379659)
                  ·
                    rfl

theorem cell21_1730467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_1730467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730467 prefixEnd_1730467 := by exact prefixLift 1730467
  have htrace : WordTrace (prefixWord ++ tailWord_1730467) baseStart_1730467 baseEnd_1730467 := by
    simpa [prefixWord, tailWord_1730467, baseEnd_1730467] using wordTrace_append hprefix tailTrace_1730467
  have hstable : (prefixWord ++ tailWord_1730467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730467).length < 2 ^ (prefixWord ++ tailWord_1730467).sum := by decide
  have hdescent : baseEnd_1730467 < baseStart_1730467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730518 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1730518 : Nat := 118140960795 + 1730518 * 2 ^ 59
def prefixEnd_1730518 : Nat := 4983230072969 + 3 ^ 40 * 1730518 * 2
def baseEnd_1730518 : Nat := 394927784558829144029555

theorem tailTrace_1730518 : CollatzResearch.WordTrace tailWord_1730518 prefixEnd_1730518 394927784558829144029555 := by
  unfold tailWord_1730518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944823546539769361853513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42078117829757539859770805 3944823546539769361853513)
  ·
    refine ⟨2958617659904827021390135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3944823546539769361853513 2958617659904827021390135)
    ·
      refine ⟨4437926489857240532085203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958617659904827021390135 4437926489857240532085203)
      ·
        refine ⟨6656889734785860798127805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437926489857240532085203 6656889734785860798127805)
        ·
          refine ⟨2496333650544697799297927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656889734785860798127805 2496333650544697799297927)
          ·
            refine ⟨3744500475817046698946891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496333650544697799297927 3744500475817046698946891)
            ·
              refine ⟨5616750713725570048420337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744500475817046698946891 5616750713725570048420337)
              ·
                refine ⟨4212563035294177536315253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616750713725570048420337 4212563035294177536315253)
                ·
                  refine ⟨394927784558829144029555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212563035294177536315253 394927784558829144029555)
                  ·
                    rfl

theorem cell21_1730518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1730518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730518 prefixEnd_1730518 := by exact prefixLift 1730518
  have htrace : WordTrace (prefixWord ++ tailWord_1730518) baseStart_1730518 baseEnd_1730518 := by
    simpa [prefixWord, tailWord_1730518, baseEnd_1730518] using wordTrace_append hprefix tailTrace_1730518
  have hstable : (prefixWord ++ tailWord_1730518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730518).length < 2 ^ (prefixWord ++ tailWord_1730518).sum := by decide
  have hdescent : baseEnd_1730518 < baseStart_1730518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730543 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_1730543 : Nat := 118140960795 + 1730543 * 2 ^ 59
def prefixEnd_1730543 : Nat := 4983230072969 + 3 ^ 40 * 1730543 * 2
def baseEnd_1730543 : Nat := 394933489899434656112837

theorem tailTrace_1730543 : CollatzResearch.WordTrace tailWord_1730543 prefixEnd_1730543 394933489899434656112837 := by
  unfold tailWord_1730543
  simp only [CollatzResearch.WordTrace]
  refine ⟨63118088569545739059316283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42078725713030492706210855 63118088569545739059316283)
  ·
    refine ⟨94677132854318608588974425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63118088569545739059316283 94677132854318608588974425)
    ·
      refine ⟨71007849640738956441730819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94677132854318608588974425 71007849640738956441730819)
      ·
        refine ⟨106511774461108434662596229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71007849640738956441730819 106511774461108434662596229)
        ·
          refine ⟨19970957711457831499236793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106511774461108434662596229 19970957711457831499236793)
          ·
            refine ⟨14978218283593373624427595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19970957711457831499236793 14978218283593373624427595)
            ·
              refine ⟨22467327425390060436641393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14978218283593373624427595 22467327425390060436641393)
              ·
                refine ⟨16850495569042545327481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22467327425390060436641393 16850495569042545327481045)
                ·
                  refine ⟨394933489899434656112837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16850495569042545327481045 394933489899434656112837)
                  ·
                    rfl

theorem cell21_1730543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_1730543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730543 prefixEnd_1730543 := by exact prefixLift 1730543
  have htrace : WordTrace (prefixWord ++ tailWord_1730543) baseStart_1730543 baseEnd_1730543 := by
    simpa [prefixWord, tailWord_1730543, baseEnd_1730543] using wordTrace_append hprefix tailTrace_1730543
  have hstable : (prefixWord ++ tailWord_1730543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730543).length < 2 ^ (prefixWord ++ tailWord_1730543).sum := by decide
  have hdescent : baseEnd_1730543 < baseStart_1730543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730625 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 4]
def baseStart_1730625 : Nat := 118140960795 + 1730625 * 2 ^ 59
def prefixEnd_1730625 : Nat := 4983230072969 + 3 ^ 40 * 1730625 * 2
def baseEnd_1730625 : Nat := 394952203416620735746003

theorem tailTrace_1730625 : CollatzResearch.WordTrace tailWord_1730625 prefixEnd_1730625 394952203416620735746003 := by
  unfold tailWord_1730625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63121079355248667063801329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42080719570165778042534219 63121079355248667063801329)
  ·
    refine ⟨47340809516436500297850997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63121079355248667063801329 47340809516436500297850997)
    ·
      refine ⟨4438200892165921902923531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47340809516436500297850997 4438200892165921902923531)
      ·
        refine ⟨6657301338248882854385297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438200892165921902923531 6657301338248882854385297)
        ·
          refine ⟨4992976003686662140788973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657301338248882854385297 4992976003686662140788973)
          ·
            refine ⟨1872366001382498302795865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4992976003686662140788973 1872366001382498302795865)
            ·
              refine ⟨1404274501036873727096899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872366001382498302795865 1404274501036873727096899)
              ·
                refine ⟨2106411751555310590645349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404274501036873727096899 2106411751555310590645349)
                ·
                  refine ⟨394952203416620735746003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106411751555310590645349 394952203416620735746003)
                  ·
                    rfl

theorem cell21_1730625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_1730625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730625 prefixEnd_1730625 := by exact prefixLift 1730625
  have htrace : WordTrace (prefixWord ++ tailWord_1730625) baseStart_1730625 baseEnd_1730625 := by
    simpa [prefixWord, tailWord_1730625, baseEnd_1730625] using wordTrace_append hprefix tailTrace_1730625
  have hstable : (prefixWord ++ tailWord_1730625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730625).length < 2 ^ (prefixWord ++ tailWord_1730625).sum := by decide
  have hdescent : baseEnd_1730625 < baseStart_1730625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730664 : List Nat := [2, 1, 4, 14]
def baseStart_1730664 : Nat := 118140960795 + 1730664 * 2 ^ 59
def prefixEnd_1730664 : Nat := 4983230072969 + 3 ^ 40 * 1730664 * 2
def baseEnd_1730664 : Nat := 1625354336411379977761

theorem tailTrace_1730664 : CollatzResearch.WordTrace tailWord_1730664 prefixEnd_1730664 1625354336411379977761 := by
  unfold tailWord_1730664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561250901053688362235523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42081667868071584482980697 31561250901053688362235523)
  ·
    refine ⟨47341876351580532543353285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31561250901053688362235523 47341876351580532543353285)
    ·
      refine ⟨8876601815921349851878741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47341876351580532543353285 8876601815921349851878741)
      ·
        refine ⟨1625354336411379977761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8876601815921349851878741 1625354336411379977761)
        ·
          rfl

theorem cell21_1730664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 14].length) (baseStart_1730664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730664 prefixEnd_1730664 := by exact prefixLift 1730664
  have htrace : WordTrace (prefixWord ++ tailWord_1730664) baseStart_1730664 baseEnd_1730664 := by
    simpa [prefixWord, tailWord_1730664, baseEnd_1730664] using wordTrace_append hprefix tailTrace_1730664
  have hstable : (prefixWord ++ tailWord_1730664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730664).length < 2 ^ (prefixWord ++ tailWord_1730664).sum := by decide
  have hdescent : baseEnd_1730664 < baseStart_1730664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730681 : List Nat := [1, 2, 1, 3, 4, 1, 3, 6]
def baseStart_1730681 : Nat := 118140960795 + 1730681 * 2 ^ 59
def prefixEnd_1730681 : Nat := 4983230072969 + 3 ^ 40 * 1730681 * 2
def baseEnd_1730681 : Nat := 131654994459859027604185

theorem tailTrace_1730681 : CollatzResearch.WordTrace tailWord_1730681 prefixEnd_1730681 131654994459859027604185 := by
  unfold tailWord_1730681
  simp only [CollatzResearch.WordTrace]
  refine ⟨63123121843045788627839897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42082081228697192418559931 63123121843045788627839897)
  ·
    refine ⟨47342341382284341470879923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63123121843045788627839897 47342341382284341470879923)
    ·
      refine ⟨71013512073426512206319885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47342341382284341470879923 71013512073426512206319885)
      ·
        refine ⟨26630067027534942077369957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71013512073426512206319885 26630067027534942077369957)
        ·
          refine ⟨4993137567662801639506867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26630067027534942077369957 4993137567662801639506867)
          ·
            refine ⟨7489706351494202459260301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993137567662801639506867 7489706351494202459260301)
            ·
              refine ⟨2808639881810325922222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7489706351494202459260301 2808639881810325922222613)
              ·
                refine ⟨131654994459859027604185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2808639881810325922222613 131654994459859027604185)
                ·
                  rfl

theorem cell21_1730681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_1730681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730681 prefixEnd_1730681 := by exact prefixLift 1730681
  have htrace : WordTrace (prefixWord ++ tailWord_1730681) baseStart_1730681 baseEnd_1730681 := by
    simpa [prefixWord, tailWord_1730681, baseEnd_1730681] using wordTrace_append hprefix tailTrace_1730681
  have hstable : (prefixWord ++ tailWord_1730681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730681).length < 2 ^ (prefixWord ++ tailWord_1730681).sum := by decide
  have hdescent : baseEnd_1730681 < baseStart_1730681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730695 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_1730695 : Nat := 118140960795 + 1730695 * 2 ^ 59
def prefixEnd_1730695 : Nat := 4983230072969 + 3 ^ 40 * 1730695 * 2
def baseEnd_1730695 : Nat := 394968178370316169579193

theorem tailTrace_1730695 : CollatzResearch.WordTrace tailWord_1730695 prefixEnd_1730695 394968178370316169579193 := by
  unfold tailWord_1730695
  simp only [CollatzResearch.WordTrace]
  refine ⟨63123632464995069018849539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42082421643330046012566359 63123632464995069018849539)
  ·
    refine ⟨94685448697492603528274309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63123632464995069018849539 94685448697492603528274309)
    ·
      refine ⟨17753521630779863161551433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94685448697492603528274309 17753521630779863161551433)
      ·
        refine ⟨13315141223084897371163575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17753521630779863161551433 13315141223084897371163575)
        ·
          refine ⟨19972711834627346056745363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315141223084897371163575 19972711834627346056745363)
          ·
            refine ⟨29959067751941019085118045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19972711834627346056745363 29959067751941019085118045)
            ·
              refine ⟨11234650406977882156919267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29959067751941019085118045 11234650406977882156919267)
              ·
                refine ⟨16851975610466823235378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234650406977882156919267 16851975610466823235378901)
                ·
                  refine ⟨394968178370316169579193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16851975610466823235378901 394968178370316169579193)
                  ·
                    rfl

theorem cell21_1730695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_1730695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730695 prefixEnd_1730695 := by exact prefixLift 1730695
  have htrace : WordTrace (prefixWord ++ tailWord_1730695) baseStart_1730695 baseEnd_1730695 := by
    simpa [prefixWord, tailWord_1730695, baseEnd_1730695] using wordTrace_append hprefix tailTrace_1730695
  have hstable : (prefixWord ++ tailWord_1730695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730695).length < 2 ^ (prefixWord ++ tailWord_1730695).sum := by decide
  have hdescent : baseEnd_1730695 < baseStart_1730695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730698 : List Nat := [3, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1730698 : Nat := 118140960795 + 1730698 * 2 ^ 59
def prefixEnd_1730698 : Nat := 4983230072969 + 3 ^ 40 * 1730698 * 2
def baseEnd_1730698 : Nat := 131656287670396277009729

theorem tailTrace_1730698 : CollatzResearch.WordTrace tailWord_1730698 prefixEnd_1730698 131656287670396277009729 := by
  unfold tailWord_1730698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780935470996050132802187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42082494589322800354139165 15780935470996050132802187)
  ·
    refine ⟨23671403206494075199203281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15780935470996050132802187 23671403206494075199203281)
    ·
      refine ⟨17753552404870556399402461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23671403206494075199203281 17753552404870556399402461)
      ·
        refine ⟨6657582151826458649775923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17753552404870556399402461 6657582151826458649775923)
        ·
          refine ⟨9986373227739687974663885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657582151826458649775923 9986373227739687974663885)
          ·
            refine ⟨3744889960402382990498957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9986373227739687974663885 3744889960402382990498957)
            ·
              refine ⟨1404333735150893621437109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3744889960402382990498957 1404333735150893621437109)
              ·
                refine ⟨131656287670396277009729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1404333735150893621437109 131656287670396277009729)
                ·
                  rfl

theorem cell21_1730698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1730698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730698 prefixEnd_1730698 := by exact prefixLift 1730698
  have htrace : WordTrace (prefixWord ++ tailWord_1730698) baseStart_1730698 baseEnd_1730698 := by
    simpa [prefixWord, tailWord_1730698, baseEnd_1730698] using wordTrace_append hprefix tailTrace_1730698
  have hstable : (prefixWord ++ tailWord_1730698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730698).length < 2 ^ (prefixWord ++ tailWord_1730698).sum := by decide
  have hdescent : baseEnd_1730698 < baseStart_1730698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730718 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1730718 : Nat := 118140960795 + 1730718 * 2 ^ 59
def prefixEnd_1730718 : Nat := 4983230072969 + 3 ^ 40 * 1730718 * 2
def baseEnd_1730718 : Nat := 394973427283673240695813

theorem tailTrace_1730718 : CollatzResearch.WordTrace tailWord_1730718 prefixEnd_1730718 394973427283673240695813 := by
  unfold tailWord_1730718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890558917988967993367101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42082980895941162631291205 7890558917988967993367101)
  ·
    refine ⟨2958959594245862997512663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7890558917988967993367101 2958959594245862997512663)
    ·
      refine ⟨4438439391368794496268995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958959594245862997512663 4438439391368794496268995)
      ·
        refine ⟨6657659087053191744403493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438439391368794496268995 6657659087053191744403493)
        ·
          refine ⟨1248311078822473452075655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6657659087053191744403493 1248311078822473452075655)
          ·
            refine ⟨1872466618233710178113483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248311078822473452075655 1872466618233710178113483)
            ·
              refine ⟨2808699927350565267170225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872466618233710178113483 2808699927350565267170225)
              ·
                refine ⟨2106524945512923950377669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808699927350565267170225 2106524945512923950377669)
                ·
                  refine ⟨394973427283673240695813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106524945512923950377669 394973427283673240695813)
                  ·
                    rfl

theorem cell21_1730718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1730718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730718 prefixEnd_1730718 := by exact prefixLift 1730718
  have htrace : WordTrace (prefixWord ++ tailWord_1730718) baseStart_1730718 baseEnd_1730718 := by
    simpa [prefixWord, tailWord_1730718, baseEnd_1730718] using wordTrace_append hprefix tailTrace_1730718
  have hstable : (prefixWord ++ tailWord_1730718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730718).length < 2 ^ (prefixWord ++ tailWord_1730718).sum := by decide
  have hdescent : baseEnd_1730718 < baseStart_1730718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730757 : List Nat := [1, 3, 1, 1, 1, 1, 8, 5]
def baseStart_1730757 : Nat := 118140960795 + 1730757 * 2 ^ 59
def prefixEnd_1730757 : Nat := 4983230072969 + 3 ^ 40 * 1730757 * 2
def baseEnd_1730757 : Nat := 131660775871672613181911

theorem tailTrace_1730757 : CollatzResearch.WordTrace tailWord_1730757 prefixEnd_1730757 131660775871672613181911 := by
  unfold tailWord_1730757
  simp only [CollatzResearch.WordTrace]
  refine ⟨63125893790770453607606525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42083929193846969071737683 63125893790770453607606525)
  ·
    refine ⟨23672210171538920102852447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63125893790770453607606525 23672210171538920102852447)
    ·
      refine ⟨35508315257308380154278671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672210171538920102852447 35508315257308380154278671)
      ·
        refine ⟨53262472885962570231418007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35508315257308380154278671 53262472885962570231418007)
        ·
          refine ⟨79893709328943855347127011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53262472885962570231418007 79893709328943855347127011)
          ·
            refine ⟨119840563993415783020690517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79893709328943855347127011 119840563993415783020690517)
            ·
              refine ⟨1404381609297841207273717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 119840563993415783020690517 1404381609297841207273717)
              ·
                refine ⟨131660775871672613181911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1404381609297841207273717 131660775871672613181911)
                ·
                  rfl

theorem cell21_1730757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].length) (baseStart_1730757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730757 prefixEnd_1730757 := by exact prefixLift 1730757
  have htrace : WordTrace (prefixWord ++ tailWord_1730757) baseStart_1730757 baseEnd_1730757 := by
    simpa [prefixWord, tailWord_1730757, baseEnd_1730757] using wordTrace_append hprefix tailTrace_1730757
  have hstable : (prefixWord ++ tailWord_1730757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730757).length < 2 ^ (prefixWord ++ tailWord_1730757).sum := by decide
  have hdescent : baseEnd_1730757 < baseStart_1730757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730774 : List Nat := [5, 2, 1, 2, 1, 1, 9]
def baseStart_1730774 : Nat := 118140960795 + 1730774 * 2 ^ 59
def prefixEnd_1730774 : Nat := 4983230072969 + 3 ^ 40 * 1730774 * 2
def baseEnd_1730774 : Nat := 43887356360736620862485

theorem tailTrace_1730774 : CollatzResearch.WordTrace tailWord_1730774 prefixEnd_1730774 43887356360736620862485 := by
  unfold tailWord_1730774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945407114481804094435961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42084342554472577007316917 3945407114481804094435961)
  ·
    refine ⟨2959055335861353070826971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3945407114481804094435961 2959055335861353070826971)
    ·
      refine ⟨4438583003792029606240457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959055335861353070826971 4438583003792029606240457)
      ·
        refine ⟨3328937252844022204680343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438583003792029606240457 3328937252844022204680343)
        ·
          refine ⟨4993405879266033307020515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328937252844022204680343 4993405879266033307020515)
          ·
            refine ⟨7490108818899049960530773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993405879266033307020515 7490108818899049960530773)
            ·
              refine ⟨43887356360736620862485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7490108818899049960530773 43887356360736620862485)
              ·
                rfl

theorem cell21_1730774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 9].length) (baseStart_1730774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730774 prefixEnd_1730774 := by exact prefixLift 1730774
  have htrace : WordTrace (prefixWord ++ tailWord_1730774) baseStart_1730774 baseEnd_1730774 := by
    simpa [prefixWord, tailWord_1730774, baseEnd_1730774] using wordTrace_append hprefix tailTrace_1730774
  have hstable : (prefixWord ++ tailWord_1730774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730774).length < 2 ^ (prefixWord ++ tailWord_1730774).sum := by decide
  have hdescent : baseEnd_1730774 < baseStart_1730774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730780 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_1730780 : Nat := 118140960795 + 1730780 * 2 ^ 59
def prefixEnd_1730780 : Nat := 4983230072969 + 3 ^ 40 * 1730780 * 2
def baseEnd_1730780 : Nat := 394987576528374910662353

theorem tailTrace_1730780 : CollatzResearch.WordTrace tailWord_1730780 prefixEnd_1730780 394987576528374910662353 := by
  unfold tailWord_1730780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563366334843564267846897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42084488446458085690462529 31563366334843564267846897)
  ·
    refine ⟨23672524751132673200885173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31563366334843564267846897 23672524751132673200885173)
    ·
      refine ⟨2219299195418688112582985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23672524751132673200885173 2219299195418688112582985)
      ·
        refine ⟨1664474396564016084437239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219299195418688112582985 1664474396564016084437239)
        ·
          refine ⟨2496711594846024126655859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664474396564016084437239 2496711594846024126655859)
          ·
            refine ⟨3745067392269036189983789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496711594846024126655859 3745067392269036189983789)
            ·
              refine ⟨1404400272100888571243921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3745067392269036189983789 1404400272100888571243921)
              ·
                refine ⟨1053300204075666428432941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404400272100888571243921 1053300204075666428432941)
                ·
                  refine ⟨394987576528374910662353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053300204075666428432941 394987576528374910662353)
                  ·
                    rfl

theorem cell21_1730780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_1730780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730780 prefixEnd_1730780 := by exact prefixLift 1730780
  have htrace : WordTrace (prefixWord ++ tailWord_1730780) baseStart_1730780 baseEnd_1730780 := by
    simpa [prefixWord, tailWord_1730780, baseEnd_1730780] using wordTrace_append hprefix tailTrace_1730780
  have hstable : (prefixWord ++ tailWord_1730780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730780).length < 2 ^ (prefixWord ++ tailWord_1730780).sum := by decide
  have hdescent : baseEnd_1730780 < baseStart_1730780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730816 : List Nat := [2, 1, 1, 2, 1, 1, 6, 7]
def baseStart_1730816 : Nat := 118140960795 + 1730816 * 2 ^ 59
def prefixEnd_1730816 : Nat := 4983230072969 + 3 ^ 40 * 1730816 * 2
def baseEnd_1730816 : Nat := 131665264072948949354093

theorem tailTrace_1730816 : CollatzResearch.WordTrace tailWord_1730816 prefixEnd_1730816 131665264072948949354093 := by
  unfold tailWord_1730816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564022848778353342002151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42085363798371137789336201 31564022848778353342002151)
  ·
    refine ⟨47346034273167530013003227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31564022848778353342002151 47346034273167530013003227)
    ·
      refine ⟨71019051409751295019504841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47346034273167530013003227 71019051409751295019504841)
      ·
        refine ⟨53264288557313471264628631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71019051409751295019504841 53264288557313471264628631)
        ·
          refine ⟨79896432835970206896942947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53264288557313471264628631 79896432835970206896942947)
          ·
            refine ⟨119844649253955310345414421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79896432835970206896942947 119844649253955310345414421)
            ·
              refine ⟨5617717933779155172441301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119844649253955310345414421 5617717933779155172441301)
              ·
                refine ⟨131665264072948949354093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5617717933779155172441301 131665264072948949354093)
                ·
                  rfl

theorem cell21_1730816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_1730816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730816 prefixEnd_1730816 := by exact prefixLift 1730816
  have htrace : WordTrace (prefixWord ++ tailWord_1730816) baseStart_1730816 baseEnd_1730816 := by
    simpa [prefixWord, tailWord_1730816, baseEnd_1730816] using wordTrace_append hprefix tailTrace_1730816
  have hstable : (prefixWord ++ tailWord_1730816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730816).length < 2 ^ (prefixWord ++ tailWord_1730816).sum := by decide
  have hdescent : baseEnd_1730816 < baseStart_1730816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730850 : List Nat := [3, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1730850 : Nat := 118140960795 + 1730850 * 2 ^ 59
def prefixEnd_1730850 : Nat := 4983230072969 + 3 ^ 40 * 1730850 * 2
def baseEnd_1730850 : Nat := 131667850494023448165181

theorem tailTrace_1730850 : CollatzResearch.WordTrace tailWord_1730850 prefixEnd_1730850 131667850494023448165181 := by
  unfold tailWord_1730850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782321444858382622685501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42086190519622353660494669 15782321444858382622685501)
  ·
    refine ⟨5918370541821893483507063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15782321444858382622685501 5918370541821893483507063)
    ·
      refine ⟨8877555812732840225260595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918370541821893483507063 8877555812732840225260595)
      ·
        refine ⟨13316333719099260337890893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877555812732840225260595 13316333719099260337890893)
        ·
          refine ⟨4993625144662222626709085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13316333719099260337890893 4993625144662222626709085)
          ·
            refine ⟨1872609429248333485015907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4993625144662222626709085 1872609429248333485015907)
            ·
              refine ⟨2808914143872500227523861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872609429248333485015907 2808914143872500227523861)
              ·
                refine ⟨131667850494023448165181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2808914143872500227523861 131667850494023448165181)
                ·
                  rfl

theorem cell21_1730850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1730850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730850 prefixEnd_1730850 := by exact prefixLift 1730850
  have htrace : WordTrace (prefixWord ++ tailWord_1730850) baseStart_1730850 baseEnd_1730850 := by
    simpa [prefixWord, tailWord_1730850, baseEnd_1730850] using wordTrace_append hprefix tailTrace_1730850
  have hstable : (prefixWord ++ tailWord_1730850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730850).length < 2 ^ (prefixWord ++ tailWord_1730850).sum := by decide
  have hdescent : baseEnd_1730850 < baseStart_1730850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730892 : List Nat := [2, 2, 1, 3, 2, 1, 10]
def baseStart_1730892 : Nat := 118140960795 + 1730892 * 2 ^ 59
def prefixEnd_1730892 : Nat := 4983230072969 + 3 ^ 40 * 1730892 * 2
def baseEnd_1730892 : Nat := 43890348494920844977273

theorem tailTrace_1730892 : CollatzResearch.WordTrace tailWord_1730892 prefixEnd_1730892 43890348494920844977273 := by
  unfold tailWord_1730892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31565408822640685831885465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42087211763520914442513953 31565408822640685831885465)
  ·
    refine ⟨23674056616980514373914099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31565408822640685831885465 23674056616980514373914099)
    ·
      refine ⟨35511084925470771560871149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23674056616980514373914099 35511084925470771560871149)
      ·
        refine ⟨13316656847051539335326681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35511084925470771560871149 13316656847051539335326681)
        ·
          refine ⟨9987492635288654501495011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13316656847051539335326681 9987492635288654501495011)
          ·
            refine ⟨14981238952932981752242517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987492635288654501495011 14981238952932981752242517)
            ·
              refine ⟨43890348494920844977273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14981238952932981752242517 43890348494920844977273)
              ·
                rfl

theorem cell21_1730892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 10].length) (baseStart_1730892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730892 prefixEnd_1730892 := by exact prefixLift 1730892
  have htrace : WordTrace (prefixWord ++ tailWord_1730892) baseStart_1730892 baseEnd_1730892 := by
    simpa [prefixWord, tailWord_1730892, baseEnd_1730892] using wordTrace_append hprefix tailTrace_1730892
  have hstable : (prefixWord ++ tailWord_1730892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730892).length < 2 ^ (prefixWord ++ tailWord_1730892).sum := by decide
  have hdescent : baseEnd_1730892 < baseStart_1730892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730912 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_1730912 : Nat := 118140960795 + 1730912 * 2 ^ 59
def prefixEnd_1730912 : Nat := 4983230072969 + 3 ^ 40 * 1730912 * 2
def baseEnd_1730912 : Nat := 395017700726772014462083

theorem tailTrace_1730912 : CollatzResearch.WordTrace tailWord_1730912 prefixEnd_1730912 395017700726772014462083 := by
  unfold tailWord_1730912
  simp only [CollatzResearch.WordTrace]
  refine ⟨31565773552604457539749495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42087698070139276719665993 31565773552604457539749495)
  ·
    refine ⟨47348660328906686309624243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31565773552604457539749495 47348660328906686309624243)
    ·
      refine ⟨71022990493360029464436365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47348660328906686309624243 71022990493360029464436365)
      ·
        refine ⟨26633621435010011049163637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71022990493360029464436365 26633621435010011049163637)
        ·
          refine ⟨2496902009532188535859091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26633621435010011049163637 2496902009532188535859091)
          ·
            refine ⟨3745353014298282803788637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496902009532188535859091 3745353014298282803788637)
            ·
              refine ⟨1404507380361856051420739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3745353014298282803788637 1404507380361856051420739)
              ·
                refine ⟨2106761070542784077131109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404507380361856051420739 2106761070542784077131109)
                ·
                  refine ⟨395017700726772014462083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106761070542784077131109 395017700726772014462083)
                  ·
                    rfl

theorem cell21_1730912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_1730912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730912 prefixEnd_1730912 := by exact prefixLift 1730912
  have htrace : WordTrace (prefixWord ++ tailWord_1730912) baseStart_1730912 baseEnd_1730912 := by
    simpa [prefixWord, tailWord_1730912, baseEnd_1730912] using wordTrace_append hprefix tailTrace_1730912
  have hstable : (prefixWord ++ tailWord_1730912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730912).length < 2 ^ (prefixWord ++ tailWord_1730912).sum := by decide
  have hdescent : baseEnd_1730912 < baseStart_1730912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730940 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_1730940 : Nat := 118140960795 + 1730940 * 2 ^ 59
def prefixEnd_1730940 : Nat := 4983230072969 + 3 ^ 40 * 1730940 * 2
def baseEnd_1730940 : Nat := 395024090708250187995359

theorem tailTrace_1730940 : CollatzResearch.WordTrace tailWord_1730940 prefixEnd_1730940 395024090708250187995359 := by
  unfold tailWord_1730940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31566284174553737930759137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42088378899404983907678849 31566284174553737930759137)
  ·
    refine ⟨23674713130915303448069353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31566284174553737930759137 23674713130915303448069353)
    ·
      refine ⟨17756034848186477586052015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23674713130915303448069353 17756034848186477586052015)
      ·
        refine ⟨26634052272279716379078023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17756034848186477586052015 26634052272279716379078023)
        ·
          refine ⟨39951078408419574568617035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26634052272279716379078023 39951078408419574568617035)
          ·
            refine ⟨59926617612629361852925553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39951078408419574568617035 59926617612629361852925553)
            ·
              refine ⟨44944963209472021389694165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59926617612629361852925553 44944963209472021389694165)
              ·
                refine ⟨1053397575222000501320957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44944963209472021389694165 1053397575222000501320957)
                ·
                  refine ⟨395024090708250187995359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053397575222000501320957 395024090708250187995359)
                  ·
                    rfl

theorem cell21_1730940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_1730940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1730940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1730940 prefixEnd_1730940 := by exact prefixLift 1730940
  have htrace : WordTrace (prefixWord ++ tailWord_1730940) baseStart_1730940 baseEnd_1730940 := by
    simpa [prefixWord, tailWord_1730940, baseEnd_1730940] using wordTrace_append hprefix tailTrace_1730940
  have hstable : (prefixWord ++ tailWord_1730940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730940).length < 2 ^ (prefixWord ++ tailWord_1730940).sum := by decide
  have hdescent : baseEnd_1730940 < baseStart_1730940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731075 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_1731075 : Nat := 118140960795 + 1731075 * 2 ^ 59
def prefixEnd_1731075 : Nat := 4983230072969 + 3 ^ 40 * 1731075 * 2
def baseEnd_1731075 : Nat := 395054899547519953245083

theorem tailTrace_1731075 : CollatzResearch.WordTrace tailWord_1731075 prefixEnd_1731075 395054899547519953245083 := by
  unfold tailWord_1731075
  simp only [CollatzResearch.WordTrace]
  refine ⟨63137492203618393917682679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42091661469078929278455119 63137492203618393917682679)
  ·
    refine ⟨94706238305427590876524019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63137492203618393917682679 94706238305427590876524019)
    ·
      refine ⟨142059357458141386314786029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94706238305427590876524019 142059357458141386314786029)
      ·
        refine ⟨53272259046803019868044761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142059357458141386314786029 53272259046803019868044761)
        ·
          refine ⟨39954194285102264901033571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53272259046803019868044761 39954194285102264901033571)
          ·
            refine ⟨59931291427653397351550357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39954194285102264901033571 59931291427653397351550357)
            ·
              refine ⟨2809279285671253000853923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59931291427653397351550357 2809279285671253000853923)
              ·
                refine ⟨4213918928506879501280885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809279285671253000853923 4213918928506879501280885)
                ·
                  refine ⟨395054899547519953245083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213918928506879501280885 395054899547519953245083)
                  ·
                    rfl

theorem cell21_1731075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_1731075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731075 prefixEnd_1731075 := by exact prefixLift 1731075
  have htrace : WordTrace (prefixWord ++ tailWord_1731075) baseStart_1731075 baseEnd_1731075 := by
    simpa [prefixWord, tailWord_1731075, baseEnd_1731075] using wordTrace_append hprefix tailTrace_1731075
  have hstable : (prefixWord ++ tailWord_1731075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731075).length < 2 ^ (prefixWord ++ tailWord_1731075).sum := by decide
  have hdescent : baseEnd_1731075 < baseStart_1731075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731095 : List Nat := [1, 1, 3, 6, 1, 2, 2, 5]
def baseStart_1731095 : Nat := 118140960795 + 1731095 * 2 ^ 59
def prefixEnd_1731095 : Nat := 4983230072969 + 3 ^ 40 * 1731095 * 2
def baseEnd_1731095 : Nat := 131686487940001454303903

theorem tailTrace_1731095 : CollatzResearch.WordTrace tailWord_1731095 prefixEnd_1731095 131686487940001454303903 := by
  unfold tailWord_1731095
  simp only [CollatzResearch.WordTrace]
  refine ⟨63138221663545937333410739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42092147775697291555607159 63138221663545937333410739)
  ·
    refine ⟨94707332495318906000116109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63138221663545937333410739 94707332495318906000116109)
    ·
      refine ⟨35515249685744589750043541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94707332495318906000116109 35515249685744589750043541)
      ·
        refine ⟨1664777329019277644533291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35515249685744589750043541 1664777329019277644533291)
        ·
          refine ⟨2497165993528916466799937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664777329019277644533291 2497165993528916466799937)
          ·
            refine ⟨1872874495146687350099953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2497165993528916466799937 1872874495146687350099953)
            ·
              refine ⟨1404655871360015512574965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872874495146687350099953 1404655871360015512574965)
              ·
                refine ⟨131686487940001454303903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1404655871360015512574965 131686487940001454303903)
                ·
                  rfl

theorem cell21_1731095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].length) (baseStart_1731095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731095 prefixEnd_1731095 := by exact prefixLift 1731095
  have htrace : WordTrace (prefixWord ++ tailWord_1731095) baseStart_1731095 baseEnd_1731095 := by
    simpa [prefixWord, tailWord_1731095, baseEnd_1731095] using wordTrace_append hprefix tailTrace_1731095
  have hstable : (prefixWord ++ tailWord_1731095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731095).length < 2 ^ (prefixWord ++ tailWord_1731095).sum := by decide
  have hdescent : baseEnd_1731095 < baseStart_1731095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731137 : List Nat := [1, 2, 5, 1, 1, 3, 2, 6]
def baseStart_1731137 : Nat := 118140960795 + 1731137 * 2 ^ 59
def prefixEnd_1731137 : Nat := 4983230072969 + 3 ^ 40 * 1731137 * 2
def baseEnd_1731137 : Nat := 131689682930740541070541

theorem tailTrace_1731137 : CollatzResearch.WordTrace tailWord_1731137 prefixEnd_1731137 131689682930740541070541 := by
  unfold tailWord_1731137
  simp only [CollatzResearch.WordTrace]
  refine ⟨63139753529393778506439665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42093169019595852337626443 63139753529393778506439665)
  ·
    refine ⟨47354815147045333879829749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63139753529393778506439665 47354815147045333879829749)
    ·
      refine ⟨4439513920035500051234039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47354815147045333879829749 4439513920035500051234039)
      ·
        refine ⟨6659270880053250076851059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439513920035500051234039 6659270880053250076851059)
        ·
          refine ⟨9988906320079875115276589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659270880053250076851059 9988906320079875115276589)
          ·
            refine ⟨3745839870029953168228721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9988906320079875115276589 3745839870029953168228721)
            ·
              refine ⟨2809379902522464876171541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745839870029953168228721 2809379902522464876171541)
              ·
                refine ⟨131689682930740541070541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2809379902522464876171541 131689682930740541070541)
                ·
                  rfl

theorem cell21_1731137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_1731137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731137 prefixEnd_1731137 := by exact prefixLift 1731137
  have htrace : WordTrace (prefixWord ++ tailWord_1731137) baseStart_1731137 baseEnd_1731137 := by
    simpa [prefixWord, tailWord_1731137, baseEnd_1731137] using wordTrace_append hprefix tailTrace_1731137
  have hstable : (prefixWord ++ tailWord_1731137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731137).length < 2 ^ (prefixWord ++ tailWord_1731137).sum := by decide
  have hdescent : baseEnd_1731137 < baseStart_1731137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731196 : List Nat := [2, 2, 2, 1, 1, 2, 5, 6]
def baseStart_1731196 : Nat := 118140960795 + 1731196 * 2 ^ 59
def prefixEnd_1731196 : Nat := 4983230072969 + 3 ^ 40 * 1731196 * 2
def baseEnd_1731196 : Nat := 131694171132016877242723

theorem tailTrace_1731196 : CollatzResearch.WordTrace tailWord_1731196 prefixEnd_1731196 131694171132016877242723 := by
  unfold tailWord_1731196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31570952718090015791418721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42094603624120021055224961 31570952718090015791418721)
  ·
    refine ⟨23678214538567511843564041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31570952718090015791418721 23678214538567511843564041)
    ·
      refine ⟨17758660903925633882673031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23678214538567511843564041 17758660903925633882673031)
      ·
        refine ⟨26637991355888450824009547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17758660903925633882673031 26637991355888450824009547)
        ·
          refine ⟨39956987033832676236014321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26637991355888450824009547 39956987033832676236014321)
          ·
            refine ⟨29967740275374507177010741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39956987033832676236014321 29967740275374507177010741)
            ·
              refine ⟨2809475650816360047844757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29967740275374507177010741 2809475650816360047844757)
              ·
                refine ⟨131694171132016877242723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2809475650816360047844757 131694171132016877242723)
                ·
                  rfl

theorem cell21_1731196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_1731196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731196 prefixEnd_1731196 := by exact prefixLift 1731196
  have htrace : WordTrace (prefixWord ++ tailWord_1731196) baseStart_1731196 baseEnd_1731196 := by
    simpa [prefixWord, tailWord_1731196, baseEnd_1731196] using wordTrace_append hprefix tailTrace_1731196
  have hstable : (prefixWord ++ tailWord_1731196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731196).length < 2 ^ (prefixWord ++ tailWord_1731196).sum := by decide
  have hdescent : baseEnd_1731196 < baseStart_1731196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731272 : List Nat := [2, 1, 3, 1, 2, 4, 1, 7]
def baseStart_1731272 : Nat := 118140960795 + 1731272 * 2 ^ 59
def prefixEnd_1731272 : Nat := 4983230072969 + 3 ^ 40 * 1731272 * 2
def baseEnd_1731272 : Nat := 131699952543830462820449

theorem tailTrace_1731272 : CollatzResearch.WordTrace tailWord_1731272 prefixEnd_1731272 131699952543830462820449 := by
  unfold tailWord_1731272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31572338691952348281302035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42096451589269797708402713 31572338691952348281302035)
  ·
    refine ⟨47358508037928522421953053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31572338691952348281302035 47358508037928522421953053)
    ·
      refine ⟨17759440514223195908232395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47358508037928522421953053 17759440514223195908232395)
      ·
        refine ⟨26639160771334793862348593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17759440514223195908232395 26639160771334793862348593)
        ·
          refine ⟨19979370578501095396761445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26639160771334793862348593 19979370578501095396761445)
          ·
            refine ⟨3746131983468955386892771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19979370578501095396761445 3746131983468955386892771)
            ·
              refine ⟨5619197975203433080339157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746131983468955386892771 5619197975203433080339157)
              ·
                refine ⟨131699952543830462820449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5619197975203433080339157 131699952543830462820449)
                ·
                  rfl

theorem cell21_1731272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_1731272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731272 prefixEnd_1731272 := by exact prefixLift 1731272
  have htrace : WordTrace (prefixWord ++ tailWord_1731272) baseStart_1731272 baseEnd_1731272 := by
    simpa [prefixWord, tailWord_1731272, baseEnd_1731272] using wordTrace_append hprefix tailTrace_1731272
  have hstable : (prefixWord ++ tailWord_1731272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731272).length < 2 ^ (prefixWord ++ tailWord_1731272).sum := by decide
  have hdescent : baseEnd_1731272 < baseStart_1731272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731351 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_1731351 : Nat := 118140960795 + 1731351 * 2 ^ 59
def prefixEnd_1731351 : Nat := 4983230072969 + 3 ^ 40 * 1731351 * 2
def baseEnd_1731351 : Nat := 395117886507804806644519

theorem tailTrace_1731351 : CollatzResearch.WordTrace tailWord_1731351 prefixEnd_1731351 395117886507804806644519 := by
  unfold tailWord_1731351
  simp only [CollatzResearch.WordTrace]
  refine ⟨63147558750618493054729907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42098372500412328703153271 63147558750618493054729907)
  ·
    refine ⟨94721338125927739582094861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63147558750618493054729907 94721338125927739582094861)
    ·
      refine ⟨35520501797222902343285573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94721338125927739582094861 35520501797222902343285573)
      ·
        refine ⟨6660094086979294189366045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35520501797222902343285573 6660094086979294189366045)
        ·
          refine ⟨2497535282617235321012267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6660094086979294189366045 2497535282617235321012267)
          ·
            refine ⟨3746302923925852981518401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497535282617235321012267 3746302923925852981518401)
            ·
              refine ⟨2809727192944389736138801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746302923925852981518401 2809727192944389736138801)
              ·
                refine ⟨2107295394708292302104101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809727192944389736138801 2107295394708292302104101)
                ·
                  refine ⟨395117886507804806644519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107295394708292302104101 395117886507804806644519)
                  ·
                    rfl

theorem cell21_1731351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_1731351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731351 prefixEnd_1731351 := by exact prefixLift 1731351
  have htrace : WordTrace (prefixWord ++ tailWord_1731351) baseStart_1731351 baseEnd_1731351 := by
    simpa [prefixWord, tailWord_1731351, baseEnd_1731351] using wordTrace_append hprefix tailTrace_1731351
  have hstable : (prefixWord ++ tailWord_1731351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731351).length < 2 ^ (prefixWord ++ tailWord_1731351).sum := by decide
  have hdescent : baseEnd_1731351 < baseStart_1731351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731379 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_1731379 : Nat := 118140960795 + 1731379 * 2 ^ 59
def prefixEnd_1731379 : Nat := 4983230072969 + 3 ^ 40 * 1731379 * 2
def baseEnd_1731379 : Nat := 395124276489282980177795

theorem tailTrace_1731379 : CollatzResearch.WordTrace tailWord_1731379 prefixEnd_1731379 395124276489282980177795 := by
  unfold tailWord_1731379
  simp only [CollatzResearch.WordTrace]
  refine ⟨63148579994517053836749191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42099053329678035891166127 63148579994517053836749191)
  ·
    refine ⟨94722869991775580755123787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63148579994517053836749191 94722869991775580755123787)
    ·
      refine ⟨142084304987663371132685681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94722869991775580755123787 142084304987663371132685681)
      ·
        refine ⟨106563228740747528349514261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142084304987663371132685681 106563228740747528349514261)
        ·
          refine ⟨4995151347222540391383481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106563228740747528349514261 4995151347222540391383481)
          ·
            refine ⟨3746363510416905293537611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995151347222540391383481 3746363510416905293537611)
            ·
              refine ⟨5619545265625357940306417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746363510416905293537611 5619545265625357940306417)
              ·
                refine ⟨4214658949219018455229813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5619545265625357940306417 4214658949219018455229813)
                ·
                  refine ⟨395124276489282980177795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4214658949219018455229813 395124276489282980177795)
                  ·
                    rfl

theorem cell21_1731379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_1731379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731379 prefixEnd_1731379 := by exact prefixLift 1731379
  have htrace : WordTrace (prefixWord ++ tailWord_1731379) baseStart_1731379 baseEnd_1731379 := by
    simpa [prefixWord, tailWord_1731379, baseEnd_1731379] using wordTrace_append hprefix tailTrace_1731379
  have hstable : (prefixWord ++ tailWord_1731379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731379).length < 2 ^ (prefixWord ++ tailWord_1731379).sum := by decide
  have hdescent : baseEnd_1731379 < baseStart_1731379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731427 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 4]
def baseStart_1731427 : Nat := 118140960795 + 1731427 * 2 ^ 59
def prefixEnd_1731427 : Nat := 4983230072969 + 3 ^ 40 * 1731427 * 2
def baseEnd_1731427 : Nat := 395135230743245563377697

theorem tailTrace_1731427 : CollatzResearch.WordTrace tailWord_1731427 prefixEnd_1731427 395135230743245563377697 := by
  unfold tailWord_1731427
  simp only [CollatzResearch.WordTrace]
  refine ⟨63150330698343158034496535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42100220465562105356331023 63150330698343158034496535)
  ·
    refine ⟨94725496047514737051744803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63150330698343158034496535 94725496047514737051744803)
    ·
      refine ⟨142088244071272105577617205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94725496047514737051744803 142088244071272105577617205)
      ·
        refine ⟨13320772881681759897901613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142088244071272105577617205 13320772881681759897901613)
        ·
          refine ⟨4995289830630659961713105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13320772881681759897901613 4995289830630659961713105)
          ·
            refine ⟨3746467372972994971284829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995289830630659961713105 3746467372972994971284829)
            ·
              refine ⟨1404925264864873114231811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3746467372972994971284829 1404925264864873114231811)
              ·
                refine ⟨2107387897297309671347717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404925264864873114231811 2107387897297309671347717)
                ·
                  refine ⟨395135230743245563377697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107387897297309671347717 395135230743245563377697)
                  ·
                    rfl

theorem cell21_1731427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_1731427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731427 prefixEnd_1731427 := by exact prefixLift 1731427
  have htrace : WordTrace (prefixWord ++ tailWord_1731427) baseStart_1731427 baseEnd_1731427 := by
    simpa [prefixWord, tailWord_1731427, baseEnd_1731427] using wordTrace_append hprefix tailTrace_1731427
  have hstable : (prefixWord ++ tailWord_1731427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731427).length < 2 ^ (prefixWord ++ tailWord_1731427).sum := by decide
  have hdescent : baseEnd_1731427 < baseStart_1731427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
