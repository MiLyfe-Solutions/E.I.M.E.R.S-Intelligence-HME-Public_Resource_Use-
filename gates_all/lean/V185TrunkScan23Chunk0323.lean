import V185TrunkScan23Chunk0322

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1909602 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1909602 : Nat := 118140960795 + 1909602 * 2 ^ 59
def prefixEnd_1909602 : Nat := 4983230072969 + 3 ^ 40 * 1909602 * 2
def baseEnd_1909602 : Nat := 980543684787142907092907

theorem tailTrace_1909602 : CollatzResearch.WordTrace tailWord_1909602 prefixEnd_1909602 980543684787142907092907 := by
  unfold tailWord_1909602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412226706961390725462765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46432604551897041934567373 17412226706961390725462765)
  ·
    refine ⟨6529585015110521522048537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17412226706961390725462765 6529585015110521522048537)
    ·
      refine ⟨4897188761332891141536403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6529585015110521522048537 4897188761332891141536403)
      ·
        refine ⟨7345783141999336712304605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897188761332891141536403 7345783141999336712304605)
        ·
          refine ⟨2754668678249751267114227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7345783141999336712304605 2754668678249751267114227)
          ·
            refine ⟨4132003017374626900671341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754668678249751267114227 4132003017374626900671341)
            ·
              refine ⟨1549501131515485087751753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132003017374626900671341 1549501131515485087751753)
              ·
                refine ⟨1162125848636613815813815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549501131515485087751753 1162125848636613815813815)
                ·
                  refine ⟨1743188772954920723720723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162125848636613815813815 1743188772954920723720723)
                  ·
                    refine ⟨2614783159432381085581085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743188772954920723720723 2614783159432381085581085)
                    ·
                      refine ⟨980543684787142907092907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2614783159432381085581085 980543684787142907092907)
                      ·
                        rfl

theorem cell23_1909602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1909602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909602 prefixEnd_1909602 := by exact prefixLift 1909602
  have htrace : WordTrace (prefixWord ++ tailWord_1909602) baseStart_1909602 baseEnd_1909602 := by
    simpa [prefixWord, tailWord_1909602, baseEnd_1909602] using wordTrace_append hprefix tailTrace_1909602
  have hstable : (prefixWord ++ tailWord_1909602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909602).length < 2 ^ (prefixWord ++ tailWord_1909602).sum := by decide
  have hdescent : baseEnd_1909602 < baseStart_1909602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909608 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1909608 : Nat := 118140960795 + 1909608 * 2 ^ 59
def prefixEnd_1909608 : Nat := 4983230072969 + 3 ^ 40 * 1909608 * 2
def baseEnd_1909608 : Nat := 980546765671069883617879

theorem tailTrace_1909608 : CollatzResearch.WordTrace tailWord_1909608 prefixEnd_1909608 980546765671069883617879 := by
  unfold tailWord_1909608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824562832911912963284739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46432750443882550617712985 34824562832911912963284739)
  ·
    refine ⟨52236844249367869444927109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34824562832911912963284739 52236844249367869444927109)
    ·
      refine ⟨9794408296756475520923833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52236844249367869444927109 9794408296756475520923833)
      ·
        refine ⟨7345806222567356640692875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9794408296756475520923833 7345806222567356640692875)
        ·
          refine ⟨11018709333851034961039313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345806222567356640692875 11018709333851034961039313)
          ·
            refine ⟨8264032000388276220779485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11018709333851034961039313 8264032000388276220779485)
            ·
              refine ⟨3099012000145603582792307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8264032000388276220779485 3099012000145603582792307)
              ·
                refine ⟨4648518000218405374188461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099012000145603582792307 4648518000218405374188461)
                ·
                  refine ⟨1743194250081902015320673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648518000218405374188461 1743194250081902015320673)
                  ·
                    refine ⟨1307395687561426511490505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1743194250081902015320673 1307395687561426511490505)
                    ·
                      refine ⟨980546765671069883617879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307395687561426511490505 980546765671069883617879)
                      ·
                        rfl

theorem cell23_1909608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1909608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909608 prefixEnd_1909608 := by exact prefixLift 1909608
  have htrace : WordTrace (prefixWord ++ tailWord_1909608) baseStart_1909608 baseEnd_1909608 := by
    simpa [prefixWord, tailWord_1909608, baseEnd_1909608] using wordTrace_append hprefix tailTrace_1909608
  have hstable : (prefixWord ++ tailWord_1909608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909608).length < 2 ^ (prefixWord ++ tailWord_1909608).sum := by decide
  have hdescent : baseEnd_1909608 < baseStart_1909608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909624 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_1909624 : Nat := 118140960795 + 1909624 * 2 ^ 59
def prefixEnd_1909624 : Nat := 4983230072969 + 3 ^ 40 * 1909624 * 2
def baseEnd_1909624 : Nat := 980554981361541821017805

theorem tailTrace_1909624 : CollatzResearch.WordTrace tailWord_1909624 prefixEnd_1909624 980554981361541821017805 := by
  unfold tailWord_1909624
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824854616882930329575963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46433139489177240439434617 34824854616882930329575963)
  ·
    refine ⟨52237281925324395494363945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34824854616882930329575963 52237281925324395494363945)
    ·
      refine ⟨39177961443993296620772959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52237281925324395494363945 39177961443993296620772959)
      ·
        refine ⟨58766942165989944931159439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39177961443993296620772959 58766942165989944931159439)
        ·
          refine ⟨88150413248984917396739159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58766942165989944931159439 88150413248984917396739159)
          ·
            refine ⟨132225619873477376095108739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88150413248984917396739159 132225619873477376095108739)
            ·
              refine ⟨198338429810216064142663109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132225619873477376095108739 198338429810216064142663109)
              ·
                refine ⟨37188455589415512026749333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198338429810216064142663109 37188455589415512026749333)
                ·
                  refine ⟨1743208855753852126253875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37188455589415512026749333 1743208855753852126253875)
                  ·
                    refine ⟨2614813283630778189380813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743208855753852126253875 2614813283630778189380813)
                    ·
                      refine ⟨980554981361541821017805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2614813283630778189380813 980554981361541821017805)
                      ·
                        rfl

theorem cell23_1909624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_1909624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909624 prefixEnd_1909624 := by exact prefixLift 1909624
  have htrace : WordTrace (prefixWord ++ tailWord_1909624) baseStart_1909624 baseEnd_1909624 := by
    simpa [prefixWord, tailWord_1909624, baseEnd_1909624] using wordTrace_append hprefix tailTrace_1909624
  have hstable : (prefixWord ++ tailWord_1909624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909624).length < 2 ^ (prefixWord ++ tailWord_1909624).sum := by decide
  have hdescent : baseEnd_1909624 < baseStart_1909624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909657 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_1909657 : Nat := 118140960795 + 1909657 * 2 ^ 59
def prefixEnd_1909657 : Nat := 4983230072969 + 3 ^ 40 * 1909657 * 2
def baseEnd_1909657 : Nat := 326857308741046730635051

theorem tailTrace_1909657 : CollatzResearch.WordTrace tailWord_1909657 prefixEnd_1909657 326857308741046730635051 := by
  unfold tailWord_1909657
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650912842646307295103225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46433941895097538196735483 69650912842646307295103225)
  ·
    refine ⟨52238184631984730471327419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69650912842646307295103225 52238184631984730471327419)
    ·
      refine ⟨78357276947977095706991129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52238184631984730471327419 78357276947977095706991129)
      ·
        refine ⟨58767957710982821780243347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78357276947977095706991129 58767957710982821780243347)
        ·
          refine ⟨88151936566474232670365021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58767957710982821780243347 88151936566474232670365021)
          ·
            refine ⟨33056976212427837251386883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88151936566474232670365021 33056976212427837251386883)
            ·
              refine ⟨49585464318641755877080325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33056976212427837251386883 49585464318641755877080325)
              ·
                refine ⟨9297274559745329226952561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49585464318641755877080325 9297274559745329226952561)
                ·
                  refine ⟨6972955919808996920214421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9297274559745329226952561 6972955919808996920214421)
                  ·
                    refine ⟨326857308741046730635051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6972955919808996920214421 326857308741046730635051)
                    ·
                      rfl

theorem cell23_1909657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_1909657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909657 prefixEnd_1909657 := by exact prefixLift 1909657
  have htrace : WordTrace (prefixWord ++ tailWord_1909657) baseStart_1909657 baseEnd_1909657 := by
    simpa [prefixWord, tailWord_1909657, baseEnd_1909657] using wordTrace_append hprefix tailTrace_1909657
  have hstable : (prefixWord ++ tailWord_1909657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909657).length < 2 ^ (prefixWord ++ tailWord_1909657).sum := by decide
  have hdescent : baseEnd_1909657 < baseStart_1909657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909667 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1909667 : Nat := 118140960795 + 1909667 * 2 ^ 59
def prefixEnd_1909667 : Nat := 4983230072969 + 3 ^ 40 * 1909667 * 2
def baseEnd_1909667 : Nat := 980577061029685152780107

theorem tailTrace_1909667 : CollatzResearch.WordTrace tailWord_1909667 prefixEnd_1909667 980577061029685152780107 := by
  unfold tailWord_1909667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69651277572610079002967255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46434185048406719335311503 69651277572610079002967255)
  ·
    refine ⟨104476916358915118504450883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69651277572610079002967255 104476916358915118504450883)
    ·
      refine ⟨156715374538372677756676325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104476916358915118504450883 156715374538372677756676325)
      ·
        refine ⟨29384132725944877079376811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156715374538372677756676325 29384132725944877079376811)
        ·
          refine ⟨44076199088917315619065217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29384132725944877079376811 44076199088917315619065217)
          ·
            refine ⟨33057149316687986714298913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44076199088917315619065217 33057149316687986714298913)
            ·
              refine ⟨24792861987515990035724185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33057149316687986714298913 24792861987515990035724185)
              ·
                refine ⟨18594646490636992526793139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24792861987515990035724185 18594646490636992526793139)
                ·
                  refine ⟨27891969735955488790189709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18594646490636992526793139 27891969735955488790189709)
                  ·
                    refine ⟨10459488650983308296321141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27891969735955488790189709 10459488650983308296321141)
                    ·
                      refine ⟨980577061029685152780107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10459488650983308296321141 980577061029685152780107)
                      ·
                        rfl

theorem cell23_1909667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1909667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909667 prefixEnd_1909667 := by exact prefixLift 1909667
  have htrace : WordTrace (prefixWord ++ tailWord_1909667) baseStart_1909667 baseEnd_1909667 := by
    simpa [prefixWord, tailWord_1909667, baseEnd_1909667] using wordTrace_append hprefix tailTrace_1909667
  have hstable : (prefixWord ++ tailWord_1909667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909667).length < 2 ^ (prefixWord ++ tailWord_1909667).sum := by decide
  have hdescent : baseEnd_1909667 < baseStart_1909667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909687 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 9]
def baseStart_1909687 : Nat := 118140960795 + 1909687 * 2 ^ 59
def prefixEnd_1909687 : Nat := 4983230072969 + 3 ^ 40 * 1909687 * 2
def baseEnd_1909687 : Nat := 108954147849197230503335

theorem tailTrace_1909687 : CollatzResearch.WordTrace tailWord_1909687 prefixEnd_1909687 108954147849197230503335 := by
  unfold tailWord_1909687
  simp only [CollatzResearch.WordTrace]
  refine ⟨69652007032537622418695315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46434671355025081612463543 69652007032537622418695315)
  ·
    refine ⟨104478010548806433628042973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69652007032537622418695315 104478010548806433628042973)
    ·
      refine ⟨39179253955802412610516115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104478010548806433628042973 39179253955802412610516115)
      ·
        refine ⟨58768880933703618915774173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39179253955802412610516115 58768880933703618915774173)
        ·
          refine ⟨22038330350138857093415315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58768880933703618915774173 22038330350138857093415315)
          ·
            refine ⟨33057495525208285640122973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22038330350138857093415315 33057495525208285640122973)
            ·
              refine ⟨12396560821953107115046115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33057495525208285640122973 12396560821953107115046115)
              ·
                refine ⟨18594841232929660672569173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12396560821953107115046115 18594841232929660672569173)
                ·
                  refine ⟨108954147849197230503335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18594841232929660672569173 108954147849197230503335)
                  ·
                    rfl

theorem cell23_1909687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 9].length) (baseStart_1909687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909687 prefixEnd_1909687 := by exact prefixLift 1909687
  have htrace : WordTrace (prefixWord ++ tailWord_1909687) baseStart_1909687 baseEnd_1909687 := by
    simpa [prefixWord, tailWord_1909687, baseEnd_1909687] using wordTrace_append hprefix tailTrace_1909687
  have hstable : (prefixWord ++ tailWord_1909687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909687).length < 2 ^ (prefixWord ++ tailWord_1909687).sum := by decide
  have hdescent : baseEnd_1909687 < baseStart_1909687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909694 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1909694 : Nat := 118140960795 + 1909694 * 2 ^ 59
def prefixEnd_1909694 : Nat := 4983230072969 + 3 ^ 40 * 1909694 * 2
def baseEnd_1909694 : Nat := 980590925007356547142483

theorem tailTrace_1909694 : CollatzResearch.WordTrace tailWord_1909694 prefixEnd_1909694 980590925007356547142483 := by
  unfold tailWord_1909694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706532792939032826775017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46434841562341508409466757 8706532792939032826775017)
  ·
    refine ⟨6529899594704274620081263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8706532792939032826775017 6529899594704274620081263)
    ·
      refine ⟨9794849392056411930121895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529899594704274620081263 9794849392056411930121895)
      ·
        refine ⟨14692274088084617895182843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794849392056411930121895 14692274088084617895182843)
        ·
          refine ⟨22038411132126926842774265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14692274088084617895182843 22038411132126926842774265)
          ·
            refine ⟨16528808349095195132080699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22038411132126926842774265 16528808349095195132080699)
            ·
              refine ⟨24793212523642792698121049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528808349095195132080699 24793212523642792698121049)
              ·
                refine ⟨18594909392732094523590787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24793212523642792698121049 18594909392732094523590787)
                ·
                  refine ⟨27892364089098141785386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18594909392732094523590787 27892364089098141785386181)
                  ·
                    refine ⟨5229818266705901584759909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27892364089098141785386181 5229818266705901584759909)
                    ·
                      refine ⟨980590925007356547142483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5229818266705901584759909 980590925007356547142483)
                      ·
                        rfl

theorem cell23_1909694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1909694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909694 prefixEnd_1909694 := by exact prefixLift 1909694
  have htrace : WordTrace (prefixWord ++ tailWord_1909694) baseStart_1909694 baseEnd_1909694 := by
    simpa [prefixWord, tailWord_1909694, baseEnd_1909694] using wordTrace_append hprefix tailTrace_1909694
  have hstable : (prefixWord ++ tailWord_1909694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909694).length < 2 ^ (prefixWord ++ tailWord_1909694).sum := by decide
  have hdescent : baseEnd_1909694 < baseStart_1909694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909721 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 5]
def baseStart_1909721 : Nat := 118140960795 + 1909721 * 2 ^ 59
def prefixEnd_1909721 : Nat := 4983230072969 + 3 ^ 40 * 1909721 * 2
def baseEnd_1909721 : Nat := 108956087665003104611651

theorem tailTrace_1909721 : CollatzResearch.WordTrace tailWord_1909721 prefixEnd_1909721 108956087665003104611651 := by
  unfold tailWord_1909721
  simp only [CollatzResearch.WordTrace]
  refine ⟨69653247114414446225433017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46435498076276297483622011 69653247114414446225433017)
  ·
    refine ⟨52239935335810834669074763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69653247114414446225433017 52239935335810834669074763)
    ·
      refine ⟨78359903003716252003612145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52239935335810834669074763 78359903003716252003612145)
      ·
        refine ⟨58769927252787189002709109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78359903003716252003612145 58769927252787189002709109)
        ·
          refine ⟨5509680679948798969003979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58769927252787189002709109 5509680679948798969003979)
          ·
            refine ⟨8264521019923198453505969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509680679948798969003979 8264521019923198453505969)
            ·
              refine ⟨6198390764942398840129477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264521019923198453505969 6198390764942398840129477)
              ·
                refine ⟨1162198268426699782524277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6198390764942398840129477 1162198268426699782524277)
                ·
                  refine ⟨108956087665003104611651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162198268426699782524277 108956087665003104611651)
                  ·
                    rfl

theorem cell23_1909721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 5].length) (baseStart_1909721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909721 prefixEnd_1909721 := by exact prefixLift 1909721
  have htrace : WordTrace (prefixWord ++ tailWord_1909721) baseStart_1909721 baseEnd_1909721 := by
    simpa [prefixWord, tailWord_1909721, baseEnd_1909721] using wordTrace_append hprefix tailTrace_1909721
  have hstable : (prefixWord ++ tailWord_1909721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909721).length < 2 ^ (prefixWord ++ tailWord_1909721).sum := by decide
  have hdescent : baseEnd_1909721 < baseStart_1909721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909754 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1909754 : Nat := 118140960795 + 1909754 * 2 ^ 59
def prefixEnd_1909754 : Nat := 4983230072969 + 3 ^ 40 * 1909754 * 2
def baseEnd_1909754 : Nat := 980621733846626312392207

theorem tailTrace_1909754 : CollatzResearch.WordTrace tailWord_1909754 prefixEnd_1909754 980621733846626312392207 := by
  unfold tailWord_1909754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413612680823723215346079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46436300482196595240922877 17413612680823723215346079)
  ·
    refine ⟨26120419021235584823019119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17413612680823723215346079 26120419021235584823019119)
    ·
      refine ⟨39180628531853377234528679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26120419021235584823019119 39180628531853377234528679)
      ·
        refine ⟨58770942797780065851793019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39180628531853377234528679 58770942797780065851793019)
        ·
          refine ⟨88156414196670098777689529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58770942797780065851793019 88156414196670098777689529)
          ·
            refine ⟨66117310647502574083267147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88156414196670098777689529 66117310647502574083267147)
            ·
              refine ⟨99175965971253861124900721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66117310647502574083267147 99175965971253861124900721)
              ·
                refine ⟨74381974478440395843675541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99175965971253861124900721 74381974478440395843675541)
                ·
                  refine ⟨3486655053676893555172291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74381974478440395843675541 3486655053676893555172291)
                  ·
                    refine ⟨5229982580515340332758437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486655053676893555172291 5229982580515340332758437)
                    ·
                      refine ⟨980621733846626312392207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5229982580515340332758437 980621733846626312392207)
                      ·
                        rfl

theorem cell23_1909754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1909754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909754 prefixEnd_1909754 := by exact prefixLift 1909754
  have htrace : WordTrace (prefixWord ++ tailWord_1909754) baseStart_1909754 baseEnd_1909754 := by
    simpa [prefixWord, tailWord_1909754, baseEnd_1909754] using wordTrace_append hprefix tailTrace_1909754
  have hstable : (prefixWord ++ tailWord_1909754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909754).length < 2 ^ (prefixWord ++ tailWord_1909754).sum := by decide
  have hdescent : baseEnd_1909754 < baseStart_1909754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909771 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4]
def baseStart_1909771 : Nat := 118140960795 + 1909771 * 2 ^ 59
def prefixEnd_1909771 : Nat := 4983230072969 + 3 ^ 40 * 1909771 * 2
def baseEnd_1909771 : Nat := 980630463017752745879629

theorem tailTrace_1909771 : CollatzResearch.WordTrace tailWord_1909771 prefixEnd_1909771 980630463017752745879629 := by
  unfold tailWord_1909771
  simp only [CollatzResearch.WordTrace]
  refine ⟨69655070764233304764753167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46436713842822203176502111 69655070764233304764753167)
  ·
    refine ⟨104482606146349957147129751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69655070764233304764753167 104482606146349957147129751)
    ·
      refine ⟨156723909219524935720694627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104482606146349957147129751 156723909219524935720694627)
      ·
        refine ⟨235085863829287403581041941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156723909219524935720694627 235085863829287403581041941)
        ·
          refine ⟨11019649866997847042861341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235085863829287403581041941 11019649866997847042861341)
          ·
            refine ⟨4132368700124192641073003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11019649866997847042861341 4132368700124192641073003)
            ·
              refine ⟨6198553050186288961609505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132368700124192641073003 6198553050186288961609505)
              ·
                refine ⟨4648914787639716721207129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198553050186288961609505 4648914787639716721207129)
                ·
                  refine ⟨3486686090729787540905347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648914787639716721207129 3486686090729787540905347)
                  ·
                    refine ⟨5230029136094681311358021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486686090729787540905347 5230029136094681311358021)
                    ·
                      refine ⟨980630463017752745879629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5230029136094681311358021 980630463017752745879629)
                      ·
                        rfl

theorem cell23_1909771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_1909771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909771 prefixEnd_1909771 := by exact prefixLift 1909771
  have htrace : WordTrace (prefixWord ++ tailWord_1909771) baseStart_1909771 baseEnd_1909771 := by
    simpa [prefixWord, tailWord_1909771, baseEnd_1909771] using wordTrace_append hprefix tailTrace_1909771
  have hstable : (prefixWord ++ tailWord_1909771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909771).length < 2 ^ (prefixWord ++ tailWord_1909771).sum := by decide
  have hdescent : baseEnd_1909771 < baseStart_1909771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909838 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1909838 : Nat := 118140960795 + 1909838 * 2 ^ 59
def prefixEnd_1909838 : Nat := 4983230072969 + 3 ^ 40 * 1909838 * 2
def baseEnd_1909838 : Nat := 980664866221603983741821

theorem tailTrace_1909838 : CollatzResearch.WordTrace tailWord_1909838 prefixEnd_1909838 980664866221603983741821 := by
  unfold tailWord_1909838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707189306873821900930271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46438342969993716804961445 8707189306873821900930271)
  ·
    refine ⟨13060783960310732851395407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8707189306873821900930271 13060783960310732851395407)
    ·
      refine ⟨19591175940466099277093111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13060783960310732851395407 19591175940466099277093111)
      ·
        refine ⟨29386763910699148915639667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591175940466099277093111 29386763910699148915639667)
        ·
          refine ⟨44080145866048723373459501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29386763910699148915639667 44080145866048723373459501)
          ·
            refine ⟨16530054699768271265047313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44080145866048723373459501 16530054699768271265047313)
            ·
              refine ⟨12397541024826203448785485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16530054699768271265047313 12397541024826203448785485)
              ·
                refine ⟨4649077884309826293294557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12397541024826203448785485 4649077884309826293294557)
                ·
                  refine ⟨1743404206616184859985459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4649077884309826293294557 1743404206616184859985459)
                  ·
                    refine ⟨2615106309924277289978189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743404206616184859985459 2615106309924277289978189)
                    ·
                      refine ⟨980664866221603983741821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615106309924277289978189 980664866221603983741821)
                      ·
                        rfl

theorem cell23_1909838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1909838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909838 prefixEnd_1909838 := by exact prefixLift 1909838
  have htrace : WordTrace (prefixWord ++ tailWord_1909838) baseStart_1909838 baseEnd_1909838 := by
    simpa [prefixWord, tailWord_1909838, baseEnd_1909838] using wordTrace_append hprefix tailTrace_1909838
  have hstable : (prefixWord ++ tailWord_1909838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909838).length < 2 ^ (prefixWord ++ tailWord_1909838).sum := by decide
  have hdescent : baseEnd_1909838 < baseStart_1909838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909858 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1909858 : Nat := 118140960795 + 1909858 * 2 ^ 59
def prefixEnd_1909858 : Nat := 4983230072969 + 3 ^ 40 * 1909858 * 2
def baseEnd_1909858 : Nat := 326891711944897968497243

theorem tailTrace_1909858 : CollatzResearch.WordTrace tailWord_1909858 prefixEnd_1909858 326891711944897968497243 := by
  unfold tailWord_1909858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414560978729529655792557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46438829276612079082113485 17414560978729529655792557)
  ·
    refine ⟨6530460367023573620922209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17414560978729529655792557 6530460367023573620922209)
    ·
      refine ⟨4897845275267680215691657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6530460367023573620922209 4897845275267680215691657)
      ·
        refine ⟨3673383956450760161768743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4897845275267680215691657 3673383956450760161768743)
        ·
          refine ⟨5510075934676140242653115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673383956450760161768743 5510075934676140242653115)
          ·
            refine ⟨8265113902014210363979673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510075934676140242653115 8265113902014210363979673)
            ·
              refine ⟨6198835426510657772984755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265113902014210363979673 6198835426510657772984755)
              ·
                refine ⟨9298253139765986659477133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198835426510657772984755 9298253139765986659477133)
                ·
                  refine ⟨3486844927412244997303925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9298253139765986659477133 3486844927412244997303925)
                  ·
                    refine ⟨326891711944897968497243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3486844927412244997303925 326891711944897968497243)
                    ·
                      rfl

theorem cell23_1909858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1909858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909858 prefixEnd_1909858 := by exact prefixLift 1909858
  have htrace : WordTrace (prefixWord ++ tailWord_1909858) baseStart_1909858 baseEnd_1909858 := by
    simpa [prefixWord, tailWord_1909858, baseEnd_1909858] using wordTrace_append hprefix tailTrace_1909858
  have hstable : (prefixWord ++ tailWord_1909858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909858).length < 2 ^ (prefixWord ++ tailWord_1909858).sum := by decide
  have hdescent : baseEnd_1909858 < baseStart_1909858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909861 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1909861 : Nat := 118140960795 + 1909861 * 2 ^ 59
def prefixEnd_1909861 : Nat := 4983230072969 + 3 ^ 40 * 1909861 * 2
def baseEnd_1909861 : Nat := 980676676276657393754215

theorem tailTrace_1909861 : CollatzResearch.WordTrace tailWord_1909861 prefixEnd_1909861 980676676276657393754215 := by
  unfold tailWord_1909861
  simp only [CollatzResearch.WordTrace]
  refine ⟨69658353333907250135529437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46438902222604833423686291 69658353333907250135529437)
  ·
    refine ⟨26121882500215218800823539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69658353333907250135529437 26121882500215218800823539)
    ·
      refine ⟨39182823750322828201235309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26121882500215218800823539 39182823750322828201235309)
      ·
        refine ⟨14693558906371060575463241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39182823750322828201235309 14693558906371060575463241)
        ·
          refine ⟨11020169179778295431597431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14693558906371060575463241 11020169179778295431597431)
          ·
            refine ⟨16530253769667443147396147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020169179778295431597431 16530253769667443147396147)
            ·
              refine ⟨24795380654501164721094221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530253769667443147396147 24795380654501164721094221)
              ·
                refine ⟨9298267745437936770410333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24795380654501164721094221 9298267745437936770410333)
                ·
                  refine ⟨3486850404539226288903875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9298267745437936770410333 3486850404539226288903875)
                  ·
                    refine ⟨5230275606808839433355813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486850404539226288903875 5230275606808839433355813)
                    ·
                      refine ⟨980676676276657393754215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5230275606808839433355813 980676676276657393754215)
                      ·
                        rfl

theorem cell23_1909861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1909861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909861 prefixEnd_1909861 := by exact prefixLift 1909861
  have htrace : WordTrace (prefixWord ++ tailWord_1909861) baseStart_1909861 baseEnd_1909861 := by
    simpa [prefixWord, tailWord_1909861, baseEnd_1909861] using wordTrace_append hprefix tailTrace_1909861
  have hstable : (prefixWord ++ tailWord_1909861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909861).length < 2 ^ (prefixWord ++ tailWord_1909861).sum := by decide
  have hdescent : baseEnd_1909861 < baseStart_1909861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909865 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 2, 3, 2]
def baseStart_1909865 : Nat := 118140960795 + 1909865 * 2 ^ 59
def prefixEnd_1909865 : Nat := 4983230072969 + 3 ^ 40 * 1909865 * 2
def baseEnd_1909865 : Nat := 980678730199275378104197

theorem tailTrace_1909865 : CollatzResearch.WordTrace tailWord_1909865 prefixEnd_1909865 980678730199275378104197 := by
  unfold tailWord_1909865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69658499225892758818675049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46438999483928505879116699 69658499225892758818675049)
  ·
    refine ⟨52243874419419569114006287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69658499225892758818675049 52243874419419569114006287)
    ·
      refine ⟨78365811629129353671009431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52243874419419569114006287 78365811629129353671009431)
      ·
        refine ⟨117548717443694030506514147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78365811629129353671009431 117548717443694030506514147)
        ·
          refine ⟨176323076165541045759771221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117548717443694030506514147 176323076165541045759771221)
          ·
            refine ⟨2066286048814934129997319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 176323076165541045759771221 2066286048814934129997319)
            ·
              refine ⟨3099429073222401194995979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066286048814934129997319 3099429073222401194995979)
              ·
                refine ⟨4649143609833601792493969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099429073222401194995979 4649143609833601792493969)
                ·
                  refine ⟨3486857707375201344370477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4649143609833601792493969 3486857707375201344370477)
                  ·
                    refine ⟨1307571640265700504138929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486857707375201344370477 1307571640265700504138929)
                    ·
                      refine ⟨980678730199275378104197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307571640265700504138929 980678730199275378104197)
                      ·
                        rfl

theorem cell23_1909865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3, 2].length) (baseStart_1909865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909865 prefixEnd_1909865 := by exact prefixLift 1909865
  have htrace : WordTrace (prefixWord ++ tailWord_1909865) baseStart_1909865 baseEnd_1909865 := by
    simpa [prefixWord, tailWord_1909865, baseEnd_1909865] using wordTrace_append hprefix tailTrace_1909865
  have hstable : (prefixWord ++ tailWord_1909865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909865).length < 2 ^ (prefixWord ++ tailWord_1909865).sum := by decide
  have hdescent : baseEnd_1909865 < baseStart_1909865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909871 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 4, 4]
def baseStart_1909871 : Nat := 118140960795 + 1909871 * 2 ^ 59
def prefixEnd_1909871 : Nat := 4983230072969 + 3 ^ 40 * 1909871 * 2
def baseEnd_1909871 : Nat := 326893937027734118209723

theorem tailTrace_1909871 : CollatzResearch.WordTrace tailWord_1909871 prefixEnd_1909871 326893937027734118209723 := by
  unfold tailWord_1909871
  simp only [CollatzResearch.WordTrace]
  refine ⟨69658718063871021843393467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46439145375914014562262311 69658718063871021843393467)
  ·
    refine ⟨104488077095806532765090201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69658718063871021843393467 104488077095806532765090201)
    ·
      refine ⟨78366057821854899573817651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104488077095806532765090201 78366057821854899573817651)
      ·
        refine ⟨117549086732782349360726477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78366057821854899573817651 117549086732782349360726477)
        ·
          refine ⟨44080907524793381010272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117549086732782349360726477 44080907524793381010272429)
          ·
            refine ⟨16530340321797517878852161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44080907524793381010272429 16530340321797517878852161)
            ·
              refine ⟨12397755241348138409139121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16530340321797517878852161 12397755241348138409139121)
              ·
                refine ⟨9298316431011103806854341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397755241348138409139121 9298316431011103806854341)
                ·
                  refine ⟨1743434330814581963785189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9298316431011103806854341 1743434330814581963785189)
                  ·
                    refine ⟨326893937027734118209723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743434330814581963785189 326893937027734118209723)
                    ·
                      rfl

theorem cell23_1909871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_1909871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909871 prefixEnd_1909871 := by exact prefixLift 1909871
  have htrace : WordTrace (prefixWord ++ tailWord_1909871) baseStart_1909871 baseEnd_1909871 := by
    simpa [prefixWord, tailWord_1909871, baseEnd_1909871] using wordTrace_append hprefix tailTrace_1909871
  have hstable : (prefixWord ++ tailWord_1909871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909871).length < 2 ^ (prefixWord ++ tailWord_1909871).sum := by decide
  have hdescent : baseEnd_1909871 < baseStart_1909871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909884 : List Nat := [2, 2, 2, 1, 1, 3, 12]
def baseStart_1909884 : Nat := 118140960795 + 1909884 * 2 ^ 59
def prefixEnd_1909884 : Nat := 4983230072969 + 3 ^ 40 * 1909884 * 2
def baseEnd_1909884 : Nat := 12107265263354454367489

theorem tailTrace_1909884 : CollatzResearch.WordTrace tailWord_1909884 prefixEnd_1909884 12107265263354454367489 := by
  unfold tailWord_1909884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829596106411962531808353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46439461475215950042411137 34829596106411962531808353)
  ·
    refine ⟨26122197079808971898856265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34829596106411962531808353 26122197079808971898856265)
    ·
      refine ⟨19591647809856728924142199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26122197079808971898856265 19591647809856728924142199)
      ·
        refine ⟨29387471714785093386213299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591647809856728924142199 29387471714785093386213299)
        ·
          refine ⟨44081207572177640079319949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387471714785093386213299 44081207572177640079319949)
          ·
            refine ⟨16530452839566615029744981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44081207572177640079319949 16530452839566615029744981)
            ·
              refine ⟨12107265263354454367489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16530452839566615029744981 12107265263354454367489)
              ·
                rfl

theorem cell23_1909884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 12].length) (baseStart_1909884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909884 prefixEnd_1909884 := by exact prefixLift 1909884
  have htrace : WordTrace (prefixWord ++ tailWord_1909884) baseStart_1909884 baseEnd_1909884 := by
    simpa [prefixWord, tailWord_1909884, baseEnd_1909884] using wordTrace_append hprefix tailTrace_1909884
  have hstable : (prefixWord ++ tailWord_1909884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909884).length < 2 ^ (prefixWord ++ tailWord_1909884).sum := by decide
  have hdescent : baseEnd_1909884 < baseStart_1909884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909888 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_1909888 : Nat := 118140960795 + 1909888 * 2 ^ 59
def prefixEnd_1909888 : Nat := 4983230072969 + 3 ^ 40 * 1909888 * 2
def baseEnd_1909888 : Nat := 326896846751442929372197

theorem tailTrace_1909888 : CollatzResearch.WordTrace tailWord_1909888 prefixEnd_1909888 326896846751442929372197 := by
  unfold tailWord_1909888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829669052404716873381159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46439558736539622497841545 34829669052404716873381159)
  ·
    refine ⟨52244503578607075310071739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34829669052404716873381159 52244503578607075310071739)
    ·
      refine ⟨78366755367910612965107609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52244503578607075310071739 78366755367910612965107609)
      ·
        refine ⟨58775066525932959723830707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78366755367910612965107609 58775066525932959723830707)
        ·
          refine ⟨88162599788899439585746061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58775066525932959723830707 88162599788899439585746061)
          ·
            refine ⟨33060974920837289844654773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88162599788899439585746061 33060974920837289844654773)
            ·
              refine ⟨3099466398828495922936385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33060974920837289844654773 3099466398828495922936385)
              ·
                refine ⟨2324599799121371942202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099466398828495922936385 2324599799121371942202289)
                ·
                  refine ⟨1743449849341028956651717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2324599799121371942202289 1743449849341028956651717)
                  ·
                    refine ⟨326896846751442929372197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743449849341028956651717 326896846751442929372197)
                    ·
                      rfl

theorem cell23_1909888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_1909888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909888 prefixEnd_1909888 := by exact prefixLift 1909888
  have htrace : WordTrace (prefixWord ++ tailWord_1909888) baseStart_1909888 baseEnd_1909888 := by
    simpa [prefixWord, tailWord_1909888, baseEnd_1909888] using wordTrace_append hprefix tailTrace_1909888
  have hstable : (prefixWord ++ tailWord_1909888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909888).length < 2 ^ (prefixWord ++ tailWord_1909888).sum := by decide
  have hdescent : baseEnd_1909888 < baseStart_1909888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909904 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1909904 : Nat := 118140960795 + 1909904 * 2 ^ 59
def prefixEnd_1909904 : Nat := 4983230072969 + 3 ^ 40 * 1909904 * 2
def baseEnd_1909904 : Nat := 980698755944800725516517

theorem tailTrace_1909904 : CollatzResearch.WordTrace tailWord_1909904 prefixEnd_1909904 980698755944800725516517 := by
  unfold tailWord_1909904
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829960836375734239672383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46439947781834312319563177 34829960836375734239672383)
  ·
    refine ⟨52244941254563601359508575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34829960836375734239672383 52244941254563601359508575)
    ·
      refine ⟨78367411881845402039262863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52244941254563601359508575 78367411881845402039262863)
      ·
        refine ⟨117551117822768103058894295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78367411881845402039262863 117551117822768103058894295)
        ·
          refine ⟨176326676734152154588341443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117551117822768103058894295 176326676734152154588341443)
          ·
            refine ⟨264490015101228231882512165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176326676734152154588341443 264490015101228231882512165)
            ·
              refine ⟨49591877831480293477971031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264490015101228231882512165 49591877831480293477971031)
              ·
                refine ⟨74387816747220440216956547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49591877831480293477971031 74387816747220440216956547)
                ·
                  refine ⟨111581725120830660325434821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74387816747220440216956547 111581725120830660325434821)
                  ·
                    refine ⟨20921573460155748811019029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111581725120830660325434821 20921573460155748811019029)
                    ·
                      refine ⟨980698755944800725516517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20921573460155748811019029 980698755944800725516517)
                      ·
                        rfl

theorem cell23_1909904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1909904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909904 prefixEnd_1909904 := by exact prefixLift 1909904
  have htrace : WordTrace (prefixWord ++ tailWord_1909904) baseStart_1909904 baseEnd_1909904 := by
    simpa [prefixWord, tailWord_1909904, baseEnd_1909904] using wordTrace_append hprefix tailTrace_1909904
  have hstable : (prefixWord ++ tailWord_1909904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909904).length < 2 ^ (prefixWord ++ tailWord_1909904).sum := by decide
  have hdescent : baseEnd_1909904 < baseStart_1909904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909918 : List Nat := [4, 3, 1, 1, 2, 2, 1, 9]
def baseStart_1909918 : Nat := 118140960795 + 1909918 * 2 ^ 59
def prefixEnd_1909918 : Nat := 4983230072969 + 3 ^ 40 * 1909918 * 2
def baseEnd_1909918 : Nat := 36322442395331987805239

theorem tailTrace_1909918 : CollatzResearch.WordTrace tailWord_1909918 prefixEnd_1909918 36322442395331987805239 := by
  unfold tailWord_1909918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707554036837593608794301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46440288196467165913569605 8707554036837593608794301)
  ·
    refine ⟨3265332763814097603297863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8707554036837593608794301 3265332763814097603297863)
    ·
      refine ⟨4897999145721146404946795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265332763814097603297863 4897999145721146404946795)
      ·
        refine ⟨7346998718581719607420193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897999145721146404946795 7346998718581719607420193)
        ·
          refine ⟨5510249038936289705565145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7346998718581719607420193 5510249038936289705565145)
          ·
            refine ⟨4132686779202217279173859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510249038936289705565145 4132686779202217279173859)
            ·
              refine ⟨6199030168803325918760789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132686779202217279173859 6199030168803325918760789)
              ·
                refine ⟨36322442395331987805239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6199030168803325918760789 36322442395331987805239)
                ·
                  rfl

theorem cell23_1909918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_1909918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909918 prefixEnd_1909918 := by exact prefixLift 1909918
  have htrace : WordTrace (prefixWord ++ tailWord_1909918) baseStart_1909918 baseEnd_1909918 := by
    simpa [prefixWord, tailWord_1909918, baseEnd_1909918] using wordTrace_append hprefix tailTrace_1909918
  have hstable : (prefixWord ++ tailWord_1909918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909918).length < 2 ^ (prefixWord ++ tailWord_1909918).sum := by decide
  have hdescent : baseEnd_1909918 < baseStart_1909918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909962 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_1909962 : Nat := 118140960795 + 1909962 * 2 ^ 59
def prefixEnd_1909962 : Nat := 4983230072969 + 3 ^ 40 * 1909962 * 2
def baseEnd_1909962 : Nat := 980728537822761498591251

theorem tailTrace_1909962 : CollatzResearch.WordTrace tailWord_1909962 prefixEnd_1909962 980728537822761498591251 := by
  unfold tailWord_1909962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415509276635336096239035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46441358071027562923304093 17415509276635336096239035)
  ·
    refine ⟨26123263914953004144358553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17415509276635336096239035 26123263914953004144358553)
    ·
      refine ⟨19592447936214753108268915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26123263914953004144358553 19592447936214753108268915)
      ·
        refine ⟨29388671904322129662403373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592447936214753108268915 29388671904322129662403373)
        ·
          refine ⟨11020751964120798623401265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29388671904322129662403373 11020751964120798623401265)
          ·
            refine ⟨8265563973090598967550949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11020751964120798623401265 8265563973090598967550949)
            ·
              refine ⟨1549793244954487306415803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8265563973090598967550949 1549793244954487306415803)
              ·
                refine ⟨2324689867431730959623705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549793244954487306415803 2324689867431730959623705)
                ·
                  refine ⟨1743517400573798219717779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2324689867431730959623705 1743517400573798219717779)
                  ·
                    refine ⟨2615276100860697329576669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743517400573798219717779 2615276100860697329576669)
                    ·
                      refine ⟨980728537822761498591251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615276100860697329576669 980728537822761498591251)
                      ·
                        rfl

theorem cell23_1909962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_1909962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909962 prefixEnd_1909962 := by exact prefixLift 1909962
  have htrace : WordTrace (prefixWord ++ tailWord_1909962) baseStart_1909962 baseEnd_1909962 := by
    simpa [prefixWord, tailWord_1909962, baseEnd_1909962] using wordTrace_append hprefix tailTrace_1909962
  have hstable : (prefixWord ++ tailWord_1909962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909962).length < 2 ^ (prefixWord ++ tailWord_1909962).sum := by decide
  have hdescent : baseEnd_1909962 < baseStart_1909962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909971 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3]
def baseStart_1909971 : Nat := 118140960795 + 1909971 * 2 ^ 59
def prefixEnd_1909971 : Nat := 4983230072969 + 3 ^ 40 * 1909971 * 2
def baseEnd_1909971 : Nat := 980733159148651963378709

theorem tailTrace_1909971 : CollatzResearch.WordTrace tailWord_1909971 prefixEnd_1909971 980733159148651963378709 := by
  unfold tailWord_1909971
  simp only [CollatzResearch.WordTrace]
  refine ⟨69662365363508738922033767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46441576909005825948022511 69662365363508738922033767)
  ·
    refine ⟨104493548045263108383050651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69662365363508738922033767 104493548045263108383050651)
    ·
      refine ⟨156740322067894662574575977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104493548045263108383050651 156740322067894662574575977)
      ·
        refine ⟨117555241550920996930931983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156740322067894662574575977 117555241550920996930931983)
        ·
          refine ⟨176332862326381495396397975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117555241550920996930931983 176332862326381495396397975)
          ·
            refine ⟨264499293489572243094596963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176332862326381495396397975 264499293489572243094596963)
            ·
              refine ⟨396748940234358364641895445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264499293489572243094596963 396748940234358364641895445)
              ·
                refine ⟨18597606573485548342588849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396748940234358364641895445 18597606573485548342588849)
                ·
                  refine ⟨13948204930114161256941637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18597606573485548342588849 13948204930114161256941637)
                  ·
                    refine ⟨2615288424396405235676557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13948204930114161256941637 2615288424396405235676557)
                    ·
                      refine ⟨980733159148651963378709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615288424396405235676557 980733159148651963378709)
                      ·
                        rfl

theorem cell23_1909971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_1909971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909971 prefixEnd_1909971 := by exact prefixLift 1909971
  have htrace : WordTrace (prefixWord ++ tailWord_1909971) baseStart_1909971 baseEnd_1909971 := by
    simpa [prefixWord, tailWord_1909971, baseEnd_1909971] using wordTrace_append hprefix tailTrace_1909971
  have hstable : (prefixWord ++ tailWord_1909971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909971).length < 2 ^ (prefixWord ++ tailWord_1909971).sum := by decide
  have hdescent : baseEnd_1909971 < baseStart_1909971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909985 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_1909985 : Nat := 118140960795 + 1909985 * 2 ^ 59
def prefixEnd_1909985 : Nat := 4983230072969 + 3 ^ 40 * 1909985 * 2
def baseEnd_1909985 : Nat := 980740347877814908603645

theorem tailTrace_1909985 : CollatzResearch.WordTrace tailWord_1909985 prefixEnd_1909985 980740347877814908603645 := by
  unfold tailWord_1909985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69662875985458019313043409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46441917323638679542028939 69662875985458019313043409)
  ·
    refine ⟨52247156989093514484782557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69662875985458019313043409 52247156989093514484782557)
    ·
      refine ⟨19592683870910067931793459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52247156989093514484782557 19592683870910067931793459)
      ·
        refine ⟨29389025806365101897690189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592683870910067931793459 29389025806365101897690189)
        ·
          refine ⟨11020884677386913211633821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29389025806365101897690189 11020884677386913211633821)
          ·
            refine ⟨4132831754020092454362683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11020884677386913211633821 4132831754020092454362683)
            ·
              refine ⟨6199247631030138681544025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132831754020092454362683 6199247631030138681544025)
              ·
                refine ⟨4649435723272604011158019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199247631030138681544025 4649435723272604011158019)
                ·
                  refine ⟨6974153584908906016737029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649435723272604011158019 6974153584908906016737029)
                  ·
                    refine ⟨1307653797170419878138193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6974153584908906016737029 1307653797170419878138193)
                    ·
                      refine ⟨980740347877814908603645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307653797170419878138193 980740347877814908603645)
                      ·
                        rfl

theorem cell23_1909985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_1909985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909985 prefixEnd_1909985 := by exact prefixLift 1909985
  have htrace : WordTrace (prefixWord ++ tailWord_1909985) baseStart_1909985 baseEnd_1909985 := by
    simpa [prefixWord, tailWord_1909985, baseEnd_1909985] using wordTrace_append hprefix tailTrace_1909985
  have hstable : (prefixWord ++ tailWord_1909985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909985).length < 2 ^ (prefixWord ++ tailWord_1909985).sum := by decide
  have hdescent : baseEnd_1909985 < baseStart_1909985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909989 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1909989 : Nat := 118140960795 + 1909989 * 2 ^ 59
def prefixEnd_1909989 : Nat := 4983230072969 + 3 ^ 40 * 1909989 * 2
def baseEnd_1909989 : Nat := 980742401800432892953627

theorem tailTrace_1909989 : CollatzResearch.WordTrace tailWord_1909989 prefixEnd_1909989 980742401800432892953627 := by
  unfold tailWord_1909989
  simp only [CollatzResearch.WordTrace]
  refine ⟨69663021877443527996189021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46442014584962351997459347 69663021877443527996189021)
  ·
    refine ⟨26123633204041322998570883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69663021877443527996189021 26123633204041322998570883)
    ·
      refine ⟨39185449806061984497856325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26123633204041322998570883 39185449806061984497856325)
      ·
        refine ⟨7347271838636622093348061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39185449806061984497856325 7347271838636622093348061)
        ·
          refine ⟨2755226939488733285005523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7347271838636622093348061 2755226939488733285005523)
          ·
            refine ⟨4132840409233099927508285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755226939488733285005523 4132840409233099927508285)
            ·
              refine ⟨1549815153462412472815607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132840409233099927508285 1549815153462412472815607)
              ·
                refine ⟨2324722730193618709223411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549815153462412472815607 2324722730193618709223411)
                ·
                  refine ⟨3487084095290428063835117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324722730193618709223411 3487084095290428063835117)
                  ·
                    refine ⟨1307656535733910523938169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487084095290428063835117 1307656535733910523938169)
                    ·
                      refine ⟨980742401800432892953627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307656535733910523938169 980742401800432892953627)
                      ·
                        rfl

theorem cell23_1909989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1909989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909989 prefixEnd_1909989 := by exact prefixLift 1909989
  have htrace : WordTrace (prefixWord ++ tailWord_1909989) baseStart_1909989 baseEnd_1909989 := by
    simpa [prefixWord, tailWord_1909989, baseEnd_1909989] using wordTrace_append hprefix tailTrace_1909989
  have hstable : (prefixWord ++ tailWord_1909989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909989).length < 2 ^ (prefixWord ++ tailWord_1909989).sum := by decide
  have hdescent : baseEnd_1909989 < baseStart_1909989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910021 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1910021 : Nat := 118140960795 + 1910021 * 2 ^ 59
def prefixEnd_1910021 : Nat := 4983230072969 + 3 ^ 40 * 1910021 * 2
def baseEnd_1910021 : Nat := 326919611060458922584493

theorem tailTrace_1910021 : CollatzResearch.WordTrace tailWord_1910021 prefixEnd_1910021 326919611060458922584493 := by
  unfold tailWord_1910021
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664189013327597461353917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46442792675551731640902611 69664189013327597461353917)
  ·
    refine ⟨26124070879997849048007719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69664189013327597461353917 26124070879997849048007719)
    ·
      refine ⟨39186106319996773572011579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26124070879997849048007719 39186106319996773572011579)
      ·
        refine ⟨58779159479995160358017369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39186106319996773572011579 58779159479995160358017369)
        ·
          refine ⟨44084369609996370268513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58779159479995160358017369 44084369609996370268513027)
          ·
            refine ⟨66126554414994555402769541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44084369609996370268513027 66126554414994555402769541)
            ·
              refine ⟨12398728952811479138019289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66126554414994555402769541 12398728952811479138019289)
              ·
                refine ⟨9299046714608609353514467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12398728952811479138019289 9299046714608609353514467)
                ·
                  refine ⟨13948570071912914030271701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299046714608609353514467 13948570071912914030271701)
                  ·
                    refine ⟨326919611060458922584493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13948570071912914030271701 326919611060458922584493)
                    ·
                      rfl

theorem cell23_1910021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1910021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910021 prefixEnd_1910021 := by exact prefixLift 1910021
  have htrace : WordTrace (prefixWord ++ tailWord_1910021) baseStart_1910021 baseEnd_1910021 := by
    simpa [prefixWord, tailWord_1910021, baseEnd_1910021] using wordTrace_append hprefix tailTrace_1910021
  have hstable : (prefixWord ++ tailWord_1910021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910021).length < 2 ^ (prefixWord ++ tailWord_1910021).sum := by decide
  have hdescent : baseEnd_1910021 < baseStart_1910021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910119 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1910119 : Nat := 118140960795 + 1910119 * 2 ^ 59
def prefixEnd_1910119 : Nat := 4983230072969 + 3 ^ 40 * 1910119 * 2
def baseEnd_1910119 : Nat := 326936384761839128109343

theorem tailTrace_1910119 : CollatzResearch.WordTrace tailWord_1910119 prefixEnd_1910119 326936384761839128109343 := by
  unfold tailWord_1910119
  simp only [CollatzResearch.WordTrace]
  refine ⟨69667763366972560198421411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46445175577981706798947607 69667763366972560198421411)
  ·
    refine ⟨104501645050458840297632117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69667763366972560198421411 104501645050458840297632117)
    ·
      refine ⟨9797029223480516277903011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104501645050458840297632117 9797029223480516277903011)
      ·
        refine ⟨14695543835220774416854517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9797029223480516277903011 14695543835220774416854517)
        ·
          refine ⟨1377707234551947601580111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14695543835220774416854517 1377707234551947601580111)
          ·
            refine ⟨2066560851827921402370167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377707234551947601580111 2066560851827921402370167)
            ·
              refine ⟨3099841277741882103555251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066560851827921402370167 3099841277741882103555251)
              ·
                refine ⟨4649761916612823155332877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099841277741882103555251 4649761916612823155332877)
                ·
                  refine ⟨1743660718729808683249829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4649761916612823155332877 1743660718729808683249829)
                  ·
                    refine ⟨326936384761839128109343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743660718729808683249829 326936384761839128109343)
                    ·
                      rfl

theorem cell23_1910119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1910119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910119 prefixEnd_1910119 := by exact prefixLift 1910119
  have htrace : WordTrace (prefixWord ++ tailWord_1910119) baseStart_1910119 baseEnd_1910119 := by
    simpa [prefixWord, tailWord_1910119, baseEnd_1910119] using wordTrace_append hprefix tailTrace_1910119
  have hstable : (prefixWord ++ tailWord_1910119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910119).length < 2 ^ (prefixWord ++ tailWord_1910119).sum := by decide
  have hdescent : baseEnd_1910119 < baseStart_1910119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910128 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_1910128 : Nat := 118140960795 + 1910128 * 2 ^ 59
def prefixEnd_1910128 : Nat := 4983230072969 + 3 ^ 40 * 1910128 * 2
def baseEnd_1910128 : Nat := 326937925203802616371829

theorem tailTrace_1910128 : CollatzResearch.WordTrace tailWord_1910128 prefixEnd_1910128 326937925203802616371829 := by
  unfold tailWord_1910128
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834045811969977367749519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46445394415959969823666025 34834045811969977367749519)
  ·
    refine ⟨52251068717954966051624279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34834045811969977367749519 52251068717954966051624279)
    ·
      refine ⟨78376603076932449077436419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52251068717954966051624279 78376603076932449077436419)
      ·
        refine ⟨117564904615398673616154629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78376603076932449077436419 117564904615398673616154629)
        ·
          refine ⟨22043419615387251303028993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117564904615398673616154629 22043419615387251303028993)
          ·
            refine ⟨16532564711540438477271745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22043419615387251303028993 16532564711540438477271745)
            ·
              refine ⟨12399423533655328857953809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532564711540438477271745 12399423533655328857953809)
              ·
                refine ⟨9299567650241496643465357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12399423533655328857953809 9299567650241496643465357)
                ·
                  refine ⟨3487337868840561241299509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9299567650241496643465357 3487337868840561241299509)
                  ·
                    refine ⟨326937925203802616371829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3487337868840561241299509 326937925203802616371829)
                    ·
                      rfl

theorem cell23_1910128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_1910128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910128 prefixEnd_1910128 := by exact prefixLift 1910128
  have htrace : WordTrace (prefixWord ++ tailWord_1910128) baseStart_1910128 baseEnd_1910128 := by
    simpa [prefixWord, tailWord_1910128, baseEnd_1910128] using wordTrace_append hprefix tailTrace_1910128
  have hstable : (prefixWord ++ tailWord_1910128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910128).length < 2 ^ (prefixWord ++ tailWord_1910128).sum := by decide
  have hdescent : baseEnd_1910128 < baseStart_1910128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910135 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_1910135 : Nat := 118140960795 + 1910135 * 2 ^ 59
def prefixEnd_1910135 : Nat := 4983230072969 + 3 ^ 40 * 1910135 * 2
def baseEnd_1910135 : Nat := 980817369975989321727955

theorem tailTrace_1910135 : CollatzResearch.WordTrace tailWord_1910135 prefixEnd_1910135 980817369975989321727955 := by
  unfold tailWord_1910135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69668346934914594931003859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46445564623276396620669239 69668346934914594931003859)
  ·
    refine ⟨104502520402371892396505789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69668346934914594931003859 104502520402371892396505789)
    ·
      refine ⟨39188445150889459648689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104502520402371892396505789 39188445150889459648689671)
      ·
        refine ⟨58782667726334189473034507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39188445150889459648689671 58782667726334189473034507)
        ·
          refine ⟨88174001589501284209551761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58782667726334189473034507 88174001589501284209551761)
          ·
            refine ⟨66130501192125963157163821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88174001589501284209551761 66130501192125963157163821)
            ·
              refine ⟨24798937947047236183936433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66130501192125963157163821 24798937947047236183936433)
              ·
                refine ⟨18599203460285427137952325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24798937947047236183936433 18599203460285427137952325)
                ·
                  refine ⟨3487350648803517588366061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18599203460285427137952325 3487350648803517588366061)
                  ·
                    refine ⟨1307756493301319095637273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487350648803517588366061 1307756493301319095637273)
                    ·
                      refine ⟨980817369975989321727955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307756493301319095637273 980817369975989321727955)
                      ·
                        rfl

theorem cell23_1910135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_1910135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910135 prefixEnd_1910135 := by exact prefixLift 1910135
  have htrace : WordTrace (prefixWord ++ tailWord_1910135) baseStart_1910135 baseEnd_1910135 := by
    simpa [prefixWord, tailWord_1910135, baseEnd_1910135] using wordTrace_append hprefix tailTrace_1910135
  have hstable : (prefixWord ++ tailWord_1910135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910135).length < 2 ^ (prefixWord ++ tailWord_1910135).sum := by decide
  have hdescent : baseEnd_1910135 < baseStart_1910135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910152 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1910152 : Nat := 118140960795 + 1910152 * 2 ^ 59
def prefixEnd_1910152 : Nat := 4983230072969 + 3 ^ 40 * 1910152 * 2
def baseEnd_1910152 : Nat := 980826099147115755215377

theorem tailTrace_1910152 : CollatzResearch.WordTrace tailWord_1910152 prefixEnd_1910152 980826099147115755215377 := by
  unfold tailWord_1910152
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834483487926503417186355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46445977983902004556248473 34834483487926503417186355)
  ·
    refine ⟨52251725231889755125779533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34834483487926503417186355 52251725231889755125779533)
    ·
      refine ⟨19594396961958658172167325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52251725231889755125779533 19594396961958658172167325)
      ·
        refine ⟨7347898860734496814562747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19594396961958658172167325 7347898860734496814562747)
        ·
          refine ⟨11021848291101745221844121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347898860734496814562747 11021848291101745221844121)
          ·
            refine ⟨8266386218326308916383091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021848291101745221844121 8266386218326308916383091)
            ·
              refine ⟨12399579327489463374574637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266386218326308916383091 12399579327489463374574637)
              ·
                refine ⟨4649842247808548765465489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399579327489463374574637 4649842247808548765465489)
                ·
                  refine ⟨3487381685856411574099117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4649842247808548765465489 3487381685856411574099117)
                  ·
                    refine ⟨1307768132196154340287169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487381685856411574099117 1307768132196154340287169)
                    ·
                      refine ⟨980826099147115755215377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307768132196154340287169 980826099147115755215377)
                      ·
                        rfl

theorem cell23_1910152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1910152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910152 prefixEnd_1910152 := by exact prefixLift 1910152
  have htrace : WordTrace (prefixWord ++ tailWord_1910152) baseStart_1910152 baseEnd_1910152 := by
    simpa [prefixWord, tailWord_1910152, baseEnd_1910152] using wordTrace_append hprefix tailTrace_1910152
  have hstable : (prefixWord ++ tailWord_1910152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910152).length < 2 ^ (prefixWord ++ tailWord_1910152).sum := by decide
  have hdescent : baseEnd_1910152 < baseStart_1910152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910165 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_1910165 : Nat := 118140960795 + 1910165 * 2 ^ 59
def prefixEnd_1910165 : Nat := 4983230072969 + 3 ^ 40 * 1910165 * 2
def baseEnd_1910165 : Nat := 980832774395624204352817

theorem tailTrace_1910165 : CollatzResearch.WordTrace tailWord_1910165 prefixEnd_1910165 980832774395624204352817 := by
  unfold tailWord_1910165
  simp only [CollatzResearch.WordTrace]
  refine ⟨69669441124805910054595949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46446294083203940036397299 69669441124805910054595949)
  ·
    refine ⟨26126040421802216270473481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69669441124805910054595949 26126040421802216270473481)
    ·
      refine ⟨19594530316351662202855111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26126040421802216270473481 19594530316351662202855111)
      ·
        refine ⟨29391795474527493304282667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19594530316351662202855111 29391795474527493304282667)
        ·
          refine ⟨44087693211791239956424001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29391795474527493304282667 44087693211791239956424001)
          ·
            refine ⟨33065769908843429967318001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44087693211791239956424001 33065769908843429967318001)
            ·
              refine ⟨24799327431632572475488501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33065769908843429967318001 24799327431632572475488501)
              ·
                refine ⟨2324936946715553669577047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24799327431632572475488501 2324936946715553669577047)
                ·
                  refine ⟨3487405420073330504365571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324936946715553669577047 3487405420073330504365571)
                  ·
                    refine ⟨5231108130109995756548357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3487405420073330504365571 5231108130109995756548357)
                    ·
                      refine ⟨980832774395624204352817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5231108130109995756548357 980832774395624204352817)
                      ·
                        rfl

theorem cell23_1910165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_1910165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910165 prefixEnd_1910165 := by exact prefixLift 1910165
  have htrace : WordTrace (prefixWord ++ tailWord_1910165) baseStart_1910165 baseEnd_1910165 := by
    simpa [prefixWord, tailWord_1910165, baseEnd_1910165] using wordTrace_append hprefix tailTrace_1910165
  have hstable : (prefixWord ++ tailWord_1910165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910165).length < 2 ^ (prefixWord ++ tailWord_1910165).sum := by decide
  have hdescent : baseEnd_1910165 < baseStart_1910165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910188 : List Nat := [2, 2, 1, 1, 1, 1, 7, 8]
def baseStart_1910188 : Nat := 118140960795 + 1910188 * 2 ^ 59
def prefixEnd_1910188 : Nat := 4983230072969 + 3 ^ 40 * 1910188 * 2
def baseEnd_1910188 : Nat := 36327577201876948680193

theorem tailTrace_1910188 : CollatzResearch.WordTrace tailWord_1910188 prefixEnd_1910188 36327577201876948680193 := by
  unfold tailWord_1910188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835140001861292491341609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46446853335815056655122145 34835140001861292491341609)
  ·
    refine ⟨26126355001395969368506207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34835140001861292491341609 26126355001395969368506207)
    ·
      refine ⟨39189532502093954052759311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26126355001395969368506207 39189532502093954052759311)
      ·
        refine ⟨58784298753140931079138967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39189532502093954052759311 58784298753140931079138967)
        ·
          refine ⟨88176448129711396618708451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58784298753140931079138967 88176448129711396618708451)
          ·
            refine ⟨132264672194567094928062677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88176448129711396618708451 132264672194567094928062677)
            ·
              refine ⟨3099953254560166287376469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132264672194567094928062677 3099953254560166287376469)
              ·
                refine ⟨36327577201876948680193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3099953254560166287376469 36327577201876948680193)
                ·
                  rfl

theorem cell23_1910188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 8].length) (baseStart_1910188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910188 prefixEnd_1910188 := by exact prefixLift 1910188
  have htrace : WordTrace (prefixWord ++ tailWord_1910188) baseStart_1910188 baseEnd_1910188 := by
    simpa [prefixWord, tailWord_1910188, baseEnd_1910188] using wordTrace_append hprefix tailTrace_1910188
  have hstable : (prefixWord ++ tailWord_1910188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910188).length < 2 ^ (prefixWord ++ tailWord_1910188).sum := by decide
  have hdescent : baseEnd_1910188 < baseStart_1910188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910205 : List Nat := [1, 4, 1, 2, 2, 1, 5, 7]
def baseStart_1910205 : Nat := 118140960795 + 1910205 * 2 ^ 59
def prefixEnd_1910205 : Nat := 4983230072969 + 3 ^ 40 * 1910205 * 2
def baseEnd_1910205 : Nat := 36327900504511261031579

theorem tailTrace_1910205 : CollatzResearch.WordTrace tailWord_1910205 prefixEnd_1910205 36327900504511261031579 := by
  unfold tailWord_1910205
  simp only [CollatzResearch.WordTrace]
  refine ⟨69670900044660996886052069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46447266696440664590701379 69670900044660996886052069)
  ·
    refine ⟨13063293758373936916134763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69670900044660996886052069 13063293758373936916134763)
    ·
      refine ⟨19594940637560905374202145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063293758373936916134763 19594940637560905374202145)
      ·
        refine ⟨14696205478170679030651609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19594940637560905374202145 14696205478170679030651609)
        ·
          refine ⟨11022154108628009272988707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14696205478170679030651609 11022154108628009272988707)
          ·
            refine ⟨16533231162942013909483061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022154108628009272988707 16533231162942013909483061)
            ·
              refine ⟨1549990421525813804014037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16533231162942013909483061 1549990421525813804014037)
              ·
                refine ⟨36327900504511261031579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1549990421525813804014037 36327900504511261031579)
                ·
                  rfl

theorem cell23_1910205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 7].length) (baseStart_1910205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910205 prefixEnd_1910205 := by exact prefixLift 1910205
  have htrace : WordTrace (prefixWord ++ tailWord_1910205) baseStart_1910205 baseEnd_1910205 := by
    simpa [prefixWord, tailWord_1910205, baseEnd_1910205] using wordTrace_append hprefix tailTrace_1910205
  have hstable : (prefixWord ++ tailWord_1910205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910205).length < 2 ^ (prefixWord ++ tailWord_1910205).sum := by decide
  have hdescent : baseEnd_1910205 < baseStart_1910205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910212 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1910212 : Nat := 118140960795 + 1910212 * 2 ^ 59
def prefixEnd_1910212 : Nat := 4983230072969 + 3 ^ 40 * 1910212 * 2
def baseEnd_1910212 : Nat := 980856907986385520465101

theorem tailTrace_1910212 : CollatzResearch.WordTrace tailWord_1910212 prefixEnd_1910212 980856907986385520465101 := by
  unfold tailWord_1910212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835577677817818540778445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46447436903757091387704593 34835577677817818540778445)
  ·
    refine ⟨13063341629181681952791917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34835577677817818540778445 13063341629181681952791917)
    ·
      refine ⟨4898753110943130732296969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13063341629181681952791917 4898753110943130732296969)
      ·
        refine ⟨3674064833207348049222727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898753110943130732296969 3674064833207348049222727)
        ·
          refine ⟨5511097249811022073834091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674064833207348049222727 5511097249811022073834091)
          ·
            refine ⟨8266645874716533110751137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511097249811022073834091 8266645874716533110751137)
            ·
              refine ⟨6199984406037399833063353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266645874716533110751137 6199984406037399833063353)
              ·
                refine ⟨4649988304528049874797515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199984406037399833063353 4649988304528049874797515)
                ·
                  refine ⟨6974982456792074812196273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649988304528049874797515 6974982456792074812196273)
                  ·
                    refine ⟨5231236842594056109147205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974982456792074812196273 5231236842594056109147205)
                    ·
                      refine ⟨980856907986385520465101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5231236842594056109147205 980856907986385520465101)
                      ·
                        rfl

theorem cell23_1910212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1910212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910212 prefixEnd_1910212 := by exact prefixLift 1910212
  have htrace : WordTrace (prefixWord ++ tailWord_1910212) baseStart_1910212 baseEnd_1910212 := by
    simpa [prefixWord, tailWord_1910212, baseEnd_1910212] using wordTrace_append hprefix tailTrace_1910212
  have hstable : (prefixWord ++ tailWord_1910212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910212).length < 2 ^ (prefixWord ++ tailWord_1910212).sum := by decide
  have hdescent : baseEnd_1910212 < baseStart_1910212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910215 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1910215 : Nat := 118140960795 + 1910215 * 2 ^ 59
def prefixEnd_1910215 : Nat := 4983230072969 + 3 ^ 40 * 1910215 * 2
def baseEnd_1910215 : Nat := 980858448428349008727587

theorem tailTrace_1910215 : CollatzResearch.WordTrace tailWord_1910215 prefixEnd_1910215 980858448428349008727587 := by
  unfold tailWord_1910215
  simp only [CollatzResearch.WordTrace]
  refine ⟨69671264774624768593916099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46447509849749845729277399 69671264774624768593916099)
  ·
    refine ⟨104506897161937152890874149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69671264774624768593916099 104506897161937152890874149)
    ·
      refine ⟨19595043217863216167038903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104506897161937152890874149 19595043217863216167038903)
      ·
        refine ⟨29392564826794824250558355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595043217863216167038903 29392564826794824250558355)
        ·
          refine ⟨44088847240192236375837533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29392564826794824250558355 44088847240192236375837533)
          ·
            refine ⟨16533317715072088640939075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44088847240192236375837533 16533317715072088640939075)
            ·
              refine ⟨24799976572608132961408613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16533317715072088640939075 24799976572608132961408613)
              ·
                refine ⟨4649995607364024930264115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24799976572608132961408613 4649995607364024930264115)
                ·
                  refine ⟨6974993411046037395396173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649995607364024930264115 6974993411046037395396173)
                  ·
                    refine ⟨2615622529142264023273565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6974993411046037395396173 2615622529142264023273565)
                    ·
                      refine ⟨980858448428349008727587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615622529142264023273565 980858448428349008727587)
                      ·
                        rfl

theorem cell23_1910215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1910215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910215 prefixEnd_1910215 := by exact prefixLift 1910215
  have htrace : WordTrace (prefixWord ++ tailWord_1910215) baseStart_1910215 baseEnd_1910215 := by
    simpa [prefixWord, tailWord_1910215, baseEnd_1910215] using wordTrace_append hprefix tailTrace_1910215
  have hstable : (prefixWord ++ tailWord_1910215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910215).length < 2 ^ (prefixWord ++ tailWord_1910215).sum := by decide
  have hdescent : baseEnd_1910215 < baseStart_1910215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910216 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_1910216 : Nat := 118140960795 + 1910216 * 2 ^ 59
def prefixEnd_1910216 : Nat := 4983230072969 + 3 ^ 40 * 1910216 * 2
def baseEnd_1910216 : Nat := 980858961909003504815083

theorem tailTrace_1910216 : CollatzResearch.WordTrace tailWord_1910216 prefixEnd_1910216 980858961909003504815083 := by
  unfold tailWord_1910216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835650623810572882351251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46447534165080763843135001 34835650623810572882351251)
  ·
    refine ⟨52253475935715859323526877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34835650623810572882351251 52253475935715859323526877)
    ·
      refine ⟨19595053475893447246322579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52253475935715859323526877 19595053475893447246322579)
      ·
        refine ⟨29392580213840170869483869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595053475893447246322579 29392580213840170869483869)
        ·
          refine ⟨11022217580190064076056451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29392580213840170869483869 11022217580190064076056451)
          ·
            refine ⟨16533326370285096114084677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022217580190064076056451 16533326370285096114084677)
            ·
              refine ⟨3099998694428455521390877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16533326370285096114084677 3099998694428455521390877)
              ·
                refine ⟨1162499510410670820521579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3099998694428455521390877 1162499510410670820521579)
                ·
                  refine ⟨1743749265616006230782369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162499510410670820521579 1743749265616006230782369)
                  ·
                    refine ⟨1307811949212004673086777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1743749265616006230782369 1307811949212004673086777)
                    ·
                      refine ⟨980858961909003504815083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307811949212004673086777 980858961909003504815083)
                      ·
                        rfl

theorem cell23_1910216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_1910216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910216 prefixEnd_1910216 := by exact prefixLift 1910216
  have htrace : WordTrace (prefixWord ++ tailWord_1910216) baseStart_1910216 baseEnd_1910216 := by
    simpa [prefixWord, tailWord_1910216, baseEnd_1910216] using wordTrace_append hprefix tailTrace_1910216
  have hstable : (prefixWord ++ tailWord_1910216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910216).length < 2 ^ (prefixWord ++ tailWord_1910216).sum := by decide
  have hdescent : baseEnd_1910216 < baseStart_1910216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910289 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_1910289 : Nat := 118140960795 + 1910289 * 2 ^ 59
def prefixEnd_1910289 : Nat := 4983230072969 + 3 ^ 40 * 1910289 * 2
def baseEnd_1910289 : Nat := 980896445996781719202247

theorem tailTrace_1910289 : CollatzResearch.WordTrace tailWord_1910289 prefixEnd_1910289 980896445996781719202247 := by
  unfold tailWord_1910289
  simp only [CollatzResearch.WordTrace]
  refine ⟨69673963776356679232109921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46449309184237786154739947 69673963776356679232109921)
  ·
    refine ⟨52255472832267509424082441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69673963776356679232109921 52255472832267509424082441)
    ·
      refine ⟨39191604624200632068061831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52255472832267509424082441 39191604624200632068061831)
      ·
        refine ⟨58787406936300948102092747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39191604624200632068061831 58787406936300948102092747)
        ·
          refine ⟨88181110404451422153139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58787406936300948102092747 88181110404451422153139121)
          ·
            refine ⟨66135832803338566614854341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88181110404451422153139121 66135832803338566614854341)
            ·
              refine ⟨12400468650625981240285189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66135832803338566614854341 12400468650625981240285189)
              ·
                refine ⟨2325087871992371482553473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12400468650625981240285189 2325087871992371482553473)
                ·
                  refine ⟨1743815903994278611915105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325087871992371482553473 1743815903994278611915105)
                  ·
                    refine ⟨1307861927995708958936329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1743815903994278611915105 1307861927995708958936329)
                    ·
                      refine ⟨980896445996781719202247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307861927995708958936329 980896445996781719202247)
                      ·
                        rfl

theorem cell23_1910289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_1910289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910289 prefixEnd_1910289 := by exact prefixLift 1910289
  have htrace : WordTrace (prefixWord ++ tailWord_1910289) baseStart_1910289 baseEnd_1910289 := by
    simpa [prefixWord, tailWord_1910289, baseEnd_1910289] using wordTrace_append hprefix tailTrace_1910289
  have hstable : (prefixWord ++ tailWord_1910289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910289).length < 2 ^ (prefixWord ++ tailWord_1910289).sum := by decide
  have hdescent : baseEnd_1910289 < baseStart_1910289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910335 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1910335 : Nat := 118140960795 + 1910335 * 2 ^ 59
def prefixEnd_1910335 : Nat := 4983230072969 + 3 ^ 40 * 1910335 * 2
def baseEnd_1910335 : Nat := 980920066106888539227035

theorem tailTrace_1910335 : CollatzResearch.WordTrace tailWord_1910335 prefixEnd_1910335 980920066106888539227035 := by
  unfold tailWord_1910335
  simp only [CollatzResearch.WordTrace]
  refine ⟨69675641534190029088284459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46450427689460019392189639 69675641534190029088284459)
  ·
    refine ⟨104513462301285043632426689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69675641534190029088284459 104513462301285043632426689)
    ·
      refine ⟨78385096725963782724320017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104513462301285043632426689 78385096725963782724320017)
      ·
        refine ⟨58788822544472837043240013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78385096725963782724320017 58788822544472837043240013)
        ·
          refine ⟨22045808454177313891215005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58788822544472837043240013 22045808454177313891215005)
          ·
            refine ⟨8267178170316492709205627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22045808454177313891215005 8267178170316492709205627)
            ·
              refine ⟨12400767255474739063808441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267178170316492709205627 12400767255474739063808441)
              ·
                refine ⟨9300575441606054297856331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12400767255474739063808441 9300575441606054297856331)
                ·
                  refine ⟨13950863162409081446784497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300575441606054297856331 13950863162409081446784497)
                  ·
                    refine ⟨10463147371806811085088373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13950863162409081446784497 10463147371806811085088373)
                    ·
                      refine ⟨980920066106888539227035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10463147371806811085088373 980920066106888539227035)
                      ·
                        rfl

theorem cell23_1910335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1910335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910335 prefixEnd_1910335 := by exact prefixLift 1910335
  have htrace : WordTrace (prefixWord ++ tailWord_1910335) baseStart_1910335 baseEnd_1910335 := by
    simpa [prefixWord, tailWord_1910335, baseEnd_1910335] using wordTrace_append hprefix tailTrace_1910335
  have hstable : (prefixWord ++ tailWord_1910335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910335).length < 2 ^ (prefixWord ++ tailWord_1910335).sum := by decide
  have hdescent : baseEnd_1910335 < baseStart_1910335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910372 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1910372 : Nat := 118140960795 + 1910372 * 2 ^ 59
def prefixEnd_1910372 : Nat := 4983230072969 + 3 ^ 40 * 1910372 * 2
def baseEnd_1910372 : Nat := 326979688297034964821455

theorem tailTrace_1910372 : CollatzResearch.WordTrace tailWord_1910372 prefixEnd_1910372 326979688297034964821455 := by
  unfold tailWord_1910372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34838495517527992203690685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46451327356703989604920913 34838495517527992203690685)
  ·
    refine ⟨13064435819072997076384007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34838495517527992203690685 13064435819072997076384007)
    ·
      refine ⟨19596653728609495614576011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13064435819072997076384007 19596653728609495614576011)
      ·
        refine ⟨29394980592914243421864017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19596653728609495614576011 29394980592914243421864017)
        ·
          refine ⟨22046235444685682566398013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29394980592914243421864017 22046235444685682566398013)
          ·
            refine ⟨8267338291757130962399255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22046235444685682566398013 8267338291757130962399255)
            ·
              refine ⟨12401007437635696443598883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267338291757130962399255 12401007437635696443598883)
              ·
                refine ⟨18601511156453544665398325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12401007437635696443598883 18601511156453544665398325)
                ·
                  refine ⟨1743891670917519812381093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18601511156453544665398325 1743891670917519812381093)
                  ·
                    refine ⟨326979688297034964821455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743891670917519812381093 326979688297034964821455)
                    ·
                      rfl

theorem cell23_1910372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1910372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910372 prefixEnd_1910372 := by exact prefixLift 1910372
  have htrace : WordTrace (prefixWord ++ tailWord_1910372) baseStart_1910372 baseEnd_1910372 := by
    simpa [prefixWord, tailWord_1910372, baseEnd_1910372] using wordTrace_append hprefix tailTrace_1910372
  have hstable : (prefixWord ++ tailWord_1910372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910372).length < 2 ^ (prefixWord ++ tailWord_1910372).sum := by decide
  have hdescent : baseEnd_1910372 < baseStart_1910372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910405 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1910405 : Nat := 118140960795 + 1910405 * 2 ^ 59
def prefixEnd_1910405 : Nat := 4983230072969 + 3 ^ 40 * 1910405 * 2
def baseEnd_1910405 : Nat := 980956009752703265351713

theorem tailTrace_1910405 : CollatzResearch.WordTrace tailWord_1910405 prefixEnd_1910405 980956009752703265351713 := by
  unfold tailWord_1910405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678194643936431043332669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46452129762624287362221779 69678194643936431043332669)
  ·
    refine ⟨26129322991476161641249751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69678194643936431043332669 26129322991476161641249751)
    ·
      refine ⟨39193984487214242461874627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26129322991476161641249751 39193984487214242461874627)
      ·
        refine ⟨58790976730821363692811941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39193984487214242461874627 58790976730821363692811941)
        ·
          refine ⟨11023308137029005692402239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58790976730821363692811941 11023308137029005692402239)
          ·
            refine ⟨16534962205543508538603359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023308137029005692402239 16534962205543508538603359)
            ·
              refine ⟨24802443308315262807905039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534962205543508538603359 24802443308315262807905039)
              ·
                refine ⟨37203664962472894211857559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24802443308315262807905039 37203664962472894211857559)
                ·
                  refine ⟨55805497443709341317786339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37203664962472894211857559 55805497443709341317786339)
                  ·
                    refine ⟨83708246165564011976679509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55805497443709341317786339 83708246165564011976679509)
                    ·
                      refine ⟨980956009752703265351713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 83708246165564011976679509 980956009752703265351713)
                      ·
                        rfl

theorem cell23_1910405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1910405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910405 prefixEnd_1910405 := by exact prefixLift 1910405
  have htrace : WordTrace (prefixWord ++ tailWord_1910405) baseStart_1910405 baseEnd_1910405 := by
    simpa [prefixWord, tailWord_1910405, baseEnd_1910405] using wordTrace_append hprefix tailTrace_1910405
  have hstable : (prefixWord ++ tailWord_1910405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910405).length < 2 ^ (prefixWord ++ tailWord_1910405).sum := by decide
  have hdescent : baseEnd_1910405 < baseStart_1910405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910463 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 1, 1, 3]
def baseStart_1910463 : Nat := 118140960795 + 1910463 * 2 ^ 59
def prefixEnd_1910463 : Nat := 4983230072969 + 3 ^ 40 * 1910463 * 2
def baseEnd_1910463 : Nat := 980985791630664038426447

theorem tailTrace_1910463 : CollatzResearch.WordTrace tailWord_1910463 prefixEnd_1910463 980985791630664038426447 := by
  unfold tailWord_1910463
  simp only [CollatzResearch.WordTrace]
  refine ⟨69680310077726306948944043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46453540051817537965962695 69680310077726306948944043)
  ·
    refine ⟨104520465116589460423416065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69680310077726306948944043 104520465116589460423416065)
    ·
      refine ⟨78390348837442095317562049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104520465116589460423416065 78390348837442095317562049)
      ·
        refine ⟨58792761628081571488171537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78390348837442095317562049 58792761628081571488171537)
        ·
          refine ⟨44094571221061178616128653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58792761628081571488171537 44094571221061178616128653)
          ·
            refine ⟨16535464207897941981048245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44094571221061178616128653 16535464207897941981048245)
            ·
              refine ⟨1550199769490432060723273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16535464207897941981048245 1550199769490432060723273)
              ·
                refine ⟨1162649827117824045542455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550199769490432060723273 1162649827117824045542455)
                ·
                  refine ⟨1743974740676736068313683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162649827117824045542455 1743974740676736068313683)
                  ·
                    refine ⟨2615962111015104102470525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743974740676736068313683 2615962111015104102470525)
                    ·
                      refine ⟨980985791630664038426447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615962111015104102470525 980985791630664038426447)
                      ·
                        rfl

theorem cell23_1910463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_1910463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910463 prefixEnd_1910463 := by exact prefixLift 1910463
  have htrace : WordTrace (prefixWord ++ tailWord_1910463) baseStart_1910463 baseEnd_1910463 := by
    simpa [prefixWord, tailWord_1910463, baseEnd_1910463] using wordTrace_append hprefix tailTrace_1910463
  have hstable : (prefixWord ++ tailWord_1910463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910463).length < 2 ^ (prefixWord ++ tailWord_1910463).sum := by decide
  have hdescent : baseEnd_1910463 < baseStart_1910463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910470 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1910470 : Nat := 118140960795 + 1910470 * 2 ^ 59
def prefixEnd_1910470 : Nat := 4983230072969 + 3 ^ 40 * 1910470 * 2
def baseEnd_1910470 : Nat := 108998820666138390115435

theorem tailTrace_1910470 : CollatzResearch.WordTrace tailWord_1910470 prefixEnd_1910470 108998820666138390115435 := by
  unfold tailWord_1910470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177517668396904598264027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46453710259133964762965909 2177517668396904598264027)
  ·
    refine ⟨3266276502595356897396041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177517668396904598264027 3266276502595356897396041)
    ·
      refine ⟨2449707376946517673047031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3266276502595356897396041 2449707376946517673047031)
      ·
        refine ⟨3674561065419776509570547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449707376946517673047031 3674561065419776509570547)
        ·
          refine ⟨5511841598129664764355821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674561065419776509570547 5511841598129664764355821)
          ·
            refine ⟨2066940599298624286633433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5511841598129664764355821 2066940599298624286633433)
            ·
              refine ⟨1550205449473968214975075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066940599298624286633433 1550205449473968214975075)
              ·
                refine ⟨2325308174210952322462613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550205449473968214975075 2325308174210952322462613)
                ·
                  refine ⟨108998820666138390115435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2325308174210952322462613 108998820666138390115435)
                  ·
                    rfl

theorem cell23_1910470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1910470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910470 prefixEnd_1910470 := by exact prefixLift 1910470
  have htrace : WordTrace (prefixWord ++ tailWord_1910470) baseStart_1910470 baseEnd_1910470 := by
    simpa [prefixWord, tailWord_1910470, baseEnd_1910470] using wordTrace_append hprefix tailTrace_1910470
  have hstable : (prefixWord ++ tailWord_1910470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910470).length < 2 ^ (prefixWord ++ tailWord_1910470).sum := by decide
  have hdescent : baseEnd_1910470 < baseStart_1910470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910472 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1910472 : Nat := 118140960795 + 1910472 * 2 ^ 59
def prefixEnd_1910472 : Nat := 4983230072969 + 3 ^ 40 * 1910472 * 2
def baseEnd_1910472 : Nat := 980990412956554503213905

theorem tailTrace_1910472 : CollatzResearch.WordTrace tailWord_1910472 prefixEnd_1910472 980990412956554503213905 := by
  unfold tailWord_1910472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840319167346850743010835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46453758889795800990681113 34840319167346850743010835)
  ·
    refine ⟨52260478751020276114516253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34840319167346850743010835 52260478751020276114516253)
    ·
      refine ⟨19597679531632603542943595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52260478751020276114516253 19597679531632603542943595)
      ·
        refine ⟨29396519297448905314415393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597679531632603542943595 29396519297448905314415393)
        ·
          refine ⟨22047389473086678985811545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29396519297448905314415393 22047389473086678985811545)
          ·
            refine ⟨16535542104815009239358659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22047389473086678985811545 16535542104815009239358659)
            ·
              refine ⟨24803313157222513859037989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16535542104815009239358659 24803313157222513859037989)
              ·
                refine ⟨4650621216979221348569623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24803313157222513859037989 4650621216979221348569623)
                ·
                  refine ⟨6975931825468832022854435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650621216979221348569623 6975931825468832022854435)
                  ·
                    refine ⟨10463897738203248034281653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975931825468832022854435 10463897738203248034281653)
                    ·
                      refine ⟨980990412956554503213905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10463897738203248034281653 980990412956554503213905)
                      ·
                        rfl

theorem cell23_1910472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1910472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910472 prefixEnd_1910472 := by exact prefixLift 1910472
  have htrace : WordTrace (prefixWord ++ tailWord_1910472) baseStart_1910472 baseEnd_1910472 := by
    simpa [prefixWord, tailWord_1910472, baseEnd_1910472] using wordTrace_append hprefix tailTrace_1910472
  have hstable : (prefixWord ++ tailWord_1910472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910472).length < 2 ^ (prefixWord ++ tailWord_1910472).sum := by decide
  have hdescent : baseEnd_1910472 < baseStart_1910472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910489 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1910489 : Nat := 118140960795 + 1910489 * 2 ^ 59
def prefixEnd_1910489 : Nat := 4983230072969 + 3 ^ 40 * 1910489 * 2
def baseEnd_1910489 : Nat := 980999142127680936701327

theorem tailTrace_1910489 : CollatzResearch.WordTrace tailWord_1910489 prefixEnd_1910489 980999142127680936701327 := by
  unfold tailWord_1910489
  simp only [CollatzResearch.WordTrace]
  refine ⟨69681258375632113389390521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46454172250421408926260347 69681258375632113389390521)
  ·
    refine ⟨52260943781724085042042891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69681258375632113389390521 52260943781724085042042891)
    ·
      refine ⟨78391415672586127563064337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52260943781724085042042891 78391415672586127563064337)
      ·
        refine ⟨58793561754439595672298253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78391415672586127563064337 58793561754439595672298253)
        ·
          refine ⟨22047585657914848377111845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58793561754439595672298253 22047585657914848377111845)
          ·
            refine ⟨4133922310859034070708471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22047585657914848377111845 4133922310859034070708471)
            ·
              refine ⟨6200883466288551106062707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133922310859034070708471 6200883466288551106062707)
              ·
                refine ⟨9301325199432826659094061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200883466288551106062707 9301325199432826659094061)
                ·
                  refine ⟨3487996949787309997160273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9301325199432826659094061 3487996949787309997160273)
                  ·
                    refine ⟨2615997712340482497870205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3487996949787309997160273 2615997712340482497870205)
                    ·
                      refine ⟨980999142127680936701327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2615997712340482497870205 980999142127680936701327)
                      ·
                        rfl

theorem cell23_1910489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1910489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910489 prefixEnd_1910489 := by exact prefixLift 1910489
  have htrace : WordTrace (prefixWord ++ tailWord_1910489) baseStart_1910489 baseEnd_1910489 := by
    simpa [prefixWord, tailWord_1910489, baseEnd_1910489] using wordTrace_append hprefix tailTrace_1910489
  have hstable : (prefixWord ++ tailWord_1910489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910489).length < 2 ^ (prefixWord ++ tailWord_1910489).sum := by decide
  have hdescent : baseEnd_1910489 < baseStart_1910489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910519 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1910519 : Nat := 118140960795 + 1910519 * 2 ^ 59
def prefixEnd_1910519 : Nat := 4983230072969 + 3 ^ 40 * 1910519 * 2
def baseEnd_1910519 : Nat := 981014546547315819326189

theorem tailTrace_1910519 : CollatzResearch.WordTrace tailWord_1910519 prefixEnd_1910519 981014546547315819326189 := by
  unfold tailWord_1910519
  simp only [CollatzResearch.WordTrace]
  refine ⟨69682352565523428512982611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46454901710348952341988407 69682352565523428512982611)
  ·
    refine ⟨104523528848285142769473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69682352565523428512982611 104523528848285142769473917)
    ·
      refine ⟨39196323318106928538552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104523528848285142769473917 39196323318106928538552719)
      ·
        refine ⟨58794484977160392807829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39196323318106928538552719 58794484977160392807829079)
        ·
          refine ⟨88191727465740589211743619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58794484977160392807829079 88191727465740589211743619)
          ·
            refine ⟨132287591198610883817615429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88191727465740589211743619 132287591198610883817615429)
            ·
              refine ⟨24803923349739540715802893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132287591198610883817615429 24803923349739540715802893)
              ·
                refine ⟨9301471256152327768426085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24803923349739540715802893 9301471256152327768426085)
                ·
                  refine ⟨1744025860528561456579891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9301471256152327768426085 1744025860528561456579891)
                  ·
                    refine ⟨2616038790792842184869837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1744025860528561456579891 2616038790792842184869837)
                    ·
                      refine ⟨981014546547315819326189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2616038790792842184869837 981014546547315819326189)
                      ·
                        rfl

theorem cell23_1910519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1910519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910519 prefixEnd_1910519 := by exact prefixLift 1910519
  have htrace : WordTrace (prefixWord ++ tailWord_1910519) baseStart_1910519 baseEnd_1910519 := by
    simpa [prefixWord, tailWord_1910519, baseEnd_1910519] using wordTrace_append hprefix tailTrace_1910519
  have hstable : (prefixWord ++ tailWord_1910519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910519).length < 2 ^ (prefixWord ++ tailWord_1910519).sum := by decide
  have hdescent : baseEnd_1910519 < baseStart_1910519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910526 : List Nat := [4, 2, 2, 1, 3, 2, 1, 8]
def baseStart_1910526 : Nat := 118140960795 + 1910526 * 2 ^ 59
def prefixEnd_1910526 : Nat := 4983230072969 + 3 ^ 40 * 1910526 * 2
def baseEnd_1910526 : Nat := 36334005218959158960691

theorem tailTrace_1910526 : CollatzResearch.WordTrace tailWord_1910526 prefixEnd_1910526 36334005218959158960691 := by
  unfold tailWord_1910526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710325984562258588560929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46455071917665379138991621 8710325984562258588560929)
  ·
    refine ⟨6532744488421693941420697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8710325984562258588560929 6532744488421693941420697)
    ·
      refine ⟨4899558366316270456065523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6532744488421693941420697 4899558366316270456065523)
      ·
        refine ⟨7349337549474405684098285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899558366316270456065523 7349337549474405684098285)
        ·
          refine ⟨2756001581052902131536857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7349337549474405684098285 2756001581052902131536857)
          ·
            refine ⟨2067001185789676598652643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756001581052902131536857 2067001185789676598652643)
            ·
              refine ⟨3100501778684514897978965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067001185789676598652643 3100501778684514897978965)
              ·
                refine ⟨36334005218959158960691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3100501778684514897978965 36334005218959158960691)
                ·
                  rfl

theorem cell23_1910526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_1910526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910526 prefixEnd_1910526 := by exact prefixLift 1910526
  have htrace : WordTrace (prefixWord ++ tailWord_1910526) baseStart_1910526 baseEnd_1910526 := by
    simpa [prefixWord, tailWord_1910526, baseEnd_1910526] using wordTrace_append hprefix tailTrace_1910526
  have hstable : (prefixWord ++ tailWord_1910526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910526).length < 2 ^ (prefixWord ++ tailWord_1910526).sum := by decide
  have hdescent : baseEnd_1910526 < baseStart_1910526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910536 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1910536 : Nat := 118140960795 + 1910536 * 2 ^ 59
def prefixEnd_1910536 : Nat := 4983230072969 + 3 ^ 40 * 1910536 * 2
def baseEnd_1910536 : Nat := 981023275718442252813611

theorem tailTrace_1910536 : CollatzResearch.WordTrace tailWord_1910536 prefixEnd_1910536 981023275718442252813611 := by
  unfold tailWord_1910536
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841486303230920208175731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46455315070974560277567641 34841486303230920208175731)
  ·
    refine ⟨52262229454846380312263597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34841486303230920208175731 52262229454846380312263597)
    ·
      refine ⟨19598336045567392617098849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52262229454846380312263597 19598336045567392617098849)
      ·
        refine ⟨14698752034175544462824137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19598336045567392617098849 14698752034175544462824137)
        ·
          refine ⟨11024064025631658347118103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14698752034175544462824137 11024064025631658347118103)
          ·
            refine ⟨16536096038447487520677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024064025631658347118103 16536096038447487520677155)
            ·
              refine ⟨24804144057671231281015733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16536096038447487520677155 24804144057671231281015733)
              ·
                refine ⟨2325388505406677932595225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24804144057671231281015733 2325388505406677932595225)
                ·
                  refine ⟨1744041379055008449446419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325388505406677932595225 1744041379055008449446419)
                  ·
                    refine ⟨2616062068582512674169629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1744041379055008449446419 2616062068582512674169629)
                    ·
                      refine ⟨981023275718442252813611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2616062068582512674169629 981023275718442252813611)
                      ·
                        rfl

theorem cell23_1910536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1910536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910536 prefixEnd_1910536 := by exact prefixLift 1910536
  have htrace : WordTrace (prefixWord ++ tailWord_1910536) baseStart_1910536 baseEnd_1910536 := by
    simpa [prefixWord, tailWord_1910536, baseEnd_1910536] using wordTrace_append hprefix tailTrace_1910536
  have hstable : (prefixWord ++ tailWord_1910536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910536).length < 2 ^ (prefixWord ++ tailWord_1910536).sum := by decide
  have hdescent : baseEnd_1910536 < baseStart_1910536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910541 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1910541 : Nat := 118140960795 + 1910541 * 2 ^ 59
def prefixEnd_1910541 : Nat := 4983230072969 + 3 ^ 40 * 1910541 * 2
def baseEnd_1910541 : Nat := 981025843121714733251089

theorem tailTrace_1910541 : CollatzResearch.WordTrace tailWord_1910541 prefixEnd_1910541 981025843121714733251089 := by
  unfold tailWord_1910541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69683154971443726270283477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46455436647629150846855651 69683154971443726270283477)
  ·
    refine ⟨1633198944643212334459769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69683154971443726270283477 1633198944643212334459769)
    ·
      refine ⟨1224899208482409250844827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1633198944643212334459769 1224899208482409250844827)
      ·
        refine ⟨1837348812723613876267241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224899208482409250844827 1837348812723613876267241)
        ·
          refine ⟨1378011609542710407200431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837348812723613876267241 1378011609542710407200431)
          ·
            refine ⟨2067017414314065610800647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378011609542710407200431 2067017414314065610800647)
            ·
              refine ⟨3100526121471098416200971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067017414314065610800647 3100526121471098416200971)
              ·
                refine ⟨4650789182206647624301457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100526121471098416200971 4650789182206647624301457)
                ·
                  refine ⟨3488091886654985718226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650789182206647624301457 3488091886654985718226093)
                  ·
                    refine ⟨1308034457495619644334785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488091886654985718226093 1308034457495619644334785)
                    ·
                      refine ⟨981025843121714733251089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308034457495619644334785 981025843121714733251089)
                      ·
                        rfl

theorem cell23_1910541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1910541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910541 prefixEnd_1910541 := by exact prefixLift 1910541
  have htrace : WordTrace (prefixWord ++ tailWord_1910541) baseStart_1910541 baseEnd_1910541 := by
    simpa [prefixWord, tailWord_1910541, baseEnd_1910541] using wordTrace_append hprefix tailTrace_1910541
  have hstable : (prefixWord ++ tailWord_1910541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910541).length < 2 ^ (prefixWord ++ tailWord_1910541).sum := by decide
  have hdescent : baseEnd_1910541 < baseStart_1910541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910563 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 1, 3, 2]
def baseStart_1910563 : Nat := 118140960795 + 1910563 * 2 ^ 59
def prefixEnd_1910563 : Nat := 4983230072969 + 3 ^ 40 * 1910563 * 2
def baseEnd_1910563 : Nat := 981037139696113647175987

theorem tailTrace_1910563 : CollatzResearch.WordTrace tailWord_1910563 prefixEnd_1910563 981037139696113647175987 := by
  unfold tailWord_1910563
  simp only [CollatzResearch.WordTrace]
  refine ⟨69683957377364024027584343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46455971584909349351722895 69683957377364024027584343)
  ·
    refine ⟨104525936066046036041376515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69683957377364024027584343 104525936066046036041376515)
    ·
      refine ⟨156788904099069054062064773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104525936066046036041376515 156788904099069054062064773)
      ·
        refine ⟨29397919518575447636637145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156788904099069054062064773 29397919518575447636637145)
        ·
          refine ⟨22048439638931585727477859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29397919518575447636637145 22048439638931585727477859)
          ·
            refine ⟨33072659458397378591216789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22048439638931585727477859 33072659458397378591216789)
            ·
              refine ⟨1550280912112377121463287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33072659458397378591216789 1550280912112377121463287)
              ·
                refine ⟨2325421368168565682194931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550280912112377121463287 2325421368168565682194931)
                ·
                  refine ⟨3488132052252848523292397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325421368168565682194931 3488132052252848523292397)
                  ·
                    refine ⟨1308049519594818196234649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488132052252848523292397 1308049519594818196234649)
                    ·
                      refine ⟨981037139696113647175987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308049519594818196234649 981037139696113647175987)
                      ·
                        rfl

theorem cell23_1910563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_1910563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910563 prefixEnd_1910563 := by exact prefixLift 1910563
  have htrace : WordTrace (prefixWord ++ tailWord_1910563) baseStart_1910563 baseEnd_1910563 := by
    simpa [prefixWord, tailWord_1910563, baseEnd_1910563] using wordTrace_append hprefix tailTrace_1910563
  have hstable : (prefixWord ++ tailWord_1910563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910563).length < 2 ^ (prefixWord ++ tailWord_1910563).sum := by decide
  have hdescent : baseEnd_1910563 < baseStart_1910563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910649 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1910649 : Nat := 118140960795 + 1910649 * 2 ^ 59
def prefixEnd_1910649 : Nat := 4983230072969 + 3 ^ 40 * 1910649 * 2
def baseEnd_1910649 : Nat := 981081299032400310700591

theorem tailTrace_1910649 : CollatzResearch.WordTrace tailWord_1910649 prefixEnd_1910649 981081299032400310700591 := by
  unfold tailWord_1910649
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687094055052460715215001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46458062703368307143476667 69687094055052460715215001)
  ·
    refine ⟨52265320541289345536411251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69687094055052460715215001 52265320541289345536411251)
    ·
      refine ⟨78397980811934018304616877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52265320541289345536411251 78397980811934018304616877)
      ·
        refine ⟨29399242804475256864231329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78397980811934018304616877 29399242804475256864231329)
        ·
          refine ⟨22049432103356442648173497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29399242804475256864231329 22049432103356442648173497)
          ·
            refine ⟨16537074077517331986130123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22049432103356442648173497 16537074077517331986130123)
            ·
              refine ⟨24805611116275997979195185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537074077517331986130123 24805611116275997979195185)
              ·
                refine ⟨18604208337206998484396389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24805611116275997979195185 18604208337206998484396389)
                ·
                  refine ⟨3488289063226312215824323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18604208337206998484396389 3488289063226312215824323)
                  ·
                    refine ⟨5232433594839468323736485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488289063226312215824323 5232433594839468323736485)
                    ·
                      refine ⟨981081299032400310700591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5232433594839468323736485 981081299032400310700591)
                      ·
                        rfl

theorem cell23_1910649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1910649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910649 prefixEnd_1910649 := by exact prefixLift 1910649
  have htrace : WordTrace (prefixWord ++ tailWord_1910649) baseStart_1910649 baseEnd_1910649 := by
    simpa [prefixWord, tailWord_1910649, baseEnd_1910649] using wordTrace_append hprefix tailTrace_1910649
  have hstable : (prefixWord ++ tailWord_1910649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910649).length < 2 ^ (prefixWord ++ tailWord_1910649).sum := by decide
  have hdescent : baseEnd_1910649 < baseStart_1910649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910719 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 3, 5]
def baseStart_1910719 : Nat := 118140960795 + 1910719 * 2 ^ 59
def prefixEnd_1910719 : Nat := 4983230072969 + 3 ^ 40 * 1910719 * 2
def baseEnd_1910719 : Nat := 327039080892738345608423

theorem tailTrace_1910719 : CollatzResearch.WordTrace tailWord_1910719 prefixEnd_1910719 327039080892738345608423 := by
  unfold tailWord_1910719
  simp only [CollatzResearch.WordTrace]
  refine ⟨69689647164798862670263211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46459764776532575113508807 69689647164798862670263211)
  ·
    refine ⟨104534470747198294005394817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69689647164798862670263211 104534470747198294005394817)
    ·
      refine ⟨78400853060398720504046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104534470747198294005394817 78400853060398720504046113)
      ·
        refine ⟨58800639795299040378034585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78400853060398720504046113 58800639795299040378034585)
        ·
          refine ⟨44100479846474280283525939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58800639795299040378034585 44100479846474280283525939)
          ·
            refine ⟨66150719769711420425288909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44100479846474280283525939 66150719769711420425288909)
            ·
              refine ⟨24806519913641782659483341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66150719769711420425288909 24806519913641782659483341)
              ·
                refine ⟨9302444967615668497306253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24806519913641782659483341 9302444967615668497306253)
                ·
                  refine ⟨3488416862855875686489845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302444967615668497306253 3488416862855875686489845)
                  ·
                    refine ⟨327039080892738345608423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3488416862855875686489845 327039080892738345608423)
                    ·
                      rfl

theorem cell23_1910719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_1910719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910719 prefixEnd_1910719 := by exact prefixLift 1910719
  have htrace : WordTrace (prefixWord ++ tailWord_1910719) baseStart_1910719 baseEnd_1910719 := by
    simpa [prefixWord, tailWord_1910719, baseEnd_1910719] using wordTrace_append hprefix tailTrace_1910719
  have hstable : (prefixWord ++ tailWord_1910719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910719).length < 2 ^ (prefixWord ++ tailWord_1910719).sum := by decide
  have hdescent : baseEnd_1910719 < baseStart_1910719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910776 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1910776 : Nat := 118140960795 + 1910776 * 2 ^ 59
def prefixEnd_1910776 : Nat := 4983230072969 + 3 ^ 40 * 1910776 * 2
def baseEnd_1910776 : Nat := 981146511075521313812507

theorem tailTrace_1910776 : CollatzResearch.WordTrace tailWord_1910776 prefixEnd_1910776 981146511075521313812507 := by
  unfold tailWord_1910776
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845863062796180702544091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46461150750394907603392121 34845863062796180702544091)
  ·
    refine ⟨52268794594194271053816137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34845863062796180702544091 52268794594194271053816137)
    ·
      refine ⟨39201595945645703290362103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52268794594194271053816137 39201595945645703290362103)
      ·
        refine ⟨58802393918468554935543155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39201595945645703290362103 58802393918468554935543155)
        ·
          refine ⟨88203590877702832403314733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58802393918468554935543155 88203590877702832403314733)
          ·
            refine ⟨33076346579138562151243025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88203590877702832403314733 33076346579138562151243025)
            ·
              refine ⟨24807259934353921613432269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33076346579138562151243025 24807259934353921613432269)
              ·
                refine ⟨9302722475382720605037101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24807259934353921613432269 9302722475382720605037101)
                ·
                  refine ⟨3488520928268520226888913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302722475382720605037101 3488520928268520226888913)
                  ·
                    refine ⟨2616390696201390170166685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488520928268520226888913 2616390696201390170166685)
                    ·
                      refine ⟨981146511075521313812507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2616390696201390170166685 981146511075521313812507)
                      ·
                        rfl

theorem cell23_1910776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1910776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910776 prefixEnd_1910776 := by exact prefixLift 1910776
  have htrace : WordTrace (prefixWord ++ tailWord_1910776) baseStart_1910776 baseEnd_1910776 := by
    simpa [prefixWord, tailWord_1910776, baseEnd_1910776] using wordTrace_append hprefix tailTrace_1910776
  have hstable : (prefixWord ++ tailWord_1910776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910776).length < 2 ^ (prefixWord ++ tailWord_1910776).sum := by decide
  have hdescent : baseEnd_1910776 < baseStart_1910776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910809 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_1910809 : Nat := 118140960795 + 1910809 * 2 ^ 59
def prefixEnd_1910809 : Nat := 4983230072969 + 3 ^ 40 * 1910809 * 2
def baseEnd_1910809 : Nat := 327054485312373228233285

theorem tailTrace_1910809 : CollatzResearch.WordTrace tailWord_1910809 prefixEnd_1910809 327054485312373228233285 := by
  unfold tailWord_1910809
  simp only [CollatzResearch.WordTrace]
  refine ⟨69692929734472808041039481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46461953156315205360692987 69692929734472808041039481)
  ·
    refine ⟨52269697300854606030779611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69692929734472808041039481 52269697300854606030779611)
    ·
      refine ⟨78404545951281909046169417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52269697300854606030779611 78404545951281909046169417)
      ·
        refine ⟨58803409463461431784627063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78404545951281909046169417 58803409463461431784627063)
        ·
          refine ⟨88205114195192147676940595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58803409463461431784627063 88205114195192147676940595)
          ·
            refine ⟨132307671292788221515410893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88205114195192147676940595 132307671292788221515410893)
            ·
              refine ⟨49615376734795583068279085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132307671292788221515410893 49615376734795583068279085)
              ·
                refine ⟨18605766275548343650604657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49615376734795583068279085 18605766275548343650604657)
                ·
                  refine ⟨13954324706661257737953493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18605766275548343650604657 13954324706661257737953493)
                  ·
                    refine ⟨327054485312373228233285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13954324706661257737953493 327054485312373228233285)
                    ·
                      rfl

theorem cell23_1910809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_1910809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910809 prefixEnd_1910809 := by exact prefixLift 1910809
  have htrace : WordTrace (prefixWord ++ tailWord_1910809) baseStart_1910809 baseEnd_1910809 := by
    simpa [prefixWord, tailWord_1910809, baseEnd_1910809] using wordTrace_append hprefix tailTrace_1910809
  have hstable : (prefixWord ++ tailWord_1910809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910809).length < 2 ^ (prefixWord ++ tailWord_1910809).sum := by decide
  have hdescent : baseEnd_1910809 < baseStart_1910809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910817 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_1910817 : Nat := 118140960795 + 1910817 * 2 ^ 59
def prefixEnd_1910817 : Nat := 4983230072969 + 3 ^ 40 * 1910817 * 2
def baseEnd_1910817 : Nat := 327055854594118551133273

theorem tailTrace_1910817 : CollatzResearch.WordTrace tailWord_1910817 prefixEnd_1910817 327055854594118551133273 := by
  unfold tailWord_1910817
  simp only [CollatzResearch.WordTrace]
  refine ⟨69693221518443825407330705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46462147678962550271553803 69693221518443825407330705)
  ·
    refine ⟨52269916138832869055498029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69693221518443825407330705 52269916138832869055498029)
    ·
      refine ⟨19601218552062325895811761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52269916138832869055498029 19601218552062325895811761)
      ·
        refine ⟨14700913914046744421858821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19601218552062325895811761 14700913914046744421858821)
        ·
          refine ⟨2756421358883764579098529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14700913914046744421858821 2756421358883764579098529)
          ·
            refine ⟨2067316019162823434323897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756421358883764579098529 2067316019162823434323897)
            ·
              refine ⟨1550487014372117575742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067316019162823434323897 1550487014372117575742923)
              ·
                refine ⟨2325730521558176363614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550487014372117575742923 2325730521558176363614385)
                ·
                  refine ⟨1744297891168632272710789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325730521558176363614385 1744297891168632272710789)
                  ·
                    refine ⟨327055854594118551133273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744297891168632272710789 327055854594118551133273)
                    ·
                      rfl

theorem cell23_1910817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_1910817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910817 prefixEnd_1910817 := by exact prefixLift 1910817
  have htrace : WordTrace (prefixWord ++ tailWord_1910817) baseStart_1910817 baseEnd_1910817 := by
    simpa [prefixWord, tailWord_1910817, baseEnd_1910817] using wordTrace_append hprefix tailTrace_1910817
  have hstable : (prefixWord ++ tailWord_1910817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910817).length < 2 ^ (prefixWord ++ tailWord_1910817).sum := by decide
  have hdescent : baseEnd_1910817 < baseStart_1910817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910824 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1910824 : Nat := 118140960795 + 1910824 * 2 ^ 59
def prefixEnd_1910824 : Nat := 4983230072969 + 3 ^ 40 * 1910824 * 2
def baseEnd_1910824 : Nat := 981171158146937126012287

theorem tailTrace_1910824 : CollatzResearch.WordTrace tailWord_1910824 prefixEnd_1910824 981171158146937126012287 := by
  unfold tailWord_1910824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34846738414709232801417763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46462317886278977068557017 34846738414709232801417763)
  ·
    refine ⟨52270107622063849202126645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34846738414709232801417763 52270107622063849202126645)
    ·
      refine ⟨4900322589568485862699373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52270107622063849202126645 4900322589568485862699373)
      ·
        refine ⟨1837620971088182198512265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4900322589568485862699373 1837620971088182198512265)
        ·
          refine ⟨1378215728316136648884199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837620971088182198512265 1378215728316136648884199)
          ·
            refine ⟨2067323592474204973326299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378215728316136648884199 2067323592474204973326299)
            ·
              refine ⟨3100985388711307459989449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067323592474204973326299 3100985388711307459989449)
              ·
                refine ⟨2325739041533480594992087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100985388711307459989449 2325739041533480594992087)
                ·
                  refine ⟨3488608562300220892488131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325739041533480594992087 3488608562300220892488131)
                  ·
                    refine ⟨5232912843450331338732197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488608562300220892488131 5232912843450331338732197)
                    ·
                      refine ⟨981171158146937126012287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5232912843450331338732197 981171158146937126012287)
                      ·
                        rfl

theorem cell23_1910824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1910824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910824 prefixEnd_1910824 := by exact prefixLift 1910824
  have htrace : WordTrace (prefixWord ++ tailWord_1910824) baseStart_1910824 baseEnd_1910824 := by
    simpa [prefixWord, tailWord_1910824, baseEnd_1910824] using wordTrace_append hprefix tailTrace_1910824
  have hstable : (prefixWord ++ tailWord_1910824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910824).length < 2 ^ (prefixWord ++ tailWord_1910824).sum := by decide
  have hdescent : baseEnd_1910824 < baseStart_1910824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910880 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2]
def baseStart_1910880 : Nat := 118140960795 + 1910880 * 2 ^ 59
def prefixEnd_1910880 : Nat := 4983230072969 + 3 ^ 40 * 1910880 * 2
def baseEnd_1910880 : Nat := 981199913063588906912029

theorem tailTrace_1910880 : CollatzResearch.WordTrace tailWord_1910880 prefixEnd_1910880 981199913063588906912029 := by
  unfold tailWord_1910880
  simp only [CollatzResearch.WordTrace]
  refine ⟨34847759658607793583437047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46463679544810391444582729 34847759658607793583437047)
  ·
    refine ⟨52271639487911690375155571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34847759658607793583437047 52271639487911690375155571)
    ·
      refine ⟨78407459231867535562733357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52271639487911690375155571 78407459231867535562733357)
      ·
        refine ⟨29402797211950325836025009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78407459231867535562733357 29402797211950325836025009)
        ·
          refine ⟨22052097908962744377018757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29402797211950325836025009 22052097908962744377018757)
          ·
            refine ⟨4134768357930514570691017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22052097908962744377018757 4134768357930514570691017)
            ·
              refine ⟨3101076268447885928018263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134768357930514570691017 3101076268447885928018263)
              ·
                refine ⟨4651614402671828892027395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101076268447885928018263 4651614402671828892027395)
                ·
                  refine ⟨6977421604007743338041093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651614402671828892027395 6977421604007743338041093)
                  ·
                    refine ⟨1308266550751451875882705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977421604007743338041093 1308266550751451875882705)
                    ·
                      refine ⟨981199913063588906912029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308266550751451875882705 981199913063588906912029)
                      ·
                        rfl

theorem cell23_1910880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_1910880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910880 prefixEnd_1910880 := by exact prefixLift 1910880
  have htrace : WordTrace (prefixWord ++ tailWord_1910880) baseStart_1910880 baseEnd_1910880 := by
    simpa [prefixWord, tailWord_1910880, baseEnd_1910880] using wordTrace_append hprefix tailTrace_1910880
  have hstable : (prefixWord ++ tailWord_1910880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910880).length < 2 ^ (prefixWord ++ tailWord_1910880).sum := by decide
  have hdescent : baseEnd_1910880 < baseStart_1910880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910903 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 5]
def baseStart_1910903 : Nat := 118140960795 + 1910903 * 2 ^ 59
def prefixEnd_1910903 : Nat := 4983230072969 + 3 ^ 40 * 1910903 * 2
def baseEnd_1910903 : Nat := 109023524790960257436047

theorem tailTrace_1910903 : CollatzResearch.WordTrace tailWord_1910903 prefixEnd_1910903 109023524790960257436047 := by
  unfold tailWord_1910903
  simp only [CollatzResearch.WordTrace]
  refine ⟨69696358196132262094961363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46464238797421508063307575 69696358196132262094961363)
  ·
    refine ⟨104544537294198393142442045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69696358196132262094961363 104544537294198393142442045)
    ·
      refine ⟨39204201485324397428415767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104544537294198393142442045 39204201485324397428415767)
      ·
        refine ⟨58806302227986596142623651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39204201485324397428415767 58806302227986596142623651)
        ·
          refine ⟨88209453341979894213935477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58806302227986596142623651 88209453341979894213935477)
          ·
            refine ⟨8269636250810615082556451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88209453341979894213935477 8269636250810615082556451)
            ·
              refine ⟨12404454376215922623834677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269636250810615082556451 12404454376215922623834677)
              ·
                refine ⟨1162917597770242745984501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12404454376215922623834677 1162917597770242745984501)
                ·
                  refine ⟨109023524790960257436047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162917597770242745984501 109023524790960257436047)
                  ·
                    rfl

theorem cell23_1910903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 5].length) (baseStart_1910903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910903 prefixEnd_1910903 := by exact prefixLift 1910903
  have htrace : WordTrace (prefixWord ++ tailWord_1910903) baseStart_1910903 baseEnd_1910903 := by
    simpa [prefixWord, tailWord_1910903, baseEnd_1910903] using wordTrace_append hprefix tailTrace_1910903
  have hstable : (prefixWord ++ tailWord_1910903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910903).length < 2 ^ (prefixWord ++ tailWord_1910903).sum := by decide
  have hdescent : baseEnd_1910903 < baseStart_1910903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910920 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 5]
def baseStart_1910920 : Nat := 118140960795 + 1910920 * 2 ^ 59
def prefixEnd_1910920 : Nat := 4983230072969 + 3 ^ 40 * 1910920 * 2
def baseEnd_1910920 : Nat := 109024494698863194490205

theorem tailTrace_1910920 : CollatzResearch.WordTrace tailWord_1910920 prefixEnd_1910920 109024494698863194490205 := by
  unfold tailWord_1910920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848489118535336999165107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46464652158047115998886809 34848489118535336999165107)
  ·
    refine ⟨52272733677803005498747661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34848489118535336999165107 52272733677803005498747661)
    ·
      refine ⟨19602275129176127062030373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52272733677803005498747661 19602275129176127062030373)
      ·
        refine ⟨3675426586720523824130695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19602275129176127062030373 3675426586720523824130695)
        ·
          refine ⟨5513139880080785736196043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675426586720523824130695 5513139880080785736196043)
          ·
            refine ⟨8269709820121178604294065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513139880080785736196043 8269709820121178604294065)
            ·
              refine ⟨6202282365090883953220549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269709820121178604294065 6202282365090883953220549)
              ·
                refine ⟨1162927943454540741228853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6202282365090883953220549 1162927943454540741228853)
                ·
                  refine ⟨109024494698863194490205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162927943454540741228853 109024494698863194490205)
                  ·
                    rfl

theorem cell23_1910920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 5].length) (baseStart_1910920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910920 prefixEnd_1910920 := by exact prefixLift 1910920
  have htrace : WordTrace (prefixWord ++ tailWord_1910920) baseStart_1910920 baseEnd_1910920 := by
    simpa [prefixWord, tailWord_1910920, baseEnd_1910920] using wordTrace_append hprefix tailTrace_1910920
  have hstable : (prefixWord ++ tailWord_1910920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910920).length < 2 ^ (prefixWord ++ tailWord_1910920).sum := by decide
  have hdescent : baseEnd_1910920 < baseStart_1910920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910954 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_1910954 : Nat := 118140960795 + 1910954 * 2 ^ 59
def prefixEnd_1910954 : Nat := 4983230072969 + 3 ^ 40 * 1910954 * 2
def baseEnd_1910954 : Nat := 109026434514669068598521

theorem tailTrace_1910954 : CollatzResearch.WordTrace tailWord_1910954 prefixEnd_1910954 109026434514669068598521 := by
  unfold tailWord_1910954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424554579736874451266979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46465478879298331870045277 17424554579736874451266979)
  ·
    refine ⟨26136831869605311676900469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424554579736874451266979 26136831869605311676900469)
    ·
      refine ⟨2450327987775497969709419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26136831869605311676900469 2450327987775497969709419)
      ·
        refine ⟨3675491981663246954564129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450327987775497969709419 3675491981663246954564129)
        ·
          refine ⟨2756618986247435215923097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675491981663246954564129 2756618986247435215923097)
          ·
            refine ⟨2067464239685576411942323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756618986247435215923097 2067464239685576411942323)
            ·
              refine ⟨3101196359528364617913485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067464239685576411942323 3101196359528364617913485)
              ·
                refine ⟨1162948634823136731717557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101196359528364617913485 1162948634823136731717557)
                ·
                  refine ⟨109026434514669068598521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162948634823136731717557 109026434514669068598521)
                  ·
                    rfl

theorem cell23_1910954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_1910954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1910954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1910954 prefixEnd_1910954 := by exact prefixLift 1910954
  have htrace : WordTrace (prefixWord ++ tailWord_1910954) baseStart_1910954 baseEnd_1910954 := by
    simpa [prefixWord, tailWord_1910954, baseEnd_1910954] using wordTrace_append hprefix tailTrace_1910954
  have hstable : (prefixWord ++ tailWord_1910954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910954).length < 2 ^ (prefixWord ++ tailWord_1910954).sum := by decide
  have hdescent : baseEnd_1910954 < baseStart_1910954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911004 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1911004 : Nat := 118140960795 + 1911004 * 2 ^ 59
def prefixEnd_1911004 : Nat := 4983230072969 + 3 ^ 40 * 1911004 * 2
def baseEnd_1911004 : Nat := 981263584664746421761459

theorem tailTrace_1911004 : CollatzResearch.WordTrace tailWord_1911004 prefixEnd_1911004 981263584664746421761459 := by
  unfold tailWord_1911004
  simp only [CollatzResearch.WordTrace]
  refine ⟨34850020984383178172194033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46466694645844237562925377 34850020984383178172194033)
  ·
    refine ⟨26137515738287383629145525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34850020984383178172194033 26137515738287383629145525)
    ·
      refine ⟨2450392100464442215232393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26137515738287383629145525 2450392100464442215232393)
      ·
        refine ⟨1837794075348331661424295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450392100464442215232393 1837794075348331661424295)
        ·
          refine ⟨2756691113022497492136443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837794075348331661424295 2756691113022497492136443)
          ·
            refine ⟨4135036669533746238204665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756691113022497492136443 4135036669533746238204665)
            ·
              refine ⟨3101277502150309678653499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135036669533746238204665 3101277502150309678653499)
              ·
                refine ⟨4651916253225464517980249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101277502150309678653499 4651916253225464517980249)
                ·
                  refine ⟨3488937189919098388485187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651916253225464517980249 3488937189919098388485187)
                  ·
                    refine ⟨5233405784878647582727781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488937189919098388485187 5233405784878647582727781)
                    ·
                      refine ⟨981263584664746421761459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5233405784878647582727781 981263584664746421761459)
                      ·
                        rfl

theorem cell23_1911004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1911004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911004 prefixEnd_1911004 := by exact prefixLift 1911004
  have htrace : WordTrace (prefixWord ++ tailWord_1911004) baseStart_1911004 baseEnd_1911004 := by
    simpa [prefixWord, tailWord_1911004, baseEnd_1911004] using wordTrace_append hprefix tailTrace_1911004
  have hstable : (prefixWord ++ tailWord_1911004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911004).length < 2 ^ (prefixWord ++ tailWord_1911004).sum := by decide
  have hdescent : baseEnd_1911004 < baseStart_1911004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911043 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4]
def baseStart_1911043 : Nat := 118140960795 + 1911043 * 2 ^ 59
def prefixEnd_1911043 : Nat := 4983230072969 + 3 ^ 40 * 1911043 * 2
def baseEnd_1911043 : Nat := 981283610410271769173779

theorem tailTrace_1911043 : CollatzResearch.WordTrace tailWord_1911043 prefixEnd_1911043 981283610410271769173779 := by
  unfold tailWord_1911043
  simp only [CollatzResearch.WordTrace]
  refine ⟨69701464415625066005057783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46467642943750044003371855 69701464415625066005057783)
  ·
    refine ⟨104552196623437599007586675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69701464415625066005057783 104552196623437599007586675)
    ·
      refine ⟨156828294935156398511380013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104552196623437599007586675 156828294935156398511380013)
      ·
        refine ⟨58810610600683649441767505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156828294935156398511380013 58810610600683649441767505)
        ·
          refine ⟨44107957950512737081325629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58810610600683649441767505 44107957950512737081325629)
          ·
            refine ⟨16540484231442276405497111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44107957950512737081325629 16540484231442276405497111)
            ·
              refine ⟨24810726347163414608245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540484231442276405497111 24810726347163414608245667)
              ·
                refine ⟨37216089520745121912368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24810726347163414608245667 37216089520745121912368501)
                ·
                  refine ⟨3489008392569855179284547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37216089520745121912368501 3489008392569855179284547)
                  ·
                    refine ⟨5233512588854782768926821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489008392569855179284547 5233512588854782768926821)
                    ·
                      refine ⟨981283610410271769173779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5233512588854782768926821 981283610410271769173779)
                      ·
                        rfl

theorem cell23_1911043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_1911043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911043 prefixEnd_1911043 := by exact prefixLift 1911043
  have htrace : WordTrace (prefixWord ++ tailWord_1911043) baseStart_1911043 baseEnd_1911043 := by
    simpa [prefixWord, tailWord_1911043, baseEnd_1911043] using wordTrace_append hprefix tailTrace_1911043
  have hstable : (prefixWord ++ tailWord_1911043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911043).length < 2 ^ (prefixWord ++ tailWord_1911043).sum := by decide
  have hdescent : baseEnd_1911043 < baseStart_1911043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911074 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1911074 : Nat := 118140960795 + 1911074 * 2 ^ 59
def prefixEnd_1911074 : Nat := 4983230072969 + 3 ^ 40 * 1911074 * 2
def baseEnd_1911074 : Nat := 327099842770187049295379

theorem tailTrace_1911074 : CollatzResearch.WordTrace tailWord_1911074 prefixEnd_1911074 327099842770187049295379 := by
  unfold tailWord_1911074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17425648769628189574859069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46468396719008505532957517 17425648769628189574859069)
  ·
    refine ⟨6534618288610571090572151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17425648769628189574859069 6534618288610571090572151)
    ·
      refine ⟨9801927432915856635858227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534618288610571090572151 9801927432915856635858227)
      ·
        refine ⟨14702891149373784953787341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801927432915856635858227 14702891149373784953787341)
        ·
          refine ⟨5513584181015169357670253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14702891149373784953787341 5513584181015169357670253)
          ·
            refine ⟨2067594067880688509126345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5513584181015169357670253 2067594067880688509126345)
            ·
              refine ⟨1550695550910516381844759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067594067880688509126345 1550695550910516381844759)
              ·
                refine ⟨2326043326365774572767139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550695550910516381844759 2326043326365774572767139)
                ·
                  refine ⟨3489064989548661859150709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326043326365774572767139 3489064989548661859150709)
                  ·
                    refine ⟨327099842770187049295379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3489064989548661859150709 327099842770187049295379)
                    ·
                      rfl

theorem cell23_1911074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1911074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911074 prefixEnd_1911074 := by exact prefixLift 1911074
  have htrace : WordTrace (prefixWord ++ tailWord_1911074) baseStart_1911074 baseEnd_1911074 := by
    simpa [prefixWord, tailWord_1911074, baseEnd_1911074] using wordTrace_append hprefix tailTrace_1911074
  have hstable : (prefixWord ++ tailWord_1911074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911074).length < 2 ^ (prefixWord ++ tailWord_1911074).sum := by decide
  have hdescent : baseEnd_1911074 < baseStart_1911074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911077 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_1911077 : Nat := 118140960795 + 1911077 * 2 ^ 59
def prefixEnd_1911077 : Nat := 4983230072969 + 3 ^ 40 * 1911077 * 2
def baseEnd_1911077 : Nat := 981301068752524636148623

theorem tailTrace_1911077 : CollatzResearch.WordTrace tailWord_1911077 prefixEnd_1911077 981301068752524636148623 := by
  unfold tailWord_1911077
  simp only [CollatzResearch.WordTrace]
  refine ⟨69702704497501889811795485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46468469665001259874530323 69702704497501889811795485)
  ·
    refine ⟨26138514186563208679423307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69702704497501889811795485 26138514186563208679423307)
    ·
      refine ⟨39207771279844813019134961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26138514186563208679423307 39207771279844813019134961)
      ·
        refine ⟨29405828459883609764351221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39207771279844813019134961 29405828459883609764351221)
        ·
          refine ⟨2756796418114088415407927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29405828459883609764351221 2756796418114088415407927)
          ·
            refine ⟨4135194627171132623111891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756796418114088415407927 4135194627171132623111891)
            ·
              refine ⟨6202791940756698934667837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135194627171132623111891 6202791940756698934667837)
              ·
                refine ⟨2326046977783762100500439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6202791940756698934667837 2326046977783762100500439)
                ·
                  refine ⟨3489070466675643150750659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326046977783762100500439 3489070466675643150750659)
                  ·
                    refine ⟨5233605700013464726125989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489070466675643150750659 5233605700013464726125989)
                    ·
                      refine ⟨981301068752524636148623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5233605700013464726125989 981301068752524636148623)
                      ·
                        rfl

theorem cell23_1911077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_1911077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911077 prefixEnd_1911077 := by exact prefixLift 1911077
  have htrace : WordTrace (prefixWord ++ tailWord_1911077) baseStart_1911077 baseEnd_1911077 := by
    simpa [prefixWord, tailWord_1911077, baseEnd_1911077] using wordTrace_append hprefix tailTrace_1911077
  have hstable : (prefixWord ++ tailWord_1911077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911077).length < 2 ^ (prefixWord ++ tailWord_1911077).sum := by decide
  have hdescent : baseEnd_1911077 < baseStart_1911077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911153 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1911153 : Nat := 118140960795 + 1911153 * 2 ^ 59
def prefixEnd_1911153 : Nat := 4983230072969 + 3 ^ 40 * 1911153 * 2
def baseEnd_1911153 : Nat := 981340093282266338798273

theorem tailTrace_1911153 : CollatzResearch.WordTrace tailWord_1911153 prefixEnd_1911153 981340093282266338798273 := by
  unfold tailWord_1911153
  simp only [CollatzResearch.WordTrace]
  refine ⟨69705476445226554791562113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46470317630151036527708075 69705476445226554791562113)
  ·
    refine ⟨52279107333919916093671585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69705476445226554791562113 52279107333919916093671585)
    ·
      refine ⟨39209330500439937070253689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52279107333919916093671585 39209330500439937070253689)
      ·
        refine ⟨29406997875329952802690267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39209330500439937070253689 29406997875329952802690267)
        ·
          refine ⟨44110496812994929204035401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29406997875329952802690267 44110496812994929204035401)
          ·
            refine ⟨33082872609746196903026551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44110496812994929204035401 33082872609746196903026551)
            ·
              refine ⟨49624308914619295354539827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33082872609746196903026551 49624308914619295354539827)
              ·
                refine ⟨74436463371928943031809741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49624308914619295354539827 74436463371928943031809741)
                ·
                  refine ⟨27913673764473353636928653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74436463371928943031809741 27913673764473353636928653)
                  ·
                    refine ⟨10467627661677507613848245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27913673764473353636928653 10467627661677507613848245)
                    ·
                      refine ⟨981340093282266338798273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10467627661677507613848245 981340093282266338798273)
                      ·
                        rfl

theorem cell23_1911153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1911153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911153 prefixEnd_1911153 := by exact prefixLift 1911153
  have htrace : WordTrace (prefixWord ++ tailWord_1911153) baseStart_1911153 baseEnd_1911153 := by
    simpa [prefixWord, tailWord_1911153, baseEnd_1911153] using wordTrace_append hprefix tailTrace_1911153
  have hstable : (prefixWord ++ tailWord_1911153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911153).length < 2 ^ (prefixWord ++ tailWord_1911153).sum := by decide
  have hdescent : baseEnd_1911153 < baseStart_1911153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911171 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 1, 3, 2]
def baseStart_1911171 : Nat := 118140960795 + 1911171 * 2 ^ 59
def prefixEnd_1911171 : Nat := 4983230072969 + 3 ^ 40 * 1911171 * 2
def baseEnd_1911171 : Nat := 981349335934047268373191

theorem tailTrace_1911171 : CollatzResearch.WordTrace tailWord_1911171 prefixEnd_1911171 981349335934047268373191 := by
  unfold tailWord_1911171
  simp only [CollatzResearch.WordTrace]
  refine ⟨69706132959161343865717367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46470755306107562577144911 69706132959161343865717367)
  ·
    refine ⟨104559199438742015798576051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69706132959161343865717367 104559199438742015798576051)
    ·
      refine ⟨156838799158113023697864077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104559199438742015798576051 156838799158113023697864077)
      ·
        refine ⟨58814549684292383886699029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156838799158113023697864077 58814549684292383886699029)
        ·
          refine ⟨2756932016451205494689017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58814549684292383886699029 2756932016451205494689017)
          ·
            refine ⟨2067699012338404121016763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756932016451205494689017 2067699012338404121016763)
            ·
              refine ⟨3101548518507606181525145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067699012338404121016763 3101548518507606181525145)
              ·
                refine ⟨2326161388880704636143859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101548518507606181525145 2326161388880704636143859)
                ·
                  refine ⟨3489242083321056954215789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326161388880704636143859 3489242083321056954215789)
                  ·
                    refine ⟨1308465781245396357830921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489242083321056954215789 1308465781245396357830921)
                    ·
                      refine ⟨981349335934047268373191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308465781245396357830921 981349335934047268373191)
                      ·
                        rfl

theorem cell23_1911171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_1911171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911171 prefixEnd_1911171 := by exact prefixLift 1911171
  have htrace : WordTrace (prefixWord ++ tailWord_1911171) baseStart_1911171 baseEnd_1911171 := by
    simpa [prefixWord, tailWord_1911171, baseEnd_1911171] using wordTrace_append hprefix tailTrace_1911171
  have hstable : (prefixWord ++ tailWord_1911171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911171).length < 2 ^ (prefixWord ++ tailWord_1911171).sum := by decide
  have hdescent : baseEnd_1911171 < baseStart_1911171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911173 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 9]
def baseStart_1911173 : Nat := 118140960795 + 1911173 * 2 ^ 59
def prefixEnd_1911173 : Nat := 4983230072969 + 3 ^ 40 * 1911173 * 2
def baseEnd_1911173 : Nat := 109038929210595140060909

theorem tailTrace_1911173 : CollatzResearch.WordTrace tailWord_1911173 prefixEnd_1911173 109038929210595140060909 := by
  unfold tailWord_1911173
  simp only [CollatzResearch.WordTrace]
  refine ⟨69706205905154098207290173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46470803936769398804860115 69706205905154098207290173)
  ·
    refine ⟨26139827214432786827733815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69706205905154098207290173 26139827214432786827733815)
    ·
      refine ⟨39209740821649180241600723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26139827214432786827733815 39209740821649180241600723)
      ·
        refine ⟨58814611232473770362401085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39209740821649180241600723 58814611232473770362401085)
        ·
          refine ⟨22055479212177663885900407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58814611232473770362401085 22055479212177663885900407)
          ·
            refine ⟨33083218818266495828850611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22055479212177663885900407 33083218818266495828850611)
            ·
              refine ⟨49624828227399743743275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33083218818266495828850611 49624828227399743743275917)
              ·
                refine ⟨18609310585274903903728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49624828227399743743275917 18609310585274903903728469)
                ·
                  refine ⟨109038929210595140060909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18609310585274903903728469 109038929210595140060909)
                  ·
                    rfl

theorem cell23_1911173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_1911173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911173 prefixEnd_1911173 := by exact prefixLift 1911173
  have htrace : WordTrace (prefixWord ++ tailWord_1911173) baseStart_1911173 baseEnd_1911173 := by
    simpa [prefixWord, tailWord_1911173, baseEnd_1911173] using wordTrace_append hprefix tailTrace_1911173
  have hstable : (prefixWord ++ tailWord_1911173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911173).length < 2 ^ (prefixWord ++ tailWord_1911173).sum := by decide
  have hdescent : baseEnd_1911173 < baseStart_1911173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911188 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1911188 : Nat := 118140960795 + 1911188 * 2 ^ 59
def prefixEnd_1911188 : Nat := 4983230072969 + 3 ^ 40 * 1911188 * 2
def baseEnd_1911188 : Nat := 981358065105173701860613

theorem tailTrace_1911188 : CollatzResearch.WordTrace tailWord_1911188 prefixEnd_1911188 981358065105173701860613 := by
  unfold tailWord_1911188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34853376500049877884543109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46471168666733170512724145 34853376500049877884543109)
  ·
    refine ⟨6535008093759352103351833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34853376500049877884543109 6535008093759352103351833)
    ·
      refine ⟨4901256070319514077513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6535008093759352103351833 4901256070319514077513875)
      ·
        refine ⟨7351884105479271116270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901256070319514077513875 7351884105479271116270813)
        ·
          refine ⟨2756956539554726668601555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7351884105479271116270813 2756956539554726668601555)
          ·
            refine ⟨4135434809332090002902333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756956539554726668601555 4135434809332090002902333)
            ·
              refine ⟨1550788053499533751088375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135434809332090002902333 1550788053499533751088375)
              ·
                refine ⟨2326182080249300626632563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550788053499533751088375 2326182080249300626632563)
                ·
                  refine ⟨3489273120373950939948845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326182080249300626632563 3489273120373950939948845)
                  ·
                    refine ⟨1308477420140231602480817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489273120373950939948845 1308477420140231602480817)
                    ·
                      refine ⟨981358065105173701860613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308477420140231602480817 981358065105173701860613)
                      ·
                        rfl

theorem cell23_1911188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1911188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911188 prefixEnd_1911188 := by exact prefixLift 1911188
  have htrace : WordTrace (prefixWord ++ tailWord_1911188) baseStart_1911188 baseEnd_1911188 := by
    simpa [prefixWord, tailWord_1911188, baseEnd_1911188] using wordTrace_append hprefix tailTrace_1911188
  have hstable : (prefixWord ++ tailWord_1911188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911188).length < 2 ^ (prefixWord ++ tailWord_1911188).sum := by decide
  have hdescent : baseEnd_1911188 < baseStart_1911188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911217 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1911217 : Nat := 118140960795 + 1911217 * 2 ^ 59
def prefixEnd_1911217 : Nat := 4983230072969 + 3 ^ 40 * 1911217 * 2
def baseEnd_1911217 : Nat := 981372956044154088397979

theorem tailTrace_1911217 : CollatzResearch.WordTrace tailWord_1911217 prefixEnd_1911217 981372956044154088397979 := by
  unfold tailWord_1911217
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707810716994693721891905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46471873811329795814594603 69707810716994693721891905)
  ·
    refine ⟨52280858037746020291418929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69707810716994693721891905 52280858037746020291418929)
    ·
      refine ⟨39210643528309515218564197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52280858037746020291418929 39210643528309515218564197)
      ·
        refine ⟨7351995661558034103480787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39210643528309515218564197 7351995661558034103480787)
        ·
          refine ⟨11027993492337051155221181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7351995661558034103480787 11027993492337051155221181)
          ·
            refine ⟨4135497559626394183207943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11027993492337051155221181 4135497559626394183207943)
            ·
              refine ⟨6203246339439591274811915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135497559626394183207943 6203246339439591274811915)
              ·
                refine ⟨9304869509159386912217873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203246339439591274811915 9304869509159386912217873)
                ·
                  refine ⟨6978652131869540184163405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9304869509159386912217873 6978652131869540184163405)
                  ·
                    refine ⟨2616994549451077569061277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6978652131869540184163405 2616994549451077569061277)
                    ·
                      refine ⟨981372956044154088397979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2616994549451077569061277 981372956044154088397979)
                      ·
                        rfl

theorem cell23_1911217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1911217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911217 prefixEnd_1911217 := by exact prefixLift 1911217
  have htrace : WordTrace (prefixWord ++ tailWord_1911217) baseStart_1911217 baseEnd_1911217 := by
    simpa [prefixWord, tailWord_1911217, baseEnd_1911217] using wordTrace_append hprefix tailTrace_1911217
  have hstable : (prefixWord ++ tailWord_1911217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911217).length < 2 ^ (prefixWord ++ tailWord_1911217).sum := by decide
  have hdescent : baseEnd_1911217 < baseStart_1911217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911230 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1911230 : Nat := 118140960795 + 1911230 * 2 ^ 59
def prefixEnd_1911230 : Nat := 4983230072969 + 3 ^ 40 * 1911230 * 2
def baseEnd_1911230 : Nat := 981379631292662537535419

theorem tailTrace_1911230 : CollatzResearch.WordTrace tailWord_1911230 prefixEnd_1911230 981379631292662537535419 := by
  unfold tailWord_1911230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713535608243449617764393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46472189910631731294743429 8713535608243449617764393)
  ·
    refine ⟨6535151706182587213323295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8713535608243449617764393 6535151706182587213323295)
    ·
      refine ⟨9802727559273880819984943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6535151706182587213323295 9802727559273880819984943)
      ·
        refine ⟨14704091338910821229977415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802727559273880819984943 14704091338910821229977415)
        ·
          refine ⟨22056137008366231844966123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704091338910821229977415 22056137008366231844966123)
          ·
            refine ⟨33084205512549347767449185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22056137008366231844966123 33084205512549347767449185)
            ·
              refine ⟨24813154134412010825586889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33084205512549347767449185 24813154134412010825586889)
              ·
                refine ⟨18609865600809008119190167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24813154134412010825586889 18609865600809008119190167)
                ·
                  refine ⟨27914798401213512178785251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18609865600809008119190167 27914798401213512178785251)
                  ·
                    refine ⟨41872197601820268268177877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27914798401213512178785251 41872197601820268268177877)
                    ·
                      refine ⟨981379631292662537535419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41872197601820268268177877 981379631292662537535419)
                      ·
                        rfl

theorem cell23_1911230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1911230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911230 prefixEnd_1911230 := by exact prefixLift 1911230
  have htrace : WordTrace (prefixWord ++ tailWord_1911230) baseStart_1911230 baseEnd_1911230 := by
    simpa [prefixWord, tailWord_1911230, baseEnd_1911230] using wordTrace_append hprefix tailTrace_1911230
  have hstable : (prefixWord ++ tailWord_1911230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911230).length < 2 ^ (prefixWord ++ tailWord_1911230).sum := by decide
  have hdescent : baseEnd_1911230 < baseStart_1911230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911257 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 4, 2]
def baseStart_1911257 : Nat := 118140960795 + 1911257 * 2 ^ 59
def prefixEnd_1911257 : Nat := 4983230072969 + 3 ^ 40 * 1911257 * 2
def baseEnd_1911257 : Nat := 981393495270333931897795

theorem tailTrace_1911257 : CollatzResearch.WordTrace tailWord_1911257 prefixEnd_1911257 981393495270333931897795 := by
  unfold tailWord_1911257
  simp only [CollatzResearch.WordTrace]
  refine ⟨69709269636849780553348025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46472846424566520368898683 69709269636849780553348025)
  ·
    refine ⟨52281952227637335415011019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69709269636849780553348025 52281952227637335415011019)
    ·
      refine ⟨78422928341456003122516529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52281952227637335415011019 78422928341456003122516529)
      ·
        refine ⟨58817196256092002341887397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78422928341456003122516529 58817196256092002341887397)
        ·
          refine ⟨11028224298017250439103887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58817196256092002341887397 11028224298017250439103887)
          ·
            refine ⟨16542336447025875658655831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11028224298017250439103887 16542336447025875658655831)
            ·
              refine ⟨24813504670538813487983747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16542336447025875658655831 24813504670538813487983747)
              ·
                refine ⟨37220257005808220231975621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24813504670538813487983747 37220257005808220231975621)
                ·
                  refine ⟨6978798188589041293495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37220257005808220231975621 6978798188589041293495429)
                  ·
                    refine ⟨1308524660360445242530393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978798188589041293495429 1308524660360445242530393)
                    ·
                      refine ⟨981393495270333931897795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308524660360445242530393 981393495270333931897795)
                      ·
                        rfl

theorem cell23_1911257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_1911257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911257 prefixEnd_1911257 := by exact prefixLift 1911257
  have htrace : WordTrace (prefixWord ++ tailWord_1911257) baseStart_1911257 baseEnd_1911257 := by
    simpa [prefixWord, tailWord_1911257, baseEnd_1911257] using wordTrace_append hprefix tailTrace_1911257
  have hstable : (prefixWord ++ tailWord_1911257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911257).length < 2 ^ (prefixWord ++ tailWord_1911257).sum := by decide
  have hdescent : baseEnd_1911257 < baseStart_1911257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911274 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_1911274 : Nat := 118140960795 + 1911274 * 2 ^ 59
def prefixEnd_1911274 : Nat := 4983230072969 + 3 ^ 40 * 1911274 * 2
def baseEnd_1911274 : Nat := 981402224441460365385217

theorem tailTrace_1911274 : CollatzResearch.WordTrace tailWord_1911274 prefixEnd_1911274 981402224441460365385217 := by
  unfold tailWord_1911274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427472419447048114179219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46473259785192128304477917 17427472419447048114179219)
  ·
    refine ⟨26141208629170572171268829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427472419447048114179219 26141208629170572171268829)
    ·
      refine ⟨9802953235938964564225811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26141208629170572171268829 9802953235938964564225811)
      ·
        refine ⟨14704429853908446846338717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802953235938964564225811 14704429853908446846338717)
        ·
          refine ⟨5514161195215667567377019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14704429853908446846338717 5514161195215667567377019)
          ·
            refine ⟨8271241792823501351065529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514161195215667567377019 8271241792823501351065529)
            ·
              refine ⟨6203431344617626013299147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271241792823501351065529 6203431344617626013299147)
              ·
                refine ⟨9305147016926439019948721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203431344617626013299147 9305147016926439019948721)
                ·
                  refine ⟨6978860262694829264961541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305147016926439019948721 6978860262694829264961541)
                  ·
                    refine ⟨1308536299255280487180289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978860262694829264961541 1308536299255280487180289)
                    ·
                      refine ⟨981402224441460365385217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308536299255280487180289 981402224441460365385217)
                      ·
                        rfl

theorem cell23_1911274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_1911274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911274 prefixEnd_1911274 := by exact prefixLift 1911274
  have htrace : WordTrace (prefixWord ++ tailWord_1911274) baseStart_1911274 baseEnd_1911274 := by
    simpa [prefixWord, tailWord_1911274, baseEnd_1911274] using wordTrace_append hprefix tailTrace_1911274
  have hstable : (prefixWord ++ tailWord_1911274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911274).length < 2 ^ (prefixWord ++ tailWord_1911274).sum := by decide
  have hdescent : baseEnd_1911274 < baseStart_1911274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911340 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1911340 : Nat := 118140960795 + 1911340 * 2 ^ 59
def prefixEnd_1911340 : Nat := 4983230072969 + 3 ^ 40 * 1911340 * 2
def baseEnd_1911340 : Nat := 327145371388219035719971

theorem tailTrace_1911340 : CollatzResearch.WordTrace tailWord_1911340 prefixEnd_1911340 327145371388219035719971 := by
  unfold tailWord_1911340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856148447774542864309737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46474864597032723819079649 34856148447774542864309737)
  ·
    refine ⟨26142111335830907148232303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34856148447774542864309737 26142111335830907148232303)
    ·
      refine ⟨39213167003746360722348455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26142111335830907148232303 39213167003746360722348455)
      ·
        refine ⟨58819750505619541083522683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39213167003746360722348455 58819750505619541083522683)
        ·
          refine ⟨88229625758429311625284025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58819750505619541083522683 88229625758429311625284025)
          ·
            refine ⟨66172219318821983718963019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88229625758429311625284025 66172219318821983718963019)
            ·
              refine ⟨99258328978232975578444529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66172219318821983718963019 99258328978232975578444529)
              ·
                refine ⟨74443746733674731683833397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99258328978232975578444529 74443746733674731683833397)
                ·
                  refine ⟨6979101256282006095359381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74443746733674731683833397 6979101256282006095359381)
                  ·
                    refine ⟨327145371388219035719971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6979101256282006095359381 327145371388219035719971)
                    ·
                      rfl

theorem cell23_1911340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1911340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911340 prefixEnd_1911340 := by exact prefixLift 1911340
  have htrace : WordTrace (prefixWord ++ tailWord_1911340) baseStart_1911340 baseEnd_1911340 := by
    simpa [prefixWord, tailWord_1911340, baseEnd_1911340] using wordTrace_append hprefix tailTrace_1911340
  have hstable : (prefixWord ++ tailWord_1911340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911340).length < 2 ^ (prefixWord ++ tailWord_1911340).sum := by decide
  have hdescent : baseEnd_1911340 < baseStart_1911340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911347 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4]
def baseStart_1911347 : Nat := 118140960795 + 1911347 * 2 ^ 59
def prefixEnd_1911347 : Nat := 4983230072969 + 3 ^ 40 * 1911347 * 2
def baseEnd_1911347 : Nat := 981439708529238579772381

theorem tailTrace_1911347 : CollatzResearch.WordTrace tailWord_1911347 prefixEnd_1911347 981439708529238579772381 := by
  unfold tailWord_1911347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69712552206523725924124295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46475034804349150616082863 69712552206523725924124295)
  ·
    refine ⟨104568828309785588886186443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69712552206523725924124295 104568828309785588886186443)
    ·
      refine ⟨156853242464678383329279665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104568828309785588886186443 156853242464678383329279665)
      ·
        refine ⟨117639931848508787496959749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156853242464678383329279665 117639931848508787496959749)
        ·
          refine ⟨22057487221595397655679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117639931848508787496959749 22057487221595397655679953)
          ·
            refine ⟨16543115416196548241759965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22057487221595397655679953 16543115416196548241759965)
            ·
              refine ⟨6203668281073705590659987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16543115416196548241759965 6203668281073705590659987)
              ·
                refine ⟨9305502421610558385989981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203668281073705590659987 9305502421610558385989981)
                ·
                  refine ⟨3489563408103959394746243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9305502421610558385989981 3489563408103959394746243)
                  ·
                    refine ⟨5234345112155939092119365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489563408103959394746243 5234345112155939092119365)
                    ·
                      refine ⟨981439708529238579772381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5234345112155939092119365 981439708529238579772381)
                      ·
                        rfl

theorem cell23_1911347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_1911347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911347 prefixEnd_1911347 := by exact prefixLift 1911347
  have htrace : WordTrace (prefixWord ++ tailWord_1911347) baseStart_1911347 baseEnd_1911347 := by
    simpa [prefixWord, tailWord_1911347, baseEnd_1911347] using wordTrace_append hprefix tailTrace_1911347
  have hstable : (prefixWord ++ tailWord_1911347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911347).length < 2 ^ (prefixWord ++ tailWord_1911347).sum := by decide
  have hdescent : baseEnd_1911347 < baseStart_1911347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911357 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1911357 : Nat := 118140960795 + 1911357 * 2 ^ 59
def prefixEnd_1911357 : Nat := 4983230072969 + 3 ^ 40 * 1911357 * 2
def baseEnd_1911357 : Nat := 327148281111927846882445

theorem tailTrace_1911357 : CollatzResearch.WordTrace tailWord_1911357 prefixEnd_1911357 327148281111927846882445 := by
  unfold tailWord_1911357
  simp only [CollatzResearch.WordTrace]
  refine ⟨69712916936487497631988325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46475277957658331754658883 69712916936487497631988325)
  ·
    refine ⟨13071171925591405805997811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69712916936487497631988325 13071171925591405805997811)
    ·
      refine ⟨19606757888387108708996717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071171925591405805997811 19606757888387108708996717)
      ·
        refine ⟨7352534208145165765873769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19606757888387108708996717 7352534208145165765873769)
        ·
          refine ⟨5514400656108874324405327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352534208145165765873769 5514400656108874324405327)
          ·
            refine ⟨8271600984163311486607991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514400656108874324405327 8271600984163311486607991)
            ·
              refine ⟨12407401476244967229911987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271600984163311486607991 12407401476244967229911987)
              ·
                refine ⟨18611102214367450844867981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407401476244967229911987 18611102214367450844867981)
                ·
                  refine ⟨6979163330387794066825493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18611102214367450844867981 6979163330387794066825493)
                  ·
                    refine ⟨327148281111927846882445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6979163330387794066825493 327148281111927846882445)
                    ·
                      rfl

theorem cell23_1911357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1911357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911357 prefixEnd_1911357 := by exact prefixLift 1911357
  have htrace : WordTrace (prefixWord ++ tailWord_1911357) baseStart_1911357 baseEnd_1911357 := by
    simpa [prefixWord, tailWord_1911357, baseEnd_1911357] using wordTrace_append hprefix tailTrace_1911357
  have hstable : (prefixWord ++ tailWord_1911357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911357).length < 2 ^ (prefixWord ++ tailWord_1911357).sum := by decide
  have hdescent : baseEnd_1911357 < baseStart_1911357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911361 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1911361 : Nat := 118140960795 + 1911361 * 2 ^ 59
def prefixEnd_1911361 : Nat := 4983230072969 + 3 ^ 40 * 1911361 * 2
def baseEnd_1911361 : Nat := 327148965752800508332439

theorem tailTrace_1911361 : CollatzResearch.WordTrace tailWord_1911361 prefixEnd_1911361 327148965752800508332439 := by
  unfold tailWord_1911361
  simp only [CollatzResearch.WordTrace]
  refine ⟨69713062828473006315133937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46475375218982004210089291 69713062828473006315133937)
  ·
    refine ⟨52284797121354754736350453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69713062828473006315133937 52284797121354754736350453)
    ·
      refine ⟨4901699730127008256532855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52284797121354754736350453 4901699730127008256532855)
      ·
        refine ⟨7352549595190512384799283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901699730127008256532855 7352549595190512384799283)
        ·
          refine ⟨11028824392785768577198925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352549595190512384799283 11028824392785768577198925)
          ·
            refine ⟨4135809147294663216449597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11028824392785768577198925 4135809147294663216449597)
            ·
              refine ⟨1550928430235498706168599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135809147294663216449597 1550928430235498706168599)
              ·
                refine ⟨2326392645353248059252899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550928430235498706168599 2326392645353248059252899)
                ·
                  refine ⟨3489588968029872088879349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326392645353248059252899 3489588968029872088879349)
                  ·
                    refine ⟨327148965752800508332439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3489588968029872088879349 327148965752800508332439)
                    ·
                      rfl

theorem cell23_1911361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1911361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911361 prefixEnd_1911361 := by exact prefixLift 1911361
  have htrace : WordTrace (prefixWord ++ tailWord_1911361) baseStart_1911361 baseEnd_1911361 := by
    simpa [prefixWord, tailWord_1911361, baseEnd_1911361] using wordTrace_append hprefix tailTrace_1911361
  have hstable : (prefixWord ++ tailWord_1911361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911361).length < 2 ^ (prefixWord ++ tailWord_1911361).sum := by decide
  have hdescent : baseEnd_1911361 < baseStart_1911361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911370 : List Nat := [3, 1, 2, 1, 1, 15]
def baseStart_1911370 : Nat := 118140960795 + 1911370 * 2 ^ 59
def prefixEnd_1911370 : Nat := 4983230072969 + 3 ^ 40 * 1911370 * 2
def baseEnd_1911370 : Nat := 4038895138206962920925

theorem tailTrace_1911370 : CollatzResearch.WordTrace tailWord_1911370 prefixEnd_1911370 4038895138206962920925 := by
  unfold tailWord_1911370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17428347771360100213052891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46475594056960267234807709 17428347771360100213052891)
  ·
    refine ⟨26142521657040150319579337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17428347771360100213052891 26142521657040150319579337)
    ·
      refine ⟨19606891242780112739684503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26142521657040150319579337 19606891242780112739684503)
      ·
        refine ⟨29410336864170169109526755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19606891242780112739684503 29410336864170169109526755)
        ·
          refine ⟨44115505296255253664290133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29410336864170169109526755 44115505296255253664290133)
          ·
            refine ⟨4038895138206962920925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 44115505296255253664290133 4038895138206962920925)
            ·
              rfl

theorem cell23_1911370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 15].length) (baseStart_1911370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911370 prefixEnd_1911370 := by exact prefixLift 1911370
  have htrace : WordTrace (prefixWord ++ tailWord_1911370) baseStart_1911370 baseEnd_1911370 := by
    simpa [prefixWord, tailWord_1911370, baseEnd_1911370] using wordTrace_append hprefix tailTrace_1911370
  have hstable : (prefixWord ++ tailWord_1911370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911370).length < 2 ^ (prefixWord ++ tailWord_1911370).sum := by decide
  have hdescent : baseEnd_1911370 < baseStart_1911370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911374 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1911374 : Nat := 118140960795 + 1911374 * 2 ^ 59
def prefixEnd_1911374 : Nat := 4983230072969 + 3 ^ 40 * 1911374 * 2
def baseEnd_1911374 : Nat := 327151190835636658044919

theorem tailTrace_1911374 : CollatzResearch.WordTrace tailWord_1911374 prefixEnd_1911374 327151190835636658044919 := by
  unfold tailWord_1911374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714192122178238691919647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46475691318283939690238117 8714192122178238691919647)
  ·
    refine ⟨13071288183267358037879471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8714192122178238691919647 13071288183267358037879471)
    ·
      refine ⟨19606932274901037056819207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071288183267358037879471 19606932274901037056819207)
      ·
        refine ⟨29410398412351555585228811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19606932274901037056819207 29410398412351555585228811)
        ·
          refine ⟨44115597618527333377843217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29410398412351555585228811 44115597618527333377843217)
          ·
            refine ⟨33086698213895500033382413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44115597618527333377843217 33086698213895500033382413)
            ·
              refine ⟨12407511830210812512518405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33086698213895500033382413 12407511830210812512518405)
              ·
                refine ⟨2326408468164527346097201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12407511830210812512518405 2326408468164527346097201)
                ·
                  refine ⟨1744806351123395509572901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326408468164527346097201 1744806351123395509572901)
                  ·
                    refine ⟨327151190835636658044919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744806351123395509572901 327151190835636658044919)
                    ·
                      rfl

theorem cell23_1911374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1911374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911374 prefixEnd_1911374 := by exact prefixLift 1911374
  have htrace : WordTrace (prefixWord ++ tailWord_1911374) baseStart_1911374 baseEnd_1911374 := by
    simpa [prefixWord, tailWord_1911374, baseEnd_1911374] using wordTrace_append hprefix tailTrace_1911374
  have hstable : (prefixWord ++ tailWord_1911374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911374).length < 2 ^ (prefixWord ++ tailWord_1911374).sum := by decide
  have hdescent : baseEnd_1911374 < baseStart_1911374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911447 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1911447 : Nat := 118140960795 + 1911447 * 2 ^ 59
def prefixEnd_1911447 : Nat := 4983230072969 + 3 ^ 40 * 1911447 * 2
def baseEnd_1911447 : Nat := 327163685531562729507307

theorem tailTrace_1911447 : CollatzResearch.WordTrace tailWord_1911447 prefixEnd_1911447 327163685531562729507307 := by
  unfold tailWord_1911447
  simp only [CollatzResearch.WordTrace]
  refine ⟨69716199506161443002764595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46477466337440962001843063 69716199506161443002764595)
  ·
    refine ⟨104574299259242164504146893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69716199506161443002764595 104574299259242164504146893)
    ·
      refine ⟨39215362222215811689055085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104574299259242164504146893 39215362222215811689055085)
      ·
        refine ⟨14705760833330929383395657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39215362222215811689055085 14705760833330929383395657)
        ·
          refine ⟨11029320624998197037546743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14705760833330929383395657 11029320624998197037546743)
          ·
            refine ⟨16543980937497295556320115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029320624998197037546743 16543980937497295556320115)
            ·
              refine ⟨24815971406245943334480173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16543980937497295556320115 24815971406245943334480173)
              ·
                refine ⟨9305989277342228750430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24815971406245943334480173 9305989277342228750430065)
                ·
                  refine ⟨6979491958006671562822549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305989277342228750430065 6979491958006671562822549)
                  ·
                    refine ⟨327163685531562729507307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6979491958006671562822549 327163685531562729507307)
                    ·
                      rfl

theorem cell23_1911447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1911447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911447 prefixEnd_1911447 := by exact prefixLift 1911447
  have htrace : WordTrace (prefixWord ++ tailWord_1911447) baseStart_1911447 baseEnd_1911447 := by
    simpa [prefixWord, tailWord_1911447, baseEnd_1911447] using wordTrace_append hprefix tailTrace_1911447
  have hstable : (prefixWord ++ tailWord_1911447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911447).length < 2 ^ (prefixWord ++ tailWord_1911447).sum := by decide
  have hdescent : baseEnd_1911447 < baseStart_1911447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911448 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1911448 : Nat := 118140960795 + 1911448 * 2 ^ 59
def prefixEnd_1911448 : Nat := 4983230072969 + 3 ^ 40 * 1911448 * 2
def baseEnd_1911448 : Nat := 981491570075342684609417

theorem tailTrace_1911448 : CollatzResearch.WordTrace tailWord_1911448 prefixEnd_1911448 981491570075342684609417 := by
  unfold tailWord_1911448
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858117989578910086775499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46477490652771880115700665 34858117989578910086775499)
  ·
    refine ⟨52287176984368365130163249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34858117989578910086775499 52287176984368365130163249)
    ·
      refine ⟨39215382738276273847622437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52287176984368365130163249 39215382738276273847622437)
      ·
        refine ⟨7352884263426801346429207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39215382738276273847622437 7352884263426801346429207)
        ·
          refine ⟨11029326395140202019643811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352884263426801346429207 11029326395140202019643811)
          ·
            refine ⟨16543989592710303029465717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029326395140202019643811 16543989592710303029465717)
            ·
              refine ⟨1550999024316590909012411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16543989592710303029465717 1550999024316590909012411)
              ·
                refine ⟨2326498536474886363518617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550999024316590909012411 2326498536474886363518617)
                ·
                  refine ⟨1744873902356164772638963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326498536474886363518617 1744873902356164772638963)
                  ·
                    refine ⟨2617310853534247158958445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1744873902356164772638963 2617310853534247158958445)
                    ·
                      refine ⟨981491570075342684609417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617310853534247158958445 981491570075342684609417)
                      ·
                        rfl

theorem cell23_1911448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1911448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911448 prefixEnd_1911448 := by exact prefixLift 1911448
  have htrace : WordTrace (prefixWord ++ tailWord_1911448) baseStart_1911448 baseEnd_1911448 := by
    simpa [prefixWord, tailWord_1911448, baseEnd_1911448] using wordTrace_append hprefix tailTrace_1911448
  have hstable : (prefixWord ++ tailWord_1911448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911448).length < 2 ^ (prefixWord ++ tailWord_1911448).sum := by decide
  have hdescent : baseEnd_1911448 < baseStart_1911448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911466 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1911466 : Nat := 118140960795 + 1911466 * 2 ^ 59
def prefixEnd_1911466 : Nat := 4983230072969 + 3 ^ 40 * 1911466 * 2
def baseEnd_1911466 : Nat := 981500812727123614184335

theorem tailTrace_1911466 : CollatzResearch.WordTrace tailWord_1911466 prefixEnd_1911466 981500812727123614184335 := by
  unfold tailWord_1911466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429223123273152311926563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46477928328728406165137501 17429223123273152311926563)
  ·
    refine ⟨26143834684909728467889845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429223123273152311926563 26143834684909728467889845)
    ·
      refine ⟨2450984501710287043864673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26143834684909728467889845 2450984501710287043864673)
      ·
        refine ⟨1838238376282715282898505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450984501710287043864673 1838238376282715282898505)
        ·
          refine ⟨1378678782212036462173879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838238376282715282898505 1378678782212036462173879)
          ·
            refine ⟨2068018173318054693260819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378678782212036462173879 2068018173318054693260819)
            ·
              refine ⟨3102027259977082039891229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068018173318054693260819 3102027259977082039891229)
              ·
                refine ⟨1163260222491405764959211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102027259977082039891229 1163260222491405764959211)
                ·
                  refine ⟨1744890333737108647438817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163260222491405764959211 1744890333737108647438817)
                  ·
                    refine ⟨1308667750302831485579113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1744890333737108647438817 1308667750302831485579113)
                    ·
                      refine ⟨981500812727123614184335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308667750302831485579113 981500812727123614184335)
                      ·
                        rfl

theorem cell23_1911466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1911466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911466 prefixEnd_1911466 := by exact prefixLift 1911466
  have htrace : WordTrace (prefixWord ++ tailWord_1911466) baseStart_1911466 baseEnd_1911466 := by
    simpa [prefixWord, tailWord_1911466, baseEnd_1911466] using wordTrace_append hprefix tailTrace_1911466
  have hstable : (prefixWord ++ tailWord_1911466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911466).length < 2 ^ (prefixWord ++ tailWord_1911466).sum := by decide
  have hdescent : baseEnd_1911466 < baseStart_1911466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911471 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 4, 2, 2]
def baseStart_1911471 : Nat := 118140960795 + 1911471 * 2 ^ 59
def prefixEnd_1911471 : Nat := 4983230072969 + 3 ^ 40 * 1911471 * 2
def baseEnd_1911471 : Nat := 981503380130396094621811

theorem tailTrace_1911471 : CollatzResearch.WordTrace tailWord_1911471 prefixEnd_1911471 981503380130396094621811 := by
  unfold tailWord_1911471
  simp only [CollatzResearch.WordTrace]
  refine ⟨69717074858074495101638267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46478049905382996734425511 69717074858074495101638267)
  ·
    refine ⟨104575612287111742652457401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69717074858074495101638267 104575612287111742652457401)
    ·
      refine ⟨78431709215333806989343051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104575612287111742652457401 78431709215333806989343051)
      ·
        refine ⟨117647563823000710484014577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78431709215333806989343051 117647563823000710484014577)
        ·
          refine ⟨88235672867250532863010933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117647563823000710484014577 88235672867250532863010933)
          ·
            refine ⟨8272094331304737455907275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88235672867250532863010933 8272094331304737455907275)
            ·
              refine ⟨12408141496957106183860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272094331304737455907275 12408141496957106183860913)
              ·
                refine ⟨9306106122717829637895685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12408141496957106183860913 9306106122717829637895685)
                ·
                  refine ⟨1744894898009593057105441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9306106122717829637895685 1744894898009593057105441)
                  ·
                    refine ⟨1308671173507194792829081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1744894898009593057105441 1308671173507194792829081)
                    ·
                      refine ⟨981503380130396094621811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308671173507194792829081 981503380130396094621811)
                      ·
                        rfl

theorem cell23_1911471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2, 2].length) (baseStart_1911471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911471 prefixEnd_1911471 := by exact prefixLift 1911471
  have htrace : WordTrace (prefixWord ++ tailWord_1911471) baseStart_1911471 baseEnd_1911471 := by
    simpa [prefixWord, tailWord_1911471, baseEnd_1911471] using wordTrace_append hprefix tailTrace_1911471
  have hstable : (prefixWord ++ tailWord_1911471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911471).length < 2 ^ (prefixWord ++ tailWord_1911471).sum := by decide
  have hdescent : baseEnd_1911471 < baseStart_1911471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911524 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1911524 : Nat := 118140960795 + 1911524 * 2 ^ 59
def prefixEnd_1911524 : Nat := 4983230072969 + 3 ^ 40 * 1911524 * 2
def baseEnd_1911524 : Nat := 327176864868361462419689

theorem tailTrace_1911524 : CollatzResearch.WordTrace tailWord_1911524 prefixEnd_1911524 327176864868361462419689 := by
  unfold tailWord_1911524
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859503963441242576658813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46479338617921656768878417 34859503963441242576658813)
  ·
    refine ⟨13072313986290465966247055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34859503963441242576658813 13072313986290465966247055)
    ·
      refine ⟨19608470979435698949370583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13072313986290465966247055 19608470979435698949370583)
      ·
        refine ⟨29412706469153548424055875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19608470979435698949370583 29412706469153548424055875)
        ·
          refine ⟨44119059703730322636083813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29412706469153548424055875 44119059703730322636083813)
          ·
            refine ⟨8272323694449435494265715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44119059703730322636083813 8272323694449435494265715)
            ·
              refine ⟨12408485541674153241398573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272323694449435494265715 12408485541674153241398573)
              ·
                refine ⟨4653182078127807465524465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12408485541674153241398573 4653182078127807465524465)
                ·
                  refine ⟨3489886558595855599143349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653182078127807465524465 3489886558595855599143349)
                  ·
                    refine ⟨327176864868361462419689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3489886558595855599143349 327176864868361462419689)
                    ·
                      rfl

theorem cell23_1911524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1911524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911524 prefixEnd_1911524 := by exact prefixLift 1911524
  have htrace : WordTrace (prefixWord ++ tailWord_1911524) baseStart_1911524 baseEnd_1911524 := by
    simpa [prefixWord, tailWord_1911524, baseEnd_1911524] using wordTrace_append hprefix tailTrace_1911524
  have hstable : (prefixWord ++ tailWord_1911524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911524).length < 2 ^ (prefixWord ++ tailWord_1911524).sum := by decide
  have hdescent : baseEnd_1911524 < baseStart_1911524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911534 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1911534 : Nat := 118140960795 + 1911534 * 2 ^ 59
def prefixEnd_1911534 : Nat := 4983230072969 + 3 ^ 40 * 1911534 * 2
def baseEnd_1911534 : Nat := 981535729411629348134021

theorem tailTrace_1911534 : CollatzResearch.WordTrace tailWord_1911534 prefixEnd_1911534 981535729411629348134021 := by
  unfold tailWord_1911534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714921582105782107647707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46479581771230837907454437 8714921582105782107647707)
  ·
    refine ⟨13072382373158673161471561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8714921582105782107647707 13072382373158673161471561)
    ·
      refine ⟨9804286779869004871103671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13072382373158673161471561 9804286779869004871103671)
      ·
        refine ⟨14706430169803507306655507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9804286779869004871103671 14706430169803507306655507)
        ·
          refine ⟨22059645254705260959983261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706430169803507306655507 22059645254705260959983261)
          ·
            refine ⟨8272366970514472859993723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22059645254705260959983261 8272366970514472859993723)
            ·
              refine ⟨12408550455771709289990585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272366970514472859993723 12408550455771709289990585)
              ·
                refine ⟨9306412841828781967492939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12408550455771709289990585 9306412841828781967492939)
                ·
                  refine ⟨13959619262743172951239409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306412841828781967492939 13959619262743172951239409)
                  ·
                    refine ⟨10469714447057379713429557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13959619262743172951239409 10469714447057379713429557)
                    ·
                      refine ⟨981535729411629348134021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10469714447057379713429557 981535729411629348134021)
                      ·
                        rfl

theorem cell23_1911534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1911534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911534 prefixEnd_1911534 := by exact prefixLift 1911534
  have htrace : WordTrace (prefixWord ++ tailWord_1911534) baseStart_1911534 baseEnd_1911534 := by
    simpa [prefixWord, tailWord_1911534, baseEnd_1911534] using wordTrace_append hprefix tailTrace_1911534
  have hstable : (prefixWord ++ tailWord_1911534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911534).length < 2 ^ (prefixWord ++ tailWord_1911534).sum := by decide
  have hdescent : baseEnd_1911534 < baseStart_1911534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911544 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1911544 : Nat := 118140960795 + 1911544 * 2 ^ 59
def prefixEnd_1911544 : Nat := 4983230072969 + 3 ^ 40 * 1911544 * 2
def baseEnd_1911544 : Nat := 981540864218174309008975

theorem tailTrace_1911544 : CollatzResearch.WordTrace tailWord_1911544 prefixEnd_1911544 981540864218174309008975 := by
  unfold tailWord_1911544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859868693405014284522843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46479824924540019046030457 34859868693405014284522843)
  ·
    refine ⟨52289803040107521426784265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34859868693405014284522843 52289803040107521426784265)
    ·
      refine ⟨39217352280080641070088199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52289803040107521426784265 39217352280080641070088199)
      ·
        refine ⟨58826028420120961605132299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39217352280080641070088199 58826028420120961605132299)
        ·
          refine ⟨88239042630181442407698449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58826028420120961605132299 88239042630181442407698449)
          ·
            refine ⟨66179281972636081805773837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88239042630181442407698449 66179281972636081805773837)
            ·
              refine ⟨24817230739738530677165189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66179281972636081805773837 24817230739738530677165189)
              ·
                refine ⟨4653230763700974501968473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24817230739738530677165189 4653230763700974501968473)
                ·
                  refine ⟨3489923072775730876476355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653230763700974501968473 3489923072775730876476355)
                  ·
                    refine ⟨5234884609163596314714533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489923072775730876476355 5234884609163596314714533)
                    ·
                      refine ⟨981540864218174309008975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5234884609163596314714533 981540864218174309008975)
                      ·
                        rfl

theorem cell23_1911544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1911544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911544 prefixEnd_1911544 := by exact prefixLift 1911544
  have htrace : WordTrace (prefixWord ++ tailWord_1911544) baseStart_1911544 baseEnd_1911544 := by
    simpa [prefixWord, tailWord_1911544, baseEnd_1911544] using wordTrace_append hprefix tailTrace_1911544
  have hstable : (prefixWord ++ tailWord_1911544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911544).length < 2 ^ (prefixWord ++ tailWord_1911544).sum := by decide
  have hdescent : baseEnd_1911544 < baseStart_1911544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911564 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1911564 : Nat := 118140960795 + 1911564 * 2 ^ 59
def prefixEnd_1911564 : Nat := 4983230072969 + 3 ^ 40 * 1911564 * 2
def baseEnd_1911564 : Nat := 981551133831264230758883

theorem tailTrace_1911564 : CollatzResearch.WordTrace tailWord_1911564 prefixEnd_1911564 981551133831264230758883 := by
  unfold tailWord_1911564
  simp only [CollatzResearch.WordTrace]
  refine ⟨34860233423368785992386873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46480311231158381323182497 34860233423368785992386873)
  ·
    refine ⟨26145175067526589494290155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34860233423368785992386873 26145175067526589494290155)
    ·
      refine ⟨39217762601289884241435233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26145175067526589494290155 39217762601289884241435233)
      ·
        refine ⟨29413321950967413181076425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39217762601289884241435233 29413321950967413181076425)
        ·
          refine ⟨22059991463225559885807319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29413321950967413181076425 22059991463225559885807319)
          ·
            refine ⟨33089987194838339828710979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22059991463225559885807319 33089987194838339828710979)
            ·
              refine ⟨49634980792257509743066469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33089987194838339828710979 49634980792257509743066469)
              ·
                refine ⟨9306558898548283076824963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49634980792257509743066469 9306558898548283076824963)
                ·
                  refine ⟨13959838347822424615237445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306558898548283076824963 13959838347822424615237445)
                  ·
                    refine ⟨2617469690216704615357021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13959838347822424615237445 2617469690216704615357021)
                    ·
                      refine ⟨981551133831264230758883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617469690216704615357021 981551133831264230758883)
                      ·
                        rfl

theorem cell23_1911564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1911564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911564 prefixEnd_1911564 := by exact prefixLift 1911564
  have htrace : WordTrace (prefixWord ++ tailWord_1911564) baseStart_1911564 baseEnd_1911564 := by
    simpa [prefixWord, tailWord_1911564, baseEnd_1911564] using wordTrace_append hprefix tailTrace_1911564
  have hstable : (prefixWord ++ tailWord_1911564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911564).length < 2 ^ (prefixWord ++ tailWord_1911564).sum := by decide
  have hdescent : baseEnd_1911564 < baseStart_1911564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911621 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_1911621 : Nat := 118140960795 + 1911621 * 2 ^ 59
def prefixEnd_1911621 : Nat := 4983230072969 + 3 ^ 40 * 1911621 * 2
def baseEnd_1911621 : Nat := 981580402228570507746121

theorem tailTrace_1911621 : CollatzResearch.WordTrace tailWord_1911621 prefixEnd_1911621 981580402228570507746121 := by
  unfold tailWord_1911621
  simp only [CollatzResearch.WordTrace]
  refine ⟨69722545807531070719598717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46481697205020713813065811 69722545807531070719598717)
  ·
    refine ⟨26145954677824151519849519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69722545807531070719598717 26145954677824151519849519)
    ·
      refine ⟨39218932016736227279774279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26145954677824151519849519 39218932016736227279774279)
      ·
        refine ⟨58828398025104340919661419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39218932016736227279774279 58828398025104340919661419)
        ·
          refine ⟨88242597037656511379492129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58828398025104340919661419 88242597037656511379492129)
          ·
            refine ⟨66181947778242383534619097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88242597037656511379492129 66181947778242383534619097)
            ·
              refine ⟨49636460833681787650964323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66181947778242383534619097 49636460833681787650964323)
              ·
                refine ⟨74454691250522681476446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49636460833681787650964323 74454691250522681476446485)
                ·
                  refine ⟨3490063652368250694208429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74454691250522681476446485 3490063652368250694208429)
                  ·
                    refine ⟨1308773869638094010328161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490063652368250694208429 1308773869638094010328161)
                    ·
                      refine ⟨981580402228570507746121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308773869638094010328161 981580402228570507746121)
                      ·
                        rfl

theorem cell23_1911621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_1911621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911621 prefixEnd_1911621 := by exact prefixLift 1911621
  have htrace : WordTrace (prefixWord ++ tailWord_1911621) baseStart_1911621 baseEnd_1911621 := by
    simpa [prefixWord, tailWord_1911621, baseEnd_1911621] using wordTrace_append hprefix tailTrace_1911621
  have hstable : (prefixWord ++ tailWord_1911621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911621).length < 2 ^ (prefixWord ++ tailWord_1911621).sum := by decide
  have hdescent : baseEnd_1911621 < baseStart_1911621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911628 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1911628 : Nat := 118140960795 + 1911628 * 2 ^ 59
def prefixEnd_1911628 : Nat := 4983230072969 + 3 ^ 40 * 1911628 * 2
def baseEnd_1911628 : Nat := 981583996593151980358589

theorem tailTrace_1911628 : CollatzResearch.WordTrace tailWord_1911628 prefixEnd_1911628 981583996593151980358589 := by
  unfold tailWord_1911628
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861400559252855457551769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46481867412337140610069025 34861400559252855457551769)
  ·
    refine ⟨26146050419439641593163827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34861400559252855457551769 26146050419439641593163827)
    ·
      refine ⟨39219075629159462389745741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26146050419439641593163827 39219075629159462389745741)
      ·
        refine ⟨14707153360934798396154653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39219075629159462389745741 14707153360934798396154653)
        ·
          refine ⟨5515182510350549398557995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14707153360934798396154653 5515182510350549398557995)
          ·
            refine ⟨8272773765525824097836993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515182510350549398557995 8272773765525824097836993)
            ·
              refine ⟨6204580324144368073377745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272773765525824097836993 6204580324144368073377745)
              ·
                refine ⟨4653435243108276055033309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204580324144368073377745 4653435243108276055033309)
                ·
                  refine ⟨1745038216165603520637491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4653435243108276055033309 1745038216165603520637491)
                  ·
                    refine ⟨2617557324248405280956237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1745038216165603520637491 2617557324248405280956237)
                    ·
                      refine ⟨981583996593151980358589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617557324248405280956237 981583996593151980358589)
                      ·
                        rfl

theorem cell23_1911628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1911628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911628 prefixEnd_1911628 := by exact prefixLift 1911628
  have htrace : WordTrace (prefixWord ++ tailWord_1911628) baseStart_1911628 baseEnd_1911628 := by
    simpa [prefixWord, tailWord_1911628, baseEnd_1911628] using wordTrace_append hprefix tailTrace_1911628
  have hstable : (prefixWord ++ tailWord_1911628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911628).length < 2 ^ (prefixWord ++ tailWord_1911628).sum := by decide
  have hdescent : baseEnd_1911628 < baseStart_1911628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911662 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1911662 : Nat := 118140960795 + 1911662 * 2 ^ 59
def prefixEnd_1911662 : Nat := 4983230072969 + 3 ^ 40 * 1911662 * 2
def baseEnd_1911662 : Nat := 981601454935404847333433

theorem tailTrace_1911662 : CollatzResearch.WordTrace tailWord_1911662 prefixEnd_1911662 981601454935404847333433 := by
  unfold tailWord_1911662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715505150047816840230155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46482694133588356481227493 8715505150047816840230155)
  ·
    refine ⟨13073257725071725260345233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8715505150047816840230155 13073257725071725260345233)
    ·
      refine ⟨9804943293803793945258925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13073257725071725260345233 9804943293803793945258925)
      ·
        refine ⟨3676853735176422729472097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9804943293803793945258925 3676853735176422729472097)
        ·
          refine ⟨2757640301382317047104073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3676853735176422729472097 2757640301382317047104073)
          ·
            refine ⟨2068230226036737785328055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2757640301382317047104073 2068230226036737785328055)
            ·
              refine ⟨3102345339055106677992083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068230226036737785328055 3102345339055106677992083)
              ·
                refine ⟨4653518008582660016988125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102345339055106677992083 4653518008582660016988125)
                ·
                  refine ⟨1745069253218497506370547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4653518008582660016988125 1745069253218497506370547)
                  ·
                    refine ⟨2617603879827746259555821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1745069253218497506370547 2617603879827746259555821)
                    ·
                      refine ⟨981601454935404847333433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617603879827746259555821 981601454935404847333433)
                      ·
                        rfl

theorem cell23_1911662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1911662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911662 prefixEnd_1911662 := by exact prefixLift 1911662
  have htrace : WordTrace (prefixWord ++ tailWord_1911662) baseStart_1911662 baseEnd_1911662 := by
    simpa [prefixWord, tailWord_1911662, baseEnd_1911662] using wordTrace_append hprefix tailTrace_1911662
  have hstable : (prefixWord ++ tailWord_1911662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911662).length < 2 ^ (prefixWord ++ tailWord_1911662).sum := by decide
  have hdescent : baseEnd_1911662 < baseStart_1911662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911664 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1911664 : Nat := 118140960795 + 1911664 * 2 ^ 59
def prefixEnd_1911664 : Nat := 4983230072969 + 3 ^ 40 * 1911664 * 2
def baseEnd_1911664 : Nat := 981602481896713839508423

theorem tailTrace_1911664 : CollatzResearch.WordTrace tailWord_1911664 prefixEnd_1911664 981602481896713839508423 := by
  unfold tailWord_1911664
  simp only [CollatzResearch.WordTrace]
  refine ⟨34862057073187644531707023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46482742764250192708942697 34862057073187644531707023)
  ·
    refine ⟨52293085609781466797560535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34862057073187644531707023 52293085609781466797560535)
    ·
      refine ⟨78439628414672200196340803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52293085609781466797560535 78439628414672200196340803)
      ·
        refine ⟨117659442622008300294511205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78439628414672200196340803 117659442622008300294511205)
        ·
          refine ⟨22061145491626556305220851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117659442622008300294511205 22061145491626556305220851)
          ·
            refine ⟨33091718237439834457831277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061145491626556305220851 33091718237439834457831277)
            ·
              refine ⟨12409394339039937921686729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33091718237439834457831277 12409394339039937921686729)
              ·
                refine ⟨9307045754279953441265047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12409394339039937921686729 9307045754279953441265047)
                ·
                  refine ⟨13960568631419930161897571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307045754279953441265047 13960568631419930161897571)
                  ·
                    refine ⟨20940852947129895242846357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13960568631419930161897571 20940852947129895242846357)
                    ·
                      refine ⟨981602481896713839508423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20940852947129895242846357 981602481896713839508423)
                      ·
                        rfl

theorem cell23_1911664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1911664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911664 prefixEnd_1911664 := by exact prefixLift 1911664
  have htrace : WordTrace (prefixWord ++ tailWord_1911664) baseStart_1911664 baseEnd_1911664 := by
    simpa [prefixWord, tailWord_1911664, baseEnd_1911664] using wordTrace_append hprefix tailTrace_1911664
  have hstable : (prefixWord ++ tailWord_1911664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911664).length < 2 ^ (prefixWord ++ tailWord_1911664).sum := by decide
  have hdescent : baseEnd_1911664 < baseStart_1911664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911688 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1911688 : Nat := 118140960795 + 1911688 * 2 ^ 59
def prefixEnd_1911688 : Nat := 4983230072969 + 3 ^ 40 * 1911688 * 2
def baseEnd_1911688 : Nat := 981614805432421745608313

theorem tailTrace_1911688 : CollatzResearch.WordTrace tailWord_1911688 prefixEnd_1911688 981614805432421745608313 := by
  unfold tailWord_1911688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34862494749144170581143859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46483326332192227441525145 34862494749144170581143859)
  ·
    refine ⟨52293742123716255871715789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34862494749144170581143859 52293742123716255871715789)
    ·
      refine ⟨19610153296393595951893421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52293742123716255871715789 19610153296393595951893421)
      ·
        refine ⟨7353807486147598481960033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19610153296393595951893421 7353807486147598481960033)
        ·
          refine ⟨5515355614610698861470025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7353807486147598481960033 5515355614610698861470025)
          ·
            refine ⟨4136516710958024146102519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515355614610698861470025 4136516710958024146102519)
            ·
              refine ⟨6204775066437036219153779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136516710958024146102519 6204775066437036219153779)
              ·
                refine ⟨9307162599655554328730669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204775066437036219153779 9307162599655554328730669)
                ·
                  refine ⟨3490185974870832873274001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9307162599655554328730669 3490185974870832873274001)
                  ·
                    refine ⟨2617639481153124654955501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3490185974870832873274001 2617639481153124654955501)
                    ·
                      refine ⟨981614805432421745608313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617639481153124654955501 981614805432421745608313)
                      ·
                        rfl

theorem cell23_1911688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1911688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911688 prefixEnd_1911688 := by exact prefixLift 1911688
  have htrace : WordTrace (prefixWord ++ tailWord_1911688) baseStart_1911688 baseEnd_1911688 := by
    simpa [prefixWord, tailWord_1911688, baseEnd_1911688] using wordTrace_append hprefix tailTrace_1911688
  have hstable : (prefixWord ++ tailWord_1911688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911688).length < 2 ^ (prefixWord ++ tailWord_1911688).sum := by decide
  have hdescent : baseEnd_1911688 < baseStart_1911688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911701 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1911701 : Nat := 118140960795 + 1911701 * 2 ^ 59
def prefixEnd_1911701 : Nat := 4983230072969 + 3 ^ 40 * 1911701 * 2
def baseEnd_1911701 : Nat := 981621480680930194745753

theorem tailTrace_1911701 : CollatzResearch.WordTrace tailWord_1911701 prefixEnd_1911701 981621480680930194745753 := by
  unfold tailWord_1911701
  simp only [CollatzResearch.WordTrace]
  refine ⟨69725463647241244382510957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46483642431494162921673971 69725463647241244382510957)
  ·
    refine ⟨26147048867715466643441609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69725463647241244382510957 26147048867715466643441609)
    ·
      refine ⟨19610286650786599982581207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26147048867715466643441609 19610286650786599982581207)
      ·
        refine ⟨29415429976179899973871811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610286650786599982581207 29415429976179899973871811)
        ·
          refine ⟨44123144964269849960807717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29415429976179899973871811 44123144964269849960807717)
          ·
            refine ⟨8273089680800596867651447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44123144964269849960807717 8273089680800596867651447)
            ·
              refine ⟨12409634521200895301477171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273089680800596867651447 12409634521200895301477171)
              ·
                refine ⟨18614451781801342952215757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12409634521200895301477171 18614451781801342952215757)
                ·
                  refine ⟨6980419418175503607080909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18614451781801342952215757 6980419418175503607080909)
                  ·
                    refine ⟨2617657281815813852655341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6980419418175503607080909 2617657281815813852655341)
                    ·
                      refine ⟨981621480680930194745753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2617657281815813852655341 981621480680930194745753)
                      ·
                        rfl

theorem cell23_1911701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1911701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911701 prefixEnd_1911701 := by exact prefixLift 1911701
  have htrace : WordTrace (prefixWord ++ tailWord_1911701) baseStart_1911701 baseEnd_1911701 := by
    simpa [prefixWord, tailWord_1911701, baseEnd_1911701] using wordTrace_append hprefix tailTrace_1911701
  have hstable : (prefixWord ++ tailWord_1911701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911701).length < 2 ^ (prefixWord ++ tailWord_1911701).sum := by decide
  have hdescent : baseEnd_1911701 < baseStart_1911701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911719 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1911719 : Nat := 118140960795 + 1911719 * 2 ^ 59
def prefixEnd_1911719 : Nat := 4983230072969 + 3 ^ 40 * 1911719 * 2
def baseEnd_1911719 : Nat := 981630723332711124320671

theorem tailTrace_1911719 : CollatzResearch.WordTrace tailWord_1911719 prefixEnd_1911719 981630723332711124320671 := by
  unfold tailWord_1911719
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726120161176033456666211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46484080107450688971110807 69726120161176033456666211)
  ·
    refine ⟨104589180241764050184999317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69726120161176033456666211 104589180241764050184999317)
    ·
      refine ⟨4902617823832689852421843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104589180241764050184999317 4902617823832689852421843)
      ·
        refine ⟨7353926735749034778632765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902617823832689852421843 7353926735749034778632765)
        ·
          refine ⟨2757722525905888041987287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7353926735749034778632765 2757722525905888041987287)
          ·
            refine ⟨4136583788858832062980931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757722525905888041987287 4136583788858832062980931)
            ·
              refine ⟨6204875683288248094471397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136583788858832062980931 6204875683288248094471397)
              ·
                refine ⟨1163414190616546517713387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6204875683288248094471397 1163414190616546517713387)
                ·
                  refine ⟨1745121285924819776570081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163414190616546517713387 1745121285924819776570081)
                  ·
                    refine ⟨1308840964443614832427561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745121285924819776570081 1308840964443614832427561)
                    ·
                      refine ⟨981630723332711124320671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308840964443614832427561 981630723332711124320671)
                      ·
                        rfl

theorem cell23_1911719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1911719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911719 prefixEnd_1911719 := by exact prefixLift 1911719
  have htrace : WordTrace (prefixWord ++ tailWord_1911719) baseStart_1911719 baseEnd_1911719 := by
    simpa [prefixWord, tailWord_1911719, baseEnd_1911719] using wordTrace_append hprefix tailTrace_1911719
  have hstable : (prefixWord ++ tailWord_1911719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911719).length < 2 ^ (prefixWord ++ tailWord_1911719).sum := by decide
  have hdescent : baseEnd_1911719 < baseStart_1911719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911725 : List Nat := [1, 5, 2, 3, 1, 2, 1, 8]
def baseStart_1911725 : Nat := 118140960795 + 1911725 * 2 ^ 59
def prefixEnd_1911725 : Nat := 4983230072969 + 3 ^ 40 * 1911725 * 2
def baseEnd_1911725 : Nat := 36356807563579188920209

theorem tailTrace_1911725 : CollatzResearch.WordTrace tailWord_1911725 prefixEnd_1911725 36356807563579188920209 := by
  unfold tailWord_1911725
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726338999154296481384629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46484225999436197654256419 69726338999154296481384629)
  ·
    refine ⟨6536844281170715295129809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69726338999154296481384629 6536844281170715295129809)
    ·
      refine ⟨4902633210878036471347357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536844281170715295129809 4902633210878036471347357)
      ·
        refine ⟨1838487454079263676755259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4902633210878036471347357 1838487454079263676755259)
        ·
          refine ⟨2757731181118895515132889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838487454079263676755259 2757731181118895515132889)
          ·
            refine ⟨2068298385839171636349667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2757731181118895515132889 2068298385839171636349667)
            ·
              refine ⟨3102447578758757454524501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068298385839171636349667 3102447578758757454524501)
              ·
                refine ⟨36356807563579188920209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3102447578758757454524501 36356807563579188920209)
                ·
                  rfl

theorem cell23_1911725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 8].length) (baseStart_1911725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911725 prefixEnd_1911725 := by exact prefixLift 1911725
  have htrace : WordTrace (prefixWord ++ tailWord_1911725) baseStart_1911725 baseEnd_1911725 := by
    simpa [prefixWord, tailWord_1911725, baseEnd_1911725] using wordTrace_append hprefix tailTrace_1911725
  have hstable : (prefixWord ++ tailWord_1911725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911725).length < 2 ^ (prefixWord ++ tailWord_1911725).sum := by decide
  have hdescent : baseEnd_1911725 < baseStart_1911725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911762 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1911762 : Nat := 118140960795 + 1911762 * 2 ^ 59
def prefixEnd_1911762 : Nat := 4983230072969 + 3 ^ 40 * 1911762 * 2
def baseEnd_1911762 : Nat := 981652803000854456082973

theorem tailTrace_1911762 : CollatzResearch.WordTrace tailWord_1911762 prefixEnd_1911762 981652803000854456082973 := by
  unfold tailWord_1911762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431922125005062950120385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46485125666680167866987693 17431922125005062950120385)
  ·
    refine ⟨13073941593753797212590289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17431922125005062950120385 13073941593753797212590289)
    ·
      refine ⟨9805456195315347909442717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13073941593753797212590289 9805456195315347909442717)
      ·
        refine ⟨3677046073243255466041019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9805456195315347909442717 3677046073243255466041019)
        ·
          refine ⟨5515569109864883199061529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677046073243255466041019 5515569109864883199061529)
          ·
            refine ⟨4136676832398662399296147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515569109864883199061529 4136676832398662399296147)
            ·
              refine ⟨6205015248597993598944221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136676832398662399296147 6205015248597993598944221)
              ·
                refine ⟨2326880718224247599604083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6205015248597993598944221 2326880718224247599604083)
                ·
                  refine ⟨3490321077336371399406125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326880718224247599604083 3490321077336371399406125)
                  ·
                    refine ⟨1308870404001139274777297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490321077336371399406125 1308870404001139274777297)
                    ·
                      refine ⟨981652803000854456082973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1308870404001139274777297 981652803000854456082973)
                      ·
                        rfl

theorem cell23_1911762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1911762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911762 prefixEnd_1911762 := by exact prefixLift 1911762
  have htrace : WordTrace (prefixWord ++ tailWord_1911762) baseStart_1911762 baseEnd_1911762 := by
    simpa [prefixWord, tailWord_1911762, baseEnd_1911762] using wordTrace_append hprefix tailTrace_1911762
  have hstable : (prefixWord ++ tailWord_1911762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911762).length < 2 ^ (prefixWord ++ tailWord_1911762).sum := by decide
  have hdescent : baseEnd_1911762 < baseStart_1911762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911798 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1911798 : Nat := 118140960795 + 1911798 * 2 ^ 59
def prefixEnd_1911798 : Nat := 4983230072969 + 3 ^ 40 * 1911798 * 2
def baseEnd_1911798 : Nat := 109074587589379590581423

theorem tailTrace_1911798 : CollatzResearch.WordTrace tailWord_1911798 prefixEnd_1911798 109074587589379590581423 := by
  unfold tailWord_1911798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358062595493114371799503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46486001018593219965861365 4358062595493114371799503)
  ·
    refine ⟨6537093893239671557699255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4358062595493114371799503 6537093893239671557699255)
    ·
      refine ⟨9805640839859507336548883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537093893239671557699255 9805640839859507336548883)
      ·
        refine ⟨14708461259789261004823325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805640839859507336548883 14708461259789261004823325)
        ·
          refine ⟨5515672972420972876808747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14708461259789261004823325 5515672972420972876808747)
          ·
            refine ⟨8273509458631459315213121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515672972420972876808747 8273509458631459315213121)
            ·
              refine ⟨6205132093973594486409841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273509458631459315213121 6205132093973594486409841)
              ·
                refine ⟨4653849070480195864807381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205132093973594486409841 4653849070480195864807381)
                ·
                  refine ⟨109074587589379590581423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4653849070480195864807381 109074587589379590581423)
                  ·
                    rfl

theorem cell23_1911798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1911798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911798 prefixEnd_1911798 := by exact prefixLift 1911798
  have htrace : WordTrace (prefixWord ++ tailWord_1911798) baseStart_1911798 baseEnd_1911798 := by
    simpa [prefixWord, tailWord_1911798, baseEnd_1911798] using wordTrace_append hprefix tailTrace_1911798
  have hstable : (prefixWord ++ tailWord_1911798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911798).length < 2 ^ (prefixWord ++ tailWord_1911798).sum := by decide
  have hdescent : baseEnd_1911798 < baseStart_1911798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911858 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1911858 : Nat := 118140960795 + 1911858 * 2 ^ 59
def prefixEnd_1911858 : Nat := 4983230072969 + 3 ^ 40 * 1911858 * 2
def baseEnd_1911858 : Nat := 327234032381228693494177

theorem tailTrace_1911858 : CollatzResearch.WordTrace tailWord_1911858 prefixEnd_1911858 327234032381228693494177 := by
  unfold tailWord_1911858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432797476918115048994057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46487459938448306797317485 17432797476918115048994057)
  ·
    refine ⟨13074598107688586286745543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17432797476918115048994057 13074598107688586286745543)
    ·
      refine ⟨19611897161532879430118315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074598107688586286745543 19611897161532879430118315)
      ·
        refine ⟨29417845742299319145177473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611897161532879430118315 29417845742299319145177473)
        ·
          refine ⟨22063384306724489358883105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29417845742299319145177473 22063384306724489358883105)
          ·
            refine ⟨16547538230043367019162329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22063384306724489358883105 16547538230043367019162329)
            ·
              refine ⟨12410653672532525264371747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547538230043367019162329 12410653672532525264371747)
              ·
                refine ⟨18615980508798787896557621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410653672532525264371747 18615980508798787896557621)
                ·
                  refine ⟨1745248172699886365302277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18615980508798787896557621 1745248172699886365302277)
                  ·
                    refine ⟨327234032381228693494177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745248172699886365302277 327234032381228693494177)
                    ·
                      rfl

theorem cell23_1911858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1911858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911858 prefixEnd_1911858 := by exact prefixLift 1911858
  have htrace : WordTrace (prefixWord ++ tailWord_1911858) baseStart_1911858 baseEnd_1911858 := by
    simpa [prefixWord, tailWord_1911858, baseEnd_1911858] using wordTrace_append hprefix tailTrace_1911858
  have hstable : (prefixWord ++ tailWord_1911858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911858).length < 2 ^ (prefixWord ++ tailWord_1911858).sum := by decide
  have hdescent : baseEnd_1911858 < baseStart_1911858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911861 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1911861 : Nat := 118140960795 + 1911861 * 2 ^ 59
def prefixEnd_1911861 : Nat := 4983230072969 + 3 ^ 40 * 1911861 * 2
def baseEnd_1911861 : Nat := 981703637585649568745017

theorem tailTrace_1911861 : CollatzResearch.WordTrace tailWord_1911861 prefixEnd_1911861 981703637585649568745017 := by
  unfold tailWord_1911861
  simp only [CollatzResearch.WordTrace]
  refine ⟨69731299326661591708335437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46487532884441061138890291 69731299326661591708335437)
  ·
    refine ⟨26149237247498096890625789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69731299326661591708335437 26149237247498096890625789)
    ·
      refine ⟨9805963967811786333984671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26149237247498096890625789 9805963967811786333984671)
      ·
        refine ⟨14708945951717679500977007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805963967811786333984671 14708945951717679500977007)
        ·
          refine ⟨22063418927576519251465511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14708945951717679500977007 22063418927576519251465511)
          ·
            refine ⟨33095128391364778877198267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063418927576519251465511 33095128391364778877198267)
            ·
              refine ⟨49642692587047168315797401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33095128391364778877198267 49642692587047168315797401)
              ·
                refine ⟨37232019440285376236848051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49642692587047168315797401 37232019440285376236848051)
                ·
                  refine ⟨55848029160428064355272077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37232019440285376236848051 55848029160428064355272077)
                  ·
                    refine ⟨20943010935160524133227029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55848029160428064355272077 20943010935160524133227029)
                    ·
                      refine ⟨981703637585649568745017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20943010935160524133227029 981703637585649568745017)
                      ·
                        rfl

theorem cell23_1911861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1911861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911861 prefixEnd_1911861 := by exact prefixLift 1911861
  have htrace : WordTrace (prefixWord ++ tailWord_1911861) baseStart_1911861 baseEnd_1911861 := by
    simpa [prefixWord, tailWord_1911861, baseEnd_1911861] using wordTrace_append hprefix tailTrace_1911861
  have hstable : (prefixWord ++ tailWord_1911861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911861).length < 2 ^ (prefixWord ++ tailWord_1911861).sum := by decide
  have hdescent : baseEnd_1911861 < baseStart_1911861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911865 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1911865 : Nat := 118140960795 + 1911865 * 2 ^ 59
def prefixEnd_1911865 : Nat := 4983230072969 + 3 ^ 40 * 1911865 * 2
def baseEnd_1911865 : Nat := 981705691508267553094999

theorem tailTrace_1911865 : CollatzResearch.WordTrace tailWord_1911865 prefixEnd_1911865 981705691508267553094999 := by
  unfold tailWord_1911865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69731445218647100391481049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46487630145764733594320699 69731445218647100391481049)
  ·
    refine ⟨52298583913985325293610787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69731445218647100391481049 52298583913985325293610787)
    ·
      refine ⟨78447875870977987940416181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52298583913985325293610787 78447875870977987940416181)
      ·
        refine ⟨7354488362904186369414017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78447875870977987940416181 7354488362904186369414017)
        ·
          refine ⟨5515866272178139777060513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7354488362904186369414017 5515866272178139777060513)
          ·
            refine ⟨4136899704133604832795385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515866272178139777060513 4136899704133604832795385)
            ·
              refine ⟨3102674778100203624596539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136899704133604832795385 3102674778100203624596539)
              ·
                refine ⟨4654012167150305436894809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102674778100203624596539 4654012167150305436894809)
                ·
                  refine ⟨3490509125362729077671107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654012167150305436894809 3490509125362729077671107)
                  ·
                    refine ⟨5235763688044093616506661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490509125362729077671107 5235763688044093616506661)
                    ·
                      refine ⟨981705691508267553094999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5235763688044093616506661 981705691508267553094999)
                      ·
                        rfl

theorem cell23_1911865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1911865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911865 prefixEnd_1911865 := by exact prefixLift 1911865
  have htrace : WordTrace (prefixWord ++ tailWord_1911865) baseStart_1911865 baseEnd_1911865 := by
    simpa [prefixWord, tailWord_1911865, baseEnd_1911865] using wordTrace_append hprefix tailTrace_1911865
  have hstable : (prefixWord ++ tailWord_1911865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911865).length < 2 ^ (prefixWord ++ tailWord_1911865).sum := by decide
  have hdescent : baseEnd_1911865 < baseStart_1911865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911875 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 1, 4]
def baseStart_1911875 : Nat := 118140960795 + 1911875 * 2 ^ 59
def prefixEnd_1911875 : Nat := 4983230072969 + 3 ^ 40 * 1911875 * 2
def baseEnd_1911875 : Nat := 327236942104937504656651

theorem tailTrace_1911875 : CollatzResearch.WordTrace tailWord_1911875 prefixEnd_1911875 327236942104937504656651 := by
  unfold tailWord_1911875
  simp only [CollatzResearch.WordTrace]
  refine ⟨69731809948610872099345079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46487873299073914732896719 69731809948610872099345079)
  ·
    refine ⟨104597714922916308149017619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69731809948610872099345079 104597714922916308149017619)
    ·
      refine ⟨156896572384374462223526429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104597714922916308149017619 156896572384374462223526429)
      ·
        refine ⟨58836214644140423333822411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156896572384374462223526429 58836214644140423333822411)
        ·
          refine ⟨88254321966210635000733617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58836214644140423333822411 88254321966210635000733617)
          ·
            refine ⟨66190741474657976250550213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88254321966210635000733617 66190741474657976250550213)
            ·
              refine ⟨12410764026498370546978165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66190741474657976250550213 12410764026498370546978165)
              ·
                refine ⟨1163509127484222238779203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12410764026498370546978165 1163509127484222238779203)
                ·
                  refine ⟨1745263691226333358168805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163509127484222238779203 1745263691226333358168805)
                  ·
                    refine ⟨327236942104937504656651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745263691226333358168805 327236942104937504656651)
                    ·
                      rfl

theorem cell23_1911875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 4].length) (baseStart_1911875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911875 prefixEnd_1911875 := by exact prefixLift 1911875
  have htrace : WordTrace (prefixWord ++ tailWord_1911875) baseStart_1911875 baseEnd_1911875 := by
    simpa [prefixWord, tailWord_1911875, baseEnd_1911875] using wordTrace_append hprefix tailTrace_1911875
  have hstable : (prefixWord ++ tailWord_1911875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911875).length < 2 ^ (prefixWord ++ tailWord_1911875).sum := by decide
  have hdescent : baseEnd_1911875 < baseStart_1911875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911951 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1911951 : Nat := 118140960795 + 1911951 * 2 ^ 59
def prefixEnd_1911951 : Nat := 4983230072969 + 3 ^ 40 * 1911951 * 2
def baseEnd_1911951 : Nat := 981749850844554216619603

theorem tailTrace_1911951 : CollatzResearch.WordTrace tailWord_1911951 prefixEnd_1911951 981749850844554216619603 := by
  unfold tailWord_1911951
  simp only [CollatzResearch.WordTrace]
  refine ⟨69734581896335537079111707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46489721264223691386074471 69734581896335537079111707)
  ·
    refine ⟨104601872844503305618667561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69734581896335537079111707 104601872844503305618667561)
    ·
      refine ⟨78451404633377479214000671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104601872844503305618667561 78451404633377479214000671)
      ·
        refine ⟨117677106950066218821001007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78451404633377479214000671 117677106950066218821001007)
        ·
          refine ⟨176515660425099328231501511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117677106950066218821001007 176515660425099328231501511)
          ·
            refine ⟨264773490637648992347252267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176515660425099328231501511 264773490637648992347252267)
            ·
              refine ⟨397160235956473488520878401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264773490637648992347252267 397160235956473488520878401)
              ·
                refine ⟨297870176967355116390658801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397160235956473488520878401 297870176967355116390658801)
                ·
                  refine ⟨223402632725516337292994101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297870176967355116390658801 223402632725516337292994101)
                  ·
                    refine ⟨20943996818017156621218197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223402632725516337292994101 20943996818017156621218197)
                    ·
                      refine ⟨981749850844554216619603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20943996818017156621218197 981749850844554216619603)
                      ·
                        rfl

theorem cell23_1911951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1911951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911951 prefixEnd_1911951 := by exact prefixLift 1911951
  have htrace : WordTrace (prefixWord ++ tailWord_1911951) baseStart_1911951 baseEnd_1911951 := by
    simpa [prefixWord, tailWord_1911951, baseEnd_1911951] using wordTrace_append hprefix tailTrace_1911951
  have hstable : (prefixWord ++ tailWord_1911951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911951).length < 2 ^ (prefixWord ++ tailWord_1911951).sum := by decide
  have hdescent : baseEnd_1911951 < baseStart_1911951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911968 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1911968 : Nat := 118140960795 + 1911968 * 2 ^ 59
def prefixEnd_1911968 : Nat := 4983230072969 + 3 ^ 40 * 1911968 * 2
def baseEnd_1911968 : Nat := 981758580015680650107025

theorem tailTrace_1911968 : CollatzResearch.WordTrace tailWord_1911968 prefixEnd_1911968 981758580015680650107025 := by
  unfold tailWord_1911968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867600968636974491240279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46490134624849299321653705 34867600968636974491240279)
  ·
    refine ⟨52301401452955461736860419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34867600968636974491240279 52301401452955461736860419)
    ·
      refine ⟨78452102179433192605290629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52301401452955461736860419 78452102179433192605290629)
      ·
        refine ⟨14709769158643723613491993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78452102179433192605290629 14709769158643723613491993)
        ·
          refine ⟨11032326868982792710118995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14709769158643723613491993 11032326868982792710118995)
          ·
            refine ⟨16548490303474189065178493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032326868982792710118995 16548490303474189065178493)
            ·
              refine ⟨6205683863802820899441935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16548490303474189065178493 6205683863802820899441935)
              ·
                refine ⟨9308525795704231349162903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205683863802820899441935 9308525795704231349162903)
                ·
                  refine ⟨13962788693556347023744355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308525795704231349162903 13962788693556347023744355)
                  ·
                    refine ⟨20944183040334520535616533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13962788693556347023744355 20944183040334520535616533)
                    ·
                      refine ⟨981758580015680650107025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20944183040334520535616533 981758580015680650107025)
                      ·
                        rfl

theorem cell23_1911968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1911968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911968 prefixEnd_1911968 := by exact prefixLift 1911968
  have htrace : WordTrace (prefixWord ++ tailWord_1911968) baseStart_1911968 baseEnd_1911968 := by
    simpa [prefixWord, tailWord_1911968, baseEnd_1911968] using wordTrace_append hprefix tailTrace_1911968
  have hstable : (prefixWord ++ tailWord_1911968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911968).length < 2 ^ (prefixWord ++ tailWord_1911968).sum := by decide
  have hdescent : baseEnd_1911968 < baseStart_1911968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911972 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_1911972 : Nat := 118140960795 + 1911972 * 2 ^ 59
def prefixEnd_1911972 : Nat := 4983230072969 + 3 ^ 40 * 1911972 * 2
def baseEnd_1911972 : Nat := 981760633938298634457007

theorem tailTrace_1911972 : CollatzResearch.WordTrace tailWord_1911972 prefixEnd_1911972 981760633938298634457007 := by
  unfold tailWord_1911972
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867673914629728832813085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46490231886172971777084113 34867673914629728832813085)
  ·
    refine ⟨13075377717986148312304907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34867673914629728832813085 13075377717986148312304907)
    ·
      refine ⟨19613066576979222468457361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13075377717986148312304907 19613066576979222468457361)
      ·
        refine ⟨14709799932734416851343021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19613066576979222468457361 14709799932734416851343021)
        ·
          refine ⟨5516174974775406319253633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14709799932734416851343021 5516174974775406319253633)
          ·
            refine ⟨4137131231081554739440225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516174974775406319253633 4137131231081554739440225)
            ·
              refine ⟨3102848423311166054580169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137131231081554739440225 3102848423311166054580169)
              ·
                refine ⟨2327136317483374540935127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102848423311166054580169 2327136317483374540935127)
                ·
                  refine ⟨3490704476225061811402691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327136317483374540935127 3490704476225061811402691)
                  ·
                    refine ⟨5236056714337592717104037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490704476225061811402691 5236056714337592717104037)
                    ·
                      refine ⟨981760633938298634457007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5236056714337592717104037 981760633938298634457007)
                      ·
                        rfl

theorem cell23_1911972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_1911972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1911972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1911972 prefixEnd_1911972 := by exact prefixLift 1911972
  have htrace : WordTrace (prefixWord ++ tailWord_1911972) baseStart_1911972 baseEnd_1911972 := by
    simpa [prefixWord, tailWord_1911972, baseEnd_1911972] using wordTrace_append hprefix tailTrace_1911972
  have hstable : (prefixWord ++ tailWord_1911972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911972).length < 2 ^ (prefixWord ++ tailWord_1911972).sum := by decide
  have hdescent : baseEnd_1911972 < baseStart_1911972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912032 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2]
def baseStart_1912032 : Nat := 118140960795 + 1912032 * 2 ^ 59
def prefixEnd_1912032 : Nat := 4983230072969 + 3 ^ 40 * 1912032 * 2
def baseEnd_1912032 : Nat := 981791442777568399706731

theorem tailTrace_1912032 : CollatzResearch.WordTrace tailWord_1912032 prefixEnd_1912032 981791442777568399706731 := by
  unfold tailWord_1912032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34868768104521043956405175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46491690806028058608540233 34868768104521043956405175)
  ·
    refine ⟨52303152156781565934607763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34868768104521043956405175 52303152156781565934607763)
    ·
      refine ⟨78454728235172348901911645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52303152156781565934607763 78454728235172348901911645)
      ·
        refine ⟨29420523088189630838216867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78454728235172348901911645 29420523088189630838216867)
        ·
          refine ⟨44130784632284446257325301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29420523088189630838216867 44130784632284446257325301)
          ·
            refine ⟨4137261059276666836624247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44130784632284446257325301 4137261059276666836624247)
            ·
              refine ⟨6205891588915000254936371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137261059276666836624247 6205891588915000254936371)
              ·
                refine ⟨9308837383372500382404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205891588915000254936371 9308837383372500382404557)
                ·
                  refine ⟨3490814018764687643401709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9308837383372500382404557 3490814018764687643401709)
                  ·
                    refine ⟨1309055257036757866275641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490814018764687643401709 1309055257036757866275641)
                    ·
                      refine ⟨981791442777568399706731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309055257036757866275641 981791442777568399706731)
                      ·
                        rfl

theorem cell23_1912032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_1912032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912032 prefixEnd_1912032 := by exact prefixLift 1912032
  have htrace : WordTrace (prefixWord ++ tailWord_1912032) baseStart_1912032 baseEnd_1912032 := by
    simpa [prefixWord, tailWord_1912032, baseEnd_1912032] using wordTrace_append hprefix tailTrace_1912032
  have hstable : (prefixWord ++ tailWord_1912032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912032).length < 2 ^ (prefixWord ++ tailWord_1912032).sum := by decide
  have hdescent : baseEnd_1912032 < baseStart_1912032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912065 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1912065 : Nat := 118140960795 + 1912065 * 2 ^ 59
def prefixEnd_1912065 : Nat := 4983230072969 + 3 ^ 40 * 1912065 * 2
def baseEnd_1912065 : Nat := 981808387639166770594079

theorem tailTrace_1912065 : CollatzResearch.WordTrace tailWord_1912065 prefixEnd_1912065 981808387639166770594079 := by
  unfold tailWord_1912065
  simp only [CollatzResearch.WordTrace]
  refine ⟨69738739817922534548761649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46492493211948356365841099 69738739817922534548761649)
  ·
    refine ⟨52304054863441900911571237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69738739817922534548761649 52304054863441900911571237)
    ·
      refine ⟨9807010286895356420919607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52304054863441900911571237 9807010286895356420919607)
      ·
        refine ⟨14710515430343034631379411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9807010286895356420919607 14710515430343034631379411)
        ·
          refine ⟨22065773145514551947069117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14710515430343034631379411 22065773145514551947069117)
          ·
            refine ⟨8274664929567956980150919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22065773145514551947069117 8274664929567956980150919)
            ·
              refine ⟨12411997394351935470226379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274664929567956980150919 12411997394351935470226379)
              ·
                refine ⟨18617996091527903205339569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12411997394351935470226379 18617996091527903205339569)
                ·
                  refine ⟨13963497068645927404004677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18617996091527903205339569 13963497068645927404004677)
                  ·
                    refine ⟨2618155700371111388250877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13963497068645927404004677 2618155700371111388250877)
                    ·
                      refine ⟨981808387639166770594079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618155700371111388250877 981808387639166770594079)
                      ·
                        rfl

theorem cell23_1912065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1912065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912065 prefixEnd_1912065 := by exact prefixLift 1912065
  have htrace : WordTrace (prefixWord ++ tailWord_1912065) baseStart_1912065 baseEnd_1912065 := by
    simpa [prefixWord, tailWord_1912065, baseEnd_1912065] using wordTrace_append hprefix tailTrace_1912065
  have hstable : (prefixWord ++ tailWord_1912065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912065).length < 2 ^ (prefixWord ++ tailWord_1912065).sum := by decide
  have hdescent : baseEnd_1912065 < baseStart_1912065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912075 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_1912075 : Nat := 118140960795 + 1912075 * 2 ^ 59
def prefixEnd_1912075 : Nat := 4983230072969 + 3 ^ 40 * 1912075 * 2
def baseEnd_1912075 : Nat := 981813522445711731469033

theorem tailTrace_1912075 : CollatzResearch.WordTrace tailWord_1912075 prefixEnd_1912075 981813522445711731469033 := by
  unfold tailWord_1912075
  simp only [CollatzResearch.WordTrace]
  refine ⟨69739104547886306256625679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46492736365257537504417119 69739104547886306256625679)
  ·
    refine ⟨104608656821829459384938519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69739104547886306256625679 104608656821829459384938519)
    ·
      refine ⟨156912985232744189077407779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104608656821829459384938519 156912985232744189077407779)
      ·
        refine ⟨235369477849116283616111669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156912985232744189077407779 235369477849116283616111669)
        ·
          refine ⟨22065888548354651589010469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235369477849116283616111669 22065888548354651589010469)
          ·
            refine ⟨4137354102816497172939463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22065888548354651589010469 4137354102816497172939463)
            ·
              refine ⟨6206031154224745759409195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137354102816497172939463 6206031154224745759409195)
              ·
                refine ⟨9309046731337118639113793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206031154224745759409195 9309046731337118639113793)
                ·
                  refine ⟨6981785048502838979335345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9309046731337118639113793 6981785048502838979335345)
                  ·
                    refine ⟨5236338786377129234501509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981785048502838979335345 5236338786377129234501509)
                    ·
                      refine ⟨981813522445711731469033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5236338786377129234501509 981813522445711731469033)
                      ·
                        rfl

theorem cell23_1912075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_1912075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912075 prefixEnd_1912075 := by exact prefixLift 1912075
  have htrace : WordTrace (prefixWord ++ tailWord_1912075) baseStart_1912075 baseEnd_1912075 := by
    simpa [prefixWord, tailWord_1912075, baseEnd_1912075] using wordTrace_append hprefix tailTrace_1912075
  have hstable : (prefixWord ++ tailWord_1912075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912075).length < 2 ^ (prefixWord ++ tailWord_1912075).sum := by decide
  have hdescent : baseEnd_1912075 < baseStart_1912075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912132 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1912132 : Nat := 118140960795 + 1912132 * 2 ^ 59
def prefixEnd_1912132 : Nat := 4983230072969 + 3 ^ 40 * 1912132 * 2
def baseEnd_1912132 : Nat := 327280930281006002818757

theorem tailTrace_1912132 : CollatzResearch.WordTrace tailWord_1912132 prefixEnd_1912132 327280930281006002818757 := by
  unfold tailWord_1912132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870591754339902495725325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46494122339119869994300433 34870591754339902495725325)
  ·
    refine ⟨13076471907877463435896997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34870591754339902495725325 13076471907877463435896997)
    ·
      refine ⟨2451838482727024394230687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13076471907877463435896997 2451838482727024394230687)
      ·
        refine ⟨3677757724090536591346031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451838482727024394230687 3677757724090536591346031)
        ·
          refine ⟨5516636586135804887019047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677757724090536591346031 5516636586135804887019047)
          ·
            refine ⟨8274954879203707330528571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516636586135804887019047 8274954879203707330528571)
            ·
              refine ⟨12412432318805560995792857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274954879203707330528571 12412432318805560995792857)
              ·
                refine ⟨9309324239104170746844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12412432318805560995792857 9309324239104170746844643)
                ·
                  refine ⟨13963986358656256120266965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309324239104170746844643 13963986358656256120266965)
                  ·
                    refine ⟨327280930281006002818757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13963986358656256120266965 327280930281006002818757)
                    ·
                      rfl

theorem cell23_1912132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1912132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912132 prefixEnd_1912132 := by exact prefixLift 1912132
  have htrace : WordTrace (prefixWord ++ tailWord_1912132) baseStart_1912132 baseEnd_1912132 := by
    simpa [prefixWord, tailWord_1912132, baseEnd_1912132] using wordTrace_append hprefix tailTrace_1912132
  have hstable : (prefixWord ++ tailWord_1912132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912132).length < 2 ^ (prefixWord ++ tailWord_1912132).sum := by decide
  have hdescent : baseEnd_1912132 < baseStart_1912132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912135 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1912135 : Nat := 118140960795 + 1912135 * 2 ^ 59
def prefixEnd_1912135 : Nat := 4983230072969 + 3 ^ 40 * 1912135 * 2
def baseEnd_1912135 : Nat := 981844331284981496718757

theorem tailTrace_1912135 : CollatzResearch.WordTrace tailWord_1912135 prefixEnd_1912135 981844331284981496718757 := by
  unfold tailWord_1912135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69741292927668936503809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46494195285112624335873239 69741292927668936503809859)
  ·
    refine ⟨104611939391503404755714789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69741292927668936503809859 104611939391503404755714789)
    ·
      refine ⟨19614738635906888391696523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104611939391503404755714789 19614738635906888391696523)
      ·
        refine ⟨29422107953860332587544785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614738635906888391696523 29422107953860332587544785)
        ·
          refine ⟨22066580965395249440658589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29422107953860332587544785 22066580965395249440658589)
          ·
            refine ⟨8274967862023218540246971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22066580965395249440658589 8274967862023218540246971)
            ·
              refine ⟨12412451793034827810370457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274967862023218540246971 12412451793034827810370457)
              ·
                refine ⟨9309338844776120857777843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12412451793034827810370457 9309338844776120857777843)
                ·
                  refine ⟨13964008267164181286666765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309338844776120857777843 13964008267164181286666765)
                  ·
                    refine ⟨5236503100186567982500037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13964008267164181286666765 5236503100186567982500037)
                    ·
                      refine ⟨981844331284981496718757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5236503100186567982500037 981844331284981496718757)
                      ·
                        rfl

theorem cell23_1912135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1912135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912135 prefixEnd_1912135 := by exact prefixLift 1912135
  have htrace : WordTrace (prefixWord ++ tailWord_1912135) baseStart_1912135 baseEnd_1912135 := by
    simpa [prefixWord, tailWord_1912135, baseEnd_1912135] using wordTrace_append hprefix tailTrace_1912135
  have hstable : (prefixWord ++ tailWord_1912135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912135).length < 2 ^ (prefixWord ++ tailWord_1912135).sum := by decide
  have hdescent : baseEnd_1912135 < baseStart_1912135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912172 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1912172 : Nat := 118140960795 + 1912172 * 2 ^ 59
def prefixEnd_1912172 : Nat := 4983230072969 + 3 ^ 40 * 1912172 * 2
def baseEnd_1912172 : Nat := 981863330069197851956087

theorem tailTrace_1912172 : CollatzResearch.WordTrace tailWord_1912172 prefixEnd_1912172 981863330069197851956087 := by
  unfold tailWord_1912172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871321214267445911453385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46495094952356594548604513 34871321214267445911453385)
  ·
    refine ⟨26153490910700584433590039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34871321214267445911453385 26153490910700584433590039)
    ·
      refine ⟨39230236366050876650385059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26153490910700584433590039 39230236366050876650385059)
      ·
        refine ⟨58845354549076314975577589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39230236366050876650385059 58845354549076314975577589)
        ·
          refine ⟨5516751988975904528960399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58845354549076314975577589 5516751988975904528960399)
          ·
            refine ⟨8275127983463856793440599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516751988975904528960399 8275127983463856793440599)
            ·
              refine ⟨12412691975195785190160899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275127983463856793440599 12412691975195785190160899)
              ·
                refine ⟨18619037962793677785241349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412691975195785190160899 18619037962793677785241349)
                ·
                  refine ⟨3491069618023814584732753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18619037962793677785241349 3491069618023814584732753)
                  ·
                    refine ⟨2618302213517860938549565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491069618023814584732753 2618302213517860938549565)
                    ·
                      refine ⟨981863330069197851956087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618302213517860938549565 981863330069197851956087)
                      ·
                        rfl

theorem cell23_1912172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1912172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912172 prefixEnd_1912172 := by exact prefixLift 1912172
  have htrace : WordTrace (prefixWord ++ tailWord_1912172) baseStart_1912172 baseEnd_1912172 := by
    simpa [prefixWord, tailWord_1912172, baseEnd_1912172] using wordTrace_append hprefix tailTrace_1912172
  have hstable : (prefixWord ++ tailWord_1912172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912172).length < 2 ^ (prefixWord ++ tailWord_1912172).sum := by decide
  have hdescent : baseEnd_1912172 < baseStart_1912172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912175 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 6]
def baseStart_1912175 : Nat := 118140960795 + 1912175 * 2 ^ 59
def prefixEnd_1912175 : Nat := 4983230072969 + 3 ^ 40 * 1912175 * 2
def baseEnd_1912175 : Nat := 109096096723462371135397

theorem tailTrace_1912175 : CollatzResearch.WordTrace tailWord_1912175 prefixEnd_1912175 109096096723462371135397 := by
  unfold tailWord_1912175
  simp only [CollatzResearch.WordTrace]
  refine ⟨69742751847524023335265979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46495167898349348890177319 69742751847524023335265979)
  ·
    refine ⟨104614127771286035002898969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69742751847524023335265979 104614127771286035002898969)
    ·
      refine ⟨78460595828464526252174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104614127771286035002898969 78460595828464526252174227)
      ·
        refine ⟨117690893742696789378261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78460595828464526252174227 117690893742696789378261341)
        ·
          refine ⟨44134085153511296016848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117690893742696789378261341 44134085153511296016848003)
          ·
            refine ⟨66201127730266944025272005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44134085153511296016848003 66201127730266944025272005)
            ·
              refine ⟨12412711449425052004738501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66201127730266944025272005 12412711449425052004738501)
              ·
                refine ⟨2327383396767197250888469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12412711449425052004738501 2327383396767197250888469)
                ·
                  refine ⟨109096096723462371135397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2327383396767197250888469 109096096723462371135397)
                  ·
                    rfl

theorem cell23_1912175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 6].length) (baseStart_1912175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912175 prefixEnd_1912175 := by exact prefixLift 1912175
  have htrace : WordTrace (prefixWord ++ tailWord_1912175) baseStart_1912175 baseEnd_1912175 := by
    simpa [prefixWord, tailWord_1912175, baseEnd_1912175] using wordTrace_append hprefix tailTrace_1912175
  have hstable : (prefixWord ++ tailWord_1912175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912175).length < 2 ^ (prefixWord ++ tailWord_1912175).sum := by decide
  have hdescent : baseEnd_1912175 < baseStart_1912175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912206 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1912206 : Nat := 118140960795 + 1912206 * 2 ^ 59
def prefixEnd_1912206 : Nat := 4983230072969 + 3 ^ 40 * 1912206 * 2
def baseEnd_1912206 : Nat := 981880788411450718930931

theorem tailTrace_1912206 : CollatzResearch.WordTrace tailWord_1912206 prefixEnd_1912206 981880788411450718930931 := by
  unfold tailWord_1912206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717985313801464453705559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46495921673607810419762981 8717985313801464453705559)
  ·
    refine ⟨13076977970702196680558339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717985313801464453705559 13076977970702196680558339)
    ·
      refine ⟨19615466956053295020837509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13076977970702196680558339 19615466956053295020837509)
      ·
        refine ⟨3677900054259992816407033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19615466956053295020837509 3677900054259992816407033)
        ·
          refine ⟨2758425040694994612305275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677900054259992816407033 2758425040694994612305275)
          ·
            refine ⟨4137637561042491918457913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758425040694994612305275 4137637561042491918457913)
            ·
              refine ⟨3103228170781868938843435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137637561042491918457913 3103228170781868938843435)
              ·
                refine ⟨4654842256172803408265153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103228170781868938843435 4654842256172803408265153)
                ·
                  refine ⟨3491131692129602556198865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654842256172803408265153 3491131692129602556198865)
                  ·
                    refine ⟨2618348769097201917149149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491131692129602556198865 2618348769097201917149149)
                    ·
                      refine ⟨981880788411450718930931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618348769097201917149149 981880788411450718930931)
                      ·
                        rfl

theorem cell23_1912206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1912206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912206 prefixEnd_1912206 := by exact prefixLift 1912206
  have htrace : WordTrace (prefixWord ++ tailWord_1912206) baseStart_1912206 baseEnd_1912206 := by
    simpa [prefixWord, tailWord_1912206, baseEnd_1912206] using wordTrace_append hprefix tailTrace_1912206
  have hstable : (prefixWord ++ tailWord_1912206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912206).length < 2 ^ (prefixWord ++ tailWord_1912206).sum := by decide
  have hdescent : baseEnd_1912206 < baseStart_1912206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912255 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1912255 : Nat := 118140960795 + 1912255 * 2 ^ 59
def prefixEnd_1912255 : Nat := 4983230072969 + 3 ^ 40 * 1912255 * 2
def baseEnd_1912255 : Nat := 981905948963521027218205

theorem tailTrace_1912255 : CollatzResearch.WordTrace tailWord_1912255 prefixEnd_1912255 981905948963521027218205 := by
  unfold tailWord_1912255
  simp only [CollatzResearch.WordTrace]
  refine ⟨69745669687234196998178219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46497113124822797998785479 69745669687234196998178219)
  ·
    refine ⟨104618504530851295497267329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69745669687234196998178219 104618504530851295497267329)
    ·
      refine ⟨78463878398138471622950497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104618504530851295497267329 78463878398138471622950497)
      ·
        refine ⟨58847908798603853717212873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78463878398138471622950497 58847908798603853717212873)
        ·
          refine ⟨44135931598952890287909655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58847908798603853717212873 44135931598952890287909655)
          ·
            refine ⟨66203897398429335431864483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135931598952890287909655 66203897398429335431864483)
            ·
              refine ⟨99305846097644003147796725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66203897398429335431864483 99305846097644003147796725)
              ·
                refine ⟨9309923071654125295105943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99305846097644003147796725 9309923071654125295105943)
                ·
                  refine ⟨13964884607481187942658915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309923071654125295105943 13964884607481187942658915)
                  ·
                    refine ⟨20947326911221781913988373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13964884607481187942658915 20947326911221781913988373)
                    ·
                      refine ⟨981905948963521027218205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20947326911221781913988373 981905948963521027218205)
                      ·
                        rfl

theorem cell23_1912255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1912255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912255 prefixEnd_1912255 := by exact prefixLift 1912255
  have htrace : WordTrace (prefixWord ++ tailWord_1912255) baseStart_1912255 baseEnd_1912255 := by
    simpa [prefixWord, tailWord_1912255, baseEnd_1912255] using wordTrace_append hprefix tailTrace_1912255
  have hstable : (prefixWord ++ tailWord_1912255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912255).length < 2 ^ (prefixWord ++ tailWord_1912255).sum := by decide
  have hdescent : baseEnd_1912255 < baseStart_1912255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912259 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 5, 2, 2]
def baseStart_1912259 : Nat := 118140960795 + 1912259 * 2 ^ 59
def prefixEnd_1912259 : Nat := 4983230072969 + 3 ^ 40 * 1912259 * 2
def baseEnd_1912259 : Nat := 981908002886139011568187

theorem tailTrace_1912259 : CollatzResearch.WordTrace tailWord_1912259 prefixEnd_1912259 981908002886139011568187 := by
  unfold tailWord_1912259
  simp only [CollatzResearch.WordTrace]
  refine ⟨69745815579219705681323831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46497210386146470454215887 69745815579219705681323831)
  ·
    refine ⟨104618723368829558521985747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69745815579219705681323831 104618723368829558521985747)
    ·
      refine ⟨156928085053244337782978621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104618723368829558521985747 156928085053244337782978621)
      ·
        refine ⟨58848031894966626668616983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156928085053244337782978621 58848031894966626668616983)
        ·
          refine ⟨88272047842449940002925475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58848031894966626668616983 88272047842449940002925475)
          ·
            refine ⟨132408071763674910004388213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88272047842449940002925475 132408071763674910004388213)
            ·
              refine ⟨12413256727844522812911395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132408071763674910004388213 12413256727844522812911395)
              ·
                refine ⟨18619885091766784219367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413256727844522812911395 18619885091766784219367093)
                ·
                  refine ⟨1745614227353136020565665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18619885091766784219367093 1745614227353136020565665)
                  ·
                    refine ⟨1309210670514852015424249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745614227353136020565665 1309210670514852015424249)
                    ·
                      refine ⟨981908002886139011568187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309210670514852015424249 981908002886139011568187)
                      ·
                        rfl

theorem cell23_1912259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_1912259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912259 prefixEnd_1912259 := by exact prefixLift 1912259
  have htrace : WordTrace (prefixWord ++ tailWord_1912259) baseStart_1912259 baseEnd_1912259 := by
    simpa [prefixWord, tailWord_1912259, baseEnd_1912259] using wordTrace_append hprefix tailTrace_1912259
  have hstable : (prefixWord ++ tailWord_1912259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912259).length < 2 ^ (prefixWord ++ tailWord_1912259).sum := by decide
  have hdescent : baseEnd_1912259 < baseStart_1912259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912276 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1912276 : Nat := 118140960795 + 1912276 * 2 ^ 59
def prefixEnd_1912276 : Nat := 4983230072969 + 3 ^ 40 * 1912276 * 2
def baseEnd_1912276 : Nat := 981916732057265445055609

theorem tailTrace_1912276 : CollatzResearch.WordTrace tailWord_1912276 prefixEnd_1912276 981916732057265445055609 := by
  unfold tailWord_1912276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873217810079058792346341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46497623746772078389795121 34873217810079058792346341)
  ·
    refine ⟨6538728339389823523564939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34873217810079058792346341 6538728339389823523564939)
    ·
      refine ⟨9808092509084735285347409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538728339389823523564939 9808092509084735285347409)
      ·
        refine ⟨7356069381813551464010557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9808092509084735285347409 7356069381813551464010557)
        ·
          refine ⟨2758526018180081799003959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7356069381813551464010557 2758526018180081799003959)
          ·
            refine ⟨4137789027270122698505939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758526018180081799003959 4137789027270122698505939)
            ·
              refine ⟨6206683540905184047758909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137789027270122698505939 6206683540905184047758909)
              ·
                refine ⟨2327506327839444017909591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6206683540905184047758909 2327506327839444017909591)
                ·
                  refine ⟨3491259491759166026864387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327506327839444017909591 3491259491759166026864387)
                  ·
                    refine ⟨5236889237638749040296581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3491259491759166026864387 5236889237638749040296581)
                    ·
                      refine ⟨981916732057265445055609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5236889237638749040296581 981916732057265445055609)
                      ·
                        rfl

theorem cell23_1912276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1912276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912276 prefixEnd_1912276 := by exact prefixLift 1912276
  have htrace : WordTrace (prefixWord ++ tailWord_1912276) baseStart_1912276 baseEnd_1912276 := by
    simpa [prefixWord, tailWord_1912276, baseEnd_1912276] using wordTrace_append hprefix tailTrace_1912276
  have hstable : (prefixWord ++ tailWord_1912276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912276).length < 2 ^ (prefixWord ++ tailWord_1912276).sum := by decide
  have hdescent : baseEnd_1912276 < baseStart_1912276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1912292 : Nat := 118140960795 + 1912292 * 2 ^ 59
def prefixEnd_1912292 : Nat := 4983230072969 + 3 ^ 40 * 1912292 * 2
def baseEnd_1912292 : Nat := 981924947747737382455535

theorem tailTrace_1912292 : CollatzResearch.WordTrace tailWord_1912292 prefixEnd_1912292 981924947747737382455535 := by
  unfold tailWord_1912292
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873509594050076158637565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46498012792066768211516753 34873509594050076158637565)
  ·
    refine ⟨13077566097768778559489087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34873509594050076158637565 13077566097768778559489087)
    ·
      refine ⟨19616349146653167839233631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077566097768778559489087 19616349146653167839233631)
      ·
        refine ⟨29424523719979751758850447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616349146653167839233631 29424523719979751758850447)
        ·
          refine ⟨44136785579969627638275671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424523719979751758850447 44136785579969627638275671)
          ·
            refine ⟨66205178369954441457413507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44136785579969627638275671 66205178369954441457413507)
            ·
              refine ⟨99307767554931662186120261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66205178369954441457413507 99307767554931662186120261)
              ·
                refine ⟨18620206416549686659897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99307767554931662186120261 18620206416549686659897549)
                ·
                  refine ⟨6982577406206132497461581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18620206416549686659897549 6982577406206132497461581)
                  ·
                    refine ⟨2618466527327299686548093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6982577406206132497461581 2618466527327299686548093)
                    ·
                      refine ⟨981924947747737382455535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618466527327299686548093 981924947747737382455535)
                      ·
                        rfl

theorem cell23_1912292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1912292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912292 prefixEnd_1912292 := by exact prefixLift 1912292
  have htrace : WordTrace (prefixWord ++ tailWord_1912292) baseStart_1912292 baseEnd_1912292 := by
    simpa [prefixWord, tailWord_1912292, baseEnd_1912292] using wordTrace_append hprefix tailTrace_1912292
  have hstable : (prefixWord ++ tailWord_1912292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912292).length < 2 ^ (prefixWord ++ tailWord_1912292).sum := by decide
  have hdescent : baseEnd_1912292 < baseStart_1912292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912293 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1912293 : Nat := 118140960795 + 1912293 * 2 ^ 59
def prefixEnd_1912293 : Nat := 4983230072969 + 3 ^ 40 * 1912293 * 2
def baseEnd_1912293 : Nat := 981925461228391878543031

theorem tailTrace_1912293 : CollatzResearch.WordTrace tailWord_1912293 prefixEnd_1912293 981925461228391878543031 := by
  unfold tailWord_1912293
  simp only [CollatzResearch.WordTrace]
  refine ⟨69747055661096529488061533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46498037107397686325374355 69747055661096529488061533)
  ·
    refine ⟨26155145872911198558023075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69747055661096529488061533 26155145872911198558023075)
    ·
      refine ⟨39232718809366797837034613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26155145872911198558023075 39232718809366797837034613)
      ·
        refine ⟨3678067388378137297221995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39232718809366797837034613 3678067388378137297221995)
        ·
          refine ⟨5517101082567205945832993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678067388378137297221995 5517101082567205945832993)
          ·
            refine ⟨4137825811925404459374745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517101082567205945832993 4137825811925404459374745)
            ·
              refine ⟨3103369358944053344531059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137825811925404459374745 3103369358944053344531059)
              ·
                refine ⟨4655054038416080016796589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103369358944053344531059 4655054038416080016796589)
                ·
                  refine ⟨1745645264406030006298721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4655054038416080016796589 1745645264406030006298721)
                  ·
                    refine ⟨1309233948304522504724041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745645264406030006298721 1309233948304522504724041)
                    ·
                      refine ⟨981925461228391878543031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309233948304522504724041 981925461228391878543031)
                      ·
                        rfl

theorem cell23_1912293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1912293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912293 prefixEnd_1912293 := by exact prefixLift 1912293
  have htrace : WordTrace (prefixWord ++ tailWord_1912293) baseStart_1912293 baseEnd_1912293 := by
    simpa [prefixWord, tailWord_1912293, baseEnd_1912293] using wordTrace_append hprefix tailTrace_1912293
  have hstable : (prefixWord ++ tailWord_1912293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912293).length < 2 ^ (prefixWord ++ tailWord_1912293).sum := by decide
  have hdescent : baseEnd_1912293 < baseStart_1912293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912306 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1912306 : Nat := 118140960795 + 1912306 * 2 ^ 59
def prefixEnd_1912306 : Nat := 4983230072969 + 3 ^ 40 * 1912306 * 2
def baseEnd_1912306 : Nat := 981932136476900327680471

theorem tailTrace_1912306 : CollatzResearch.WordTrace tailWord_1912306 prefixEnd_1912306 981932136476900327680471 := by
  unfold tailWord_1912306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436882452512358177071193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46498353206699621805523181 17436882452512358177071193)
  ·
    refine ⟨13077661839384268632803395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17436882452512358177071193 13077661839384268632803395)
    ·
      refine ⟨19616492759076402949205093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077661839384268632803395 19616492759076402949205093)
      ·
        refine ⟨3678092392326825552975955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19616492759076402949205093 3678092392326825552975955)
        ·
          refine ⟨5517138588490238329463933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678092392326825552975955 5517138588490238329463933)
          ·
            refine ⟨2068926970683839373548975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5517138588490238329463933 2068926970683839373548975)
            ·
              refine ⟨3103390456025759060323463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068926970683839373548975 3103390456025759060323463)
              ·
                refine ⟨4655085684038638590485195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103390456025759060323463 4655085684038638590485195)
                ·
                  refine ⟨6982628526057957885727793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655085684038638590485195 6982628526057957885727793)
                  ·
                    refine ⟨5236971394543468414295845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6982628526057957885727793 5236971394543468414295845)
                    ·
                      refine ⟨981932136476900327680471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5236971394543468414295845 981932136476900327680471)
                      ·
                        rfl

theorem cell23_1912306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1912306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912306 prefixEnd_1912306 := by exact prefixLift 1912306
  have htrace : WordTrace (prefixWord ++ tailWord_1912306) baseStart_1912306 baseEnd_1912306 := by
    simpa [prefixWord, tailWord_1912306, baseEnd_1912306] using wordTrace_append hprefix tailTrace_1912306
  have hstable : (prefixWord ++ tailWord_1912306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912306).length < 2 ^ (prefixWord ++ tailWord_1912306).sum := by decide
  have hdescent : baseEnd_1912306 < baseStart_1912306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912333 : List Nat := [1, 7, 1, 1, 3, 1, 9]
def baseStart_1912333 : Nat := 118140960795 + 1912333 * 2 ^ 59
def prefixEnd_1912333 : Nat := 4983230072969 + 3 ^ 40 * 1912333 * 2
def baseEnd_1912333 : Nat := 12122790129068786691887

theorem tailTrace_1912333 : CollatzResearch.WordTrace tailWord_1912333 prefixEnd_1912333 12122790129068786691887 := by
  unfold tailWord_1912333
  simp only [CollatzResearch.WordTrace]
  refine ⟨69748514580951616319517653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46499009720634410879678435 69748514580951616319517653)
  ·
    refine ⟨1634730810491053507488695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69748514580951616319517653 1634730810491053507488695)
    ·
      refine ⟨2452096215736580261233043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634730810491053507488695 2452096215736580261233043)
      ·
        refine ⟨3678144323604870391849565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452096215736580261233043 3678144323604870391849565)
        ·
          refine ⟨1379304121351826396943587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3678144323604870391849565 1379304121351826396943587)
          ·
            refine ⟨2068956182027739595415381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379304121351826396943587 2068956182027739595415381)
            ·
              refine ⟨12122790129068786691887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2068956182027739595415381 12122790129068786691887)
              ·
                rfl

theorem cell23_1912333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 9].length) (baseStart_1912333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912333 prefixEnd_1912333 := by exact prefixLift 1912333
  have htrace : WordTrace (prefixWord ++ tailWord_1912333) baseStart_1912333 baseEnd_1912333 := by
    simpa [prefixWord, tailWord_1912333, baseEnd_1912333] using wordTrace_append hprefix tailTrace_1912333
  have hstable : (prefixWord ++ tailWord_1912333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912333).length < 2 ^ (prefixWord ++ tailWord_1912333).sum := by decide
  have hdescent : baseEnd_1912333 < baseStart_1912333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912389 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 5]
def baseStart_1912389 : Nat := 118140960795 + 1912389 * 2 ^ 59
def prefixEnd_1912389 : Nat := 4983230072969 + 3 ^ 40 * 1912389 * 2
def baseEnd_1912389 : Nat := 109108306152358166993621

theorem tailTrace_1912389 : CollatzResearch.WordTrace tailWord_1912389 prefixEnd_1912389 109108306152358166993621 := by
  unfold tailWord_1912389
  simp only [CollatzResearch.WordTrace]
  refine ⟨69750557068748737883556221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46500371379165825255704147 69750557068748737883556221)
  ·
    refine ⟨26156458900780776706333583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69750557068748737883556221 26156458900780776706333583)
    ·
      refine ⟨39234688351171165059500375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26156458900780776706333583 39234688351171165059500375)
      ·
        refine ⟨58852032526756747589250563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39234688351171165059500375 58852032526756747589250563)
        ·
          refine ⟨88278048790135121383875845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58852032526756747589250563 88278048790135121383875845)
          ·
            refine ⟨16552134148150335259476721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88278048790135121383875845 16552134148150335259476721)
            ·
              refine ⟨12414100611112751444607541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16552134148150335259476721 12414100611112751444607541)
              ·
                refine ⟨1163821932291820447931957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12414100611112751444607541 1163821932291820447931957)
                ·
                  refine ⟨109108306152358166993621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1163821932291820447931957 109108306152358166993621)
                  ·
                    rfl

theorem cell23_1912389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_1912389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912389 prefixEnd_1912389 := by exact prefixLift 1912389
  have htrace : WordTrace (prefixWord ++ tailWord_1912389) baseStart_1912389 baseEnd_1912389 := by
    simpa [prefixWord, tailWord_1912389, baseEnd_1912389] using wordTrace_append hprefix tailTrace_1912389
  have hstable : (prefixWord ++ tailWord_1912389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912389).length < 2 ^ (prefixWord ++ tailWord_1912389).sum := by decide
  have hdescent : baseEnd_1912389 < baseStart_1912389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912413 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1912413 : Nat := 118140960795 + 1912413 * 2 ^ 59
def prefixEnd_1912413 : Nat := 4983230072969 + 3 ^ 40 * 1912413 * 2
def baseEnd_1912413 : Nat := 981987078906931409042479

theorem tailTrace_1912413 : CollatzResearch.WordTrace tailWord_1912413 prefixEnd_1912413 981987078906931409042479 := by
  unfold tailWord_1912413
  simp only [CollatzResearch.WordTrace]
  refine ⟨69751432420661789982429893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46500954947107859988286595 69751432420661789982429893)
  ·
    refine ⟨13078393578874085621705605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69751432420661789982429893 13078393578874085621705605)
    ·
      refine ⟨2452198796038891054069801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13078393578874085621705605 2452198796038891054069801)
      ·
        refine ⟨1839149097029168290552351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452198796038891054069801 1839149097029168290552351)
        ·
          refine ⟨2758723645543752435828527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839149097029168290552351 2758723645543752435828527)
          ·
            refine ⟨4138085468315628653742791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758723645543752435828527 4138085468315628653742791)
            ·
              refine ⟨6207128202473442980614187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138085468315628653742791 6207128202473442980614187)
              ·
                refine ⟨9310692303710164470921281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207128202473442980614187 9310692303710164470921281)
                ·
                  refine ⟨6983019227782623353190961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9310692303710164470921281 6983019227782623353190961)
                  ·
                    refine ⟨5237264420836967514893221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6983019227782623353190961 5237264420836967514893221)
                    ·
                      refine ⟨981987078906931409042479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5237264420836967514893221 981987078906931409042479)
                      ·
                        rfl

theorem cell23_1912413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1912413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912413 prefixEnd_1912413 := by exact prefixLift 1912413
  have htrace : WordTrace (prefixWord ++ tailWord_1912413) baseStart_1912413 baseEnd_1912413 := by
    simpa [prefixWord, tailWord_1912413, baseEnd_1912413] using wordTrace_append hprefix tailTrace_1912413
  have hstable : (prefixWord ++ tailWord_1912413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912413).length < 2 ^ (prefixWord ++ tailWord_1912413).sum := by decide
  have hdescent : baseEnd_1912413 < baseStart_1912413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912439 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_1912439 : Nat := 118140960795 + 1912439 * 2 ^ 59
def prefixEnd_1912439 : Nat := 4983230072969 + 3 ^ 40 * 1912439 * 2
def baseEnd_1912439 : Nat := 982000429403948307317359

theorem tailTrace_1912439 : CollatzResearch.WordTrace tailWord_1912439 prefixEnd_1912439 982000429403948307317359 := by
  unfold tailWord_1912439
  simp only [CollatzResearch.WordTrace]
  refine ⟨69752380718567596422876371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46501587145711730948584247 69752380718567596422876371)
  ·
    refine ⟨104628571077851394634314557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69752380718567596422876371 104628571077851394634314557)
    ·
      refine ⟨39235714154194272987867959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104628571077851394634314557 39235714154194272987867959)
      ·
        refine ⟨58853571231291409481801939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39235714154194272987867959 58853571231291409481801939)
        ·
          refine ⟨88280356846937114222702909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58853571231291409481801939 88280356846937114222702909)
          ·
            refine ⟨33105133817601417833513591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88280356846937114222702909 33105133817601417833513591)
            ·
              refine ⟨49657700726402126750270387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33105133817601417833513591 49657700726402126750270387)
              ·
                refine ⟨74486551089603190125405581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49657700726402126750270387 74486551089603190125405581)
                ·
                  refine ⟨27932456658601196297027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74486551089603190125405581 27932456658601196297027093)
                  ·
                    refine ⟨1309333905871931076423145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27932456658601196297027093 1309333905871931076423145)
                    ·
                      refine ⟨982000429403948307317359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309333905871931076423145 982000429403948307317359)
                      ·
                        rfl

theorem cell23_1912439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_1912439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912439 prefixEnd_1912439 := by exact prefixLift 1912439
  have htrace : WordTrace (prefixWord ++ tailWord_1912439) baseStart_1912439 baseEnd_1912439 := by
    simpa [prefixWord, tailWord_1912439, baseEnd_1912439] using wordTrace_append hprefix tailTrace_1912439
  have hstable : (prefixWord ++ tailWord_1912439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912439).length < 2 ^ (prefixWord ++ tailWord_1912439).sum := by decide
  have hdescent : baseEnd_1912439 < baseStart_1912439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912442 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1912442 : Nat := 118140960795 + 1912442 * 2 ^ 59
def prefixEnd_1912442 : Nat := 4983230072969 + 3 ^ 40 * 1912442 * 2
def baseEnd_1912442 : Nat := 982001969845911795579845

theorem tailTrace_1912442 : CollatzResearch.WordTrace tailWord_1912442 prefixEnd_1912442 982001969845911795579845 := by
  unfold tailWord_1912442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438122534389181983808895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46501660091704485290157053 17438122534389181983808895)
  ·
    refine ⟨26157183801583772975713343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438122534389181983808895 26157183801583772975713343)
    ·
      refine ⟨39235775702375659463570015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26157183801583772975713343 39235775702375659463570015)
      ·
        refine ⟨58853663553563489195355023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39235775702375659463570015 58853663553563489195355023)
        ·
          refine ⟨88280495330345233793032535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58853663553563489195355023 88280495330345233793032535)
          ·
            refine ⟨132420742995517850689548803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88280495330345233793032535 132420742995517850689548803)
            ·
              refine ⟨198631114493276776034323205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132420742995517850689548803 198631114493276776034323205)
              ·
                refine ⟨37243333967489395506435601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198631114493276776034323205 37243333967489395506435601)
                ·
                  refine ⟨27932500475617046629826701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37243333967489395506435601 27932500475617046629826701)
                  ·
                    refine ⟨10474687678356392486185013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27932500475617046629826701 10474687678356392486185013)
                    ·
                      refine ⟨982001969845911795579845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10474687678356392486185013 982001969845911795579845)
                      ·
                        rfl

theorem cell23_1912442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1912442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912442 prefixEnd_1912442 := by exact prefixLift 1912442
  have htrace : WordTrace (prefixWord ++ tailWord_1912442) baseStart_1912442 baseEnd_1912442 := by
    simpa [prefixWord, tailWord_1912442, baseEnd_1912442] using wordTrace_append hprefix tailTrace_1912442
  have hstable : (prefixWord ++ tailWord_1912442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912442).length < 2 ^ (prefixWord ++ tailWord_1912442).sum := by decide
  have hdescent : baseEnd_1912442 < baseStart_1912442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912459 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3]
def baseStart_1912459 : Nat := 118140960795 + 1912459 * 2 ^ 59
def prefixEnd_1912459 : Nat := 4983230072969 + 3 ^ 40 * 1912459 * 2
def baseEnd_1912459 : Nat := 982010699017038229067267

theorem tailTrace_1912459 : CollatzResearch.WordTrace tailWord_1912459 prefixEnd_1912459 982010699017038229067267 := by
  unfold tailWord_1912459
  simp only [CollatzResearch.WordTrace]
  refine ⟨69753110178495139838604431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46502073452330093225736287 69753110178495139838604431)
  ·
    refine ⟨104629665267742709757906647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69753110178495139838604431 104629665267742709757906647)
    ·
      refine ⟨156944497901614064636859971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104629665267742709757906647 156944497901614064636859971)
      ·
        refine ⟨235416746852421096955289957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156944497901614064636859971 235416746852421096955289957)
        ·
          refine ⟨44140640034828955679116867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235416746852421096955289957 44140640034828955679116867)
          ·
            refine ⟨66210960052243433518675301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44140640034828955679116867 66210960052243433518675301)
            ·
              refine ⟨12414555009795643784751619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66210960052243433518675301 12414555009795643784751619)
              ·
                refine ⟨18621832514693465677127429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414555009795643784751619 18621832514693465677127429)
                ·
                  refine ⟨3491593596505024814461393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18621832514693465677127429 3491593596505024814461393)
                  ·
                    refine ⟨2618695197378768610846045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491593596505024814461393 2618695197378768610846045)
                    ·
                      refine ⟨982010699017038229067267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618695197378768610846045 982010699017038229067267)
                      ·
                        rfl

theorem cell23_1912459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].length) (baseStart_1912459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912459 prefixEnd_1912459 := by exact prefixLift 1912459
  have htrace : WordTrace (prefixWord ++ tailWord_1912459) baseStart_1912459 baseEnd_1912459 := by
    simpa [prefixWord, tailWord_1912459, baseEnd_1912459] using wordTrace_append hprefix tailTrace_1912459
  have hstable : (prefixWord ++ tailWord_1912459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912459).length < 2 ^ (prefixWord ++ tailWord_1912459).sum := by decide
  have hdescent : baseEnd_1912459 < baseStart_1912459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1912492 : Nat := 118140960795 + 1912492 * 2 ^ 59
def prefixEnd_1912492 : Nat := 4983230072969 + 3 ^ 40 * 1912492 * 2
def baseEnd_1912492 : Nat := 327342547959545533318205

theorem tailTrace_1912492 : CollatzResearch.WordTrace tailWord_1912492 prefixEnd_1912492 327342547959545533318205 := by
  unfold tailWord_1912492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877156893687793237277865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46502875858250390983037153 34877156893687793237277865)
  ·
    refine ⟨26157867670265844927958399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34877156893687793237277865 26157867670265844927958399)
    ·
      refine ⟨39236801505398767391937599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26157867670265844927958399 39236801505398767391937599)
      ·
        refine ⟨58855202258098151087906399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39236801505398767391937599 58855202258098151087906399)
        ·
          refine ⟨88282803387147226631859599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58855202258098151087906399 88282803387147226631859599)
          ·
            refine ⟨132424205080720839947789399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88282803387147226631859599 132424205080720839947789399)
            ·
              refine ⟨198636307621081259921684099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132424205080720839947789399 198636307621081259921684099)
              ·
                refine ⟨297954461431621889882526149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198636307621081259921684099 297954461431621889882526149)
                ·
                  refine ⟨55866461518429104352973653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297954461431621889882526149 55866461518429104352973653)
                  ·
                    refine ⟨327342547959545533318205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55866461518429104352973653 327342547959545533318205)
                    ·
                      rfl

theorem cell23_1912492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1912492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912492 prefixEnd_1912492 := by exact prefixLift 1912492
  have htrace : WordTrace (prefixWord ++ tailWord_1912492) baseStart_1912492 baseEnd_1912492 := by
    simpa [prefixWord, tailWord_1912492, baseEnd_1912492] using wordTrace_append hprefix tailTrace_1912492
  have hstable : (prefixWord ++ tailWord_1912492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912492).length < 2 ^ (prefixWord ++ tailWord_1912492).sum := by decide
  have hdescent : baseEnd_1912492 < baseStart_1912492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 1, 1, 3]
def baseStart_1912523 : Nat := 118140960795 + 1912523 * 2 ^ 59
def prefixEnd_1912523 : Nat := 4983230072969 + 3 ^ 40 * 1912523 * 2
def baseEnd_1912523 : Nat := 982043561778925978666973

theorem tailTrace_1912523 : CollatzResearch.WordTrace tailWord_1912523 prefixEnd_1912523 982043561778925978666973 := by
  unfold tailWord_1912523
  simp only [CollatzResearch.WordTrace]
  refine ⟨69755444450263278768934223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46503629633508852512622815 69755444450263278768934223)
  ·
    refine ⟨104633166675394918153401335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69755444450263278768934223 104633166675394918153401335)
    ·
      refine ⟨156949750013092377230102003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104633166675394918153401335 156949750013092377230102003)
      ·
        refine ⟨235424625019638565845153005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156949750013092377230102003 235424625019638565845153005)
        ·
          refine ⟨88284234382364462191932377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235424625019638565845153005 88284234382364462191932377)
          ·
            refine ⟨66213175786773346643949283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88284234382364462191932377 66213175786773346643949283)
            ·
              refine ⟨99319763680160019965923925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66213175786773346643949283 99319763680160019965923925)
              ·
                refine ⟨1163903480626875233975671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99319763680160019965923925 1163903480626875233975671)
                ·
                  refine ⟨1745855220940312850963507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163903480626875233975671 1745855220940312850963507)
                  ·
                    refine ⟨2618782831410469276445261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1745855220940312850963507 2618782831410469276445261)
                    ·
                      refine ⟨982043561778925978666973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2618782831410469276445261 982043561778925978666973)
                      ·
                        rfl

theorem cell23_1912523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 1, 3].length) (baseStart_1912523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912523 prefixEnd_1912523 := by exact prefixLift 1912523
  have htrace : WordTrace (prefixWord ++ tailWord_1912523) baseStart_1912523 baseEnd_1912523 := by
    simpa [prefixWord, tailWord_1912523, baseEnd_1912523] using wordTrace_append hprefix tailTrace_1912523
  have hstable : (prefixWord ++ tailWord_1912523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912523).length < 2 ^ (prefixWord ++ tailWord_1912523).sum := by decide
  have hdescent : baseEnd_1912523 < baseStart_1912523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912586 : List Nat := [3, 1, 2, 2, 1, 5, 1, 8]
def baseStart_1912586 : Nat := 118140960795 + 1912586 * 2 ^ 59
def prefixEnd_1912586 : Nat := 4983230072969 + 3 ^ 40 * 1912586 * 2
def baseEnd_1912586 : Nat := 36373181891117008599229

theorem tailTrace_1912586 : CollatzResearch.WordTrace tailWord_1912586 prefixEnd_1912586 36373181891117008599229 := by
  unfold tailWord_1912586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439435562258760132119403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46505161499356693685651741 17439435562258760132119403)
  ·
    refine ⟨26159153343388140198179105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17439435562258760132119403 26159153343388140198179105)
    ·
      refine ⟨19619365007541105148634329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26159153343388140198179105 19619365007541105148634329)
      ·
        refine ⟨14714523755655828861475747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619365007541105148634329 14714523755655828861475747)
        ·
          refine ⟨22071785633483743292213621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714523755655828861475747 22071785633483743292213621)
          ·
            refine ⟨2069229903139100933645027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22071785633483743292213621 2069229903139100933645027)
            ·
              refine ⟨3103844854708651400467541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069229903139100933645027 3103844854708651400467541)
              ·
                refine ⟨36373181891117008599229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3103844854708651400467541 36373181891117008599229)
                ·
                  rfl

theorem cell23_1912586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_1912586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912586 prefixEnd_1912586 := by exact prefixLift 1912586
  have htrace : WordTrace (prefixWord ++ tailWord_1912586) baseStart_1912586 baseEnd_1912586 := by
    simpa [prefixWord, tailWord_1912586, baseEnd_1912586] using wordTrace_append hprefix tailTrace_1912586
  have hstable : (prefixWord ++ tailWord_1912586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912586).length < 2 ^ (prefixWord ++ tailWord_1912586).sum := by decide
  have hdescent : baseEnd_1912586 < baseStart_1912586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912623 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 1, 3, 2]
def baseStart_1912623 : Nat := 118140960795 + 1912623 * 2 ^ 59
def prefixEnd_1912623 : Nat := 4983230072969 + 3 ^ 40 * 1912623 * 2
def baseEnd_1912623 : Nat := 982094909844375587416513

theorem tailTrace_1912623 : CollatzResearch.WordTrace tailWord_1912623 prefixEnd_1912623 982094909844375587416513 := by
  unfold tailWord_1912623
  simp only [CollatzResearch.WordTrace]
  refine ⟨69759091749900995847574523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46506061166600663898383015 69759091749900995847574523)
  ·
    refine ⟨104638637624851493771361785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69759091749900995847574523 104638637624851493771361785)
    ·
      refine ⟨78478978218638620328521339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104638637624851493771361785 78478978218638620328521339)
      ·
        refine ⟨117718467327957930492782009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78478978218638620328521339 117718467327957930492782009)
        ·
          refine ⟨88288850495968447869586507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117718467327957930492782009 88288850495968447869586507)
          ·
            refine ⟨132433275743952671804379761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88288850495968447869586507 132433275743952671804379761)
            ·
              refine ⟨99324956807964503853284821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132433275743952671804379761 99324956807964503853284821)
              ·
                refine ⟨2327928675186668059061363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99324956807964503853284821 2327928675186668059061363)
                ·
                  refine ⟨3491893012780002088592045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327928675186668059061363 3491893012780002088592045)
                  ·
                    refine ⟨1309459879792500783222017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491893012780002088592045 1309459879792500783222017)
                    ·
                      refine ⟨982094909844375587416513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309459879792500783222017 982094909844375587416513)
                      ·
                        rfl

theorem cell23_1912623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3, 2].length) (baseStart_1912623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912623 prefixEnd_1912623 := by exact prefixLift 1912623
  have htrace : WordTrace (prefixWord ++ tailWord_1912623) baseStart_1912623 baseEnd_1912623 := by
    simpa [prefixWord, tailWord_1912623, baseEnd_1912623] using wordTrace_append hprefix tailTrace_1912623
  have hstable : (prefixWord ++ tailWord_1912623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912623).length < 2 ^ (prefixWord ++ tailWord_1912623).sum := by decide
  have hdescent : baseEnd_1912623 < baseStart_1912623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912780 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1912780 : Nat := 118140960795 + 1912780 * 2 ^ 59
def prefixEnd_1912780 : Nat := 4983230072969 + 3 ^ 40 * 1912780 * 2
def baseEnd_1912780 : Nat := 982175526307131473153291

theorem tailTrace_1912780 : CollatzResearch.WordTrace tailWord_1912780 prefixEnd_1912780 982175526307131473153291 := by
  unfold tailWord_1912780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34882409005166105830519897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46509878673554807774026529 34882409005166105830519897)
  ·
    refine ⟨26161806753874579372889923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34882409005166105830519897 26161806753874579372889923)
    ·
      refine ⟨39242710130811869059334885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26161806753874579372889923 39242710130811869059334885)
      ·
        refine ⟨7358008149527225448625291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39242710130811869059334885 7358008149527225448625291)
        ·
          refine ⟨11037012224290838172937937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358008149527225448625291 11037012224290838172937937)
          ·
            refine ⟨8277759168218128629703453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037012224290838172937937 8277759168218128629703453)
            ·
              refine ⟨3104159688081798236138795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8277759168218128629703453 3104159688081798236138795)
              ·
                refine ⟨4656239532122697354208193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104159688081798236138795 4656239532122697354208193)
                ·
                  refine ⟨3492179649092023015656145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656239532122697354208193 3492179649092023015656145)
                  ·
                    refine ⟨2619134736819017261742109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492179649092023015656145 2619134736819017261742109)
                    ·
                      refine ⟨982175526307131473153291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619134736819017261742109 982175526307131473153291)
                      ·
                        rfl

theorem cell23_1912780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1912780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912780 prefixEnd_1912780 := by exact prefixLift 1912780
  have htrace : WordTrace (prefixWord ++ tailWord_1912780) baseStart_1912780 baseEnd_1912780 := by
    simpa [prefixWord, tailWord_1912780, baseEnd_1912780] using wordTrace_append hprefix tailTrace_1912780
  have hstable : (prefixWord ++ tailWord_1912780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912780).length < 2 ^ (prefixWord ++ tailWord_1912780).sum := by decide
  have hdescent : baseEnd_1912780 < baseStart_1912780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912843 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 6, 4]
def baseStart_1912843 : Nat := 118140960795 + 1912843 * 2 ^ 59
def prefixEnd_1912843 : Nat := 4983230072969 + 3 ^ 40 * 1912843 * 2
def baseEnd_1912843 : Nat := 327402625196121575555167

theorem tailTrace_1912843 : CollatzResearch.WordTrace tailWord_1912843 prefixEnd_1912843 327402625196121575555167 := by
  unfold tailWord_1912843
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767115809103973420583183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46511410539402648947055455 69767115809103973420583183)
  ·
    refine ⟨104650673713655960130874775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69767115809103973420583183 104650673713655960130874775)
    ·
      refine ⟨156976010570483940196312163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104650673713655960130874775 156976010570483940196312163)
      ·
        refine ⟨235464015855725910294468245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156976010570483940196312163 235464015855725910294468245)
        ·
          refine ⟨11037375743237152045053199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235464015855725910294468245 11037375743237152045053199)
          ·
            refine ⟨16556063614855728067579799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037375743237152045053199 16556063614855728067579799)
            ·
              refine ⟨24834095422283592101369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16556063614855728067579799 24834095422283592101369699)
              ·
                refine ⟨37251143133425388152054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24834095422283592101369699 37251143133425388152054549)
                ·
                  refine ⟨1746147334379315069627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37251143133425388152054549 1746147334379315069627557)
                  ·
                    refine ⟨327402625196121575555167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746147334379315069627557 327402625196121575555167)
                    ·
                      rfl

theorem cell23_1912843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 4].length) (baseStart_1912843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912843 prefixEnd_1912843 := by exact prefixLift 1912843
  have htrace : WordTrace (prefixWord ++ tailWord_1912843) baseStart_1912843 baseEnd_1912843 := by
    simpa [prefixWord, tailWord_1912843, baseEnd_1912843] using wordTrace_append hprefix tailTrace_1912843
  have hstable : (prefixWord ++ tailWord_1912843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912843).length < 2 ^ (prefixWord ++ tailWord_1912843).sum := by decide
  have hdescent : baseEnd_1912843 < baseStart_1912843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912860 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1912860 : Nat := 118140960795 + 1912860 * 2 ^ 59
def prefixEnd_1912860 : Nat := 4983230072969 + 3 ^ 40 * 1912860 * 2
def baseEnd_1912860 : Nat := 327405534919830386717641

theorem tailTrace_1912860 : CollatzResearch.WordTrace tailWord_1912860 prefixEnd_1912860 327405534919830386717641 := by
  unfold tailWord_1912860
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883867925021192661976017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46511823900028256882634689 34883867925021192661976017)
  ·
    refine ⟨26162900943765894496482013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34883867925021192661976017 26162900943765894496482013)
    ·
      refine ⟨9811087853912210436180755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26162900943765894496482013 9811087853912210436180755)
      ·
        refine ⟨14716631780868315654271133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811087853912210436180755 14716631780868315654271133)
        ·
          refine ⟨5518736917825618370351675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14716631780868315654271133 5518736917825618370351675)
          ·
            refine ⟨8278105376738427555527513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518736917825618370351675 8278105376738427555527513)
            ·
              refine ⟨6208579032553820666645635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278105376738427555527513 6208579032553820666645635)
              ·
                refine ⟨9312868548830730999968453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208579032553820666645635 9312868548830730999968453)
                ·
                  refine ⟨1746162852905762062494085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9312868548830730999968453 1746162852905762062494085)
                  ·
                    refine ⟨327405534919830386717641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746162852905762062494085 327405534919830386717641)
                    ·
                      rfl

theorem cell23_1912860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1912860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912860 prefixEnd_1912860 := by exact prefixLift 1912860
  have htrace : WordTrace (prefixWord ++ tailWord_1912860) baseStart_1912860 baseEnd_1912860 := by
    simpa [prefixWord, tailWord_1912860, baseEnd_1912860] using wordTrace_append hprefix tailTrace_1912860
  have hstable : (prefixWord ++ tailWord_1912860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912860).length < 2 ^ (prefixWord ++ tailWord_1912860).sum := by decide
  have hdescent : baseEnd_1912860 < baseStart_1912860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912861 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_1912861 : Nat := 118140960795 + 1912861 * 2 ^ 59
def prefixEnd_1912861 : Nat := 4983230072969 + 3 ^ 40 * 1912861 * 2
def baseEnd_1912861 : Nat := 982217118240145656240419

theorem tailTrace_1912861 : CollatzResearch.WordTrace tailWord_1912861 prefixEnd_1912861 982217118240145656240419 := by
  unfold tailWord_1912861
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767772323038762494738437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46511848215359174996492291 69767772323038762494738437)
  ·
    refine ⟨13081457310569767967763457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69767772323038762494738437 13081457310569767967763457)
    ·
      refine ⟨9811092982927325975822593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081457310569767967763457 9811092982927325975822593)
      ·
        refine ⟨7358319737195494481866945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811092982927325975822593 7358319737195494481866945)
        ·
          refine ⟨5518739802896620861400209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7358319737195494481866945 5518739802896620861400209)
          ·
            refine ⟨4139054852172465646050157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5518739802896620861400209 4139054852172465646050157)
            ·
              refine ⟨1552145569564674617268809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4139054852172465646050157 1552145569564674617268809)
              ·
                refine ⟨1164109177173505962951607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552145569564674617268809 1164109177173505962951607)
                ·
                  refine ⟨1746163765760258944427411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164109177173505962951607 1746163765760258944427411)
                  ·
                    refine ⟨2619245648640388416641117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746163765760258944427411 2619245648640388416641117)
                    ·
                      refine ⟨982217118240145656240419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619245648640388416641117 982217118240145656240419)
                      ·
                        rfl

theorem cell23_1912861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_1912861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912861 prefixEnd_1912861 := by exact prefixLift 1912861
  have htrace : WordTrace (prefixWord ++ tailWord_1912861) baseStart_1912861 baseEnd_1912861 := by
    simpa [prefixWord, tailWord_1912861, baseEnd_1912861] using wordTrace_append hprefix tailTrace_1912861
  have hstable : (prefixWord ++ tailWord_1912861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912861).length < 2 ^ (prefixWord ++ tailWord_1912861).sum := by decide
  have hdescent : baseEnd_1912861 < baseStart_1912861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912917 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1912917 : Nat := 118140960795 + 1912917 * 2 ^ 59
def prefixEnd_1912917 : Nat := 4983230072969 + 3 ^ 40 * 1912917 * 2
def baseEnd_1912917 : Nat := 982245873156797437140161

theorem tailTrace_1912917 : CollatzResearch.WordTrace tailWord_1912917 prefixEnd_1912917 982245873156797437140161 := by
  unfold tailWord_1912917
  simp only [CollatzResearch.WordTrace]
  refine ⟨69769814810835884058777005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46513209873890589372518003 69769814810835884058777005)
  ·
    refine ⟨26163680554063456522041377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69769814810835884058777005 26163680554063456522041377)
    ·
      refine ⟨19622760415547592391531033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26163680554063456522041377 19622760415547592391531033)
      ·
        refine ⟨14717070311660694293648275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19622760415547592391531033 14717070311660694293648275)
        ·
          refine ⟨22075605467491041440472413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717070311660694293648275 22075605467491041440472413)
          ·
            refine ⟨8278352050309140540177155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22075605467491041440472413 8278352050309140540177155)
            ·
              refine ⟨12417528075463710810265733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278352050309140540177155 12417528075463710810265733)
              ·
                refine ⟨2328286514149445776924825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12417528075463710810265733 2328286514149445776924825)
                ·
                  refine ⟨1746214885612084332693619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328286514149445776924825 1746214885612084332693619)
                  ·
                    refine ⟨2619322328418126499040429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746214885612084332693619 2619322328418126499040429)
                    ·
                      refine ⟨982245873156797437140161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619322328418126499040429 982245873156797437140161)
                      ·
                        rfl

theorem cell23_1912917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1912917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912917 prefixEnd_1912917 := by exact prefixLift 1912917
  have htrace : WordTrace (prefixWord ++ tailWord_1912917) baseStart_1912917 baseEnd_1912917 := by
    simpa [prefixWord, tailWord_1912917, baseEnd_1912917] using wordTrace_append hprefix tailTrace_1912917
  have hstable : (prefixWord ++ tailWord_1912917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912917).length < 2 ^ (prefixWord ++ tailWord_1912917).sum := by decide
  have hdescent : baseEnd_1912917 < baseStart_1912917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912933 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1912933 : Nat := 118140960795 + 1912933 * 2 ^ 59
def prefixEnd_1912933 : Nat := 4983230072969 + 3 ^ 40 * 1912933 * 2
def baseEnd_1912933 : Nat := 327418029615756458180029

theorem tailTrace_1912933 : CollatzResearch.WordTrace tailWord_1912933 prefixEnd_1912933 327418029615756458180029 := by
  unfold tailWord_1912933
  simp only [CollatzResearch.WordTrace]
  refine ⟨69770398378777918791359453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46513598919185279194239635 69770398378777918791359453)
  ·
    refine ⟨26163899392041719546759795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69770398378777918791359453 26163899392041719546759795)
    ·
      refine ⟨39245849088062579320139693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26163899392041719546759795 39245849088062579320139693)
      ·
        refine ⟨14717193408023467245052385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39245849088062579320139693 14717193408023467245052385)
        ·
          refine ⟨11037895056017600433789289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14717193408023467245052385 11037895056017600433789289)
          ·
            refine ⟨8278421292013200325341967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037895056017600433789289 8278421292013200325341967)
            ·
              refine ⟨12417631938019800488012951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278421292013200325341967 12417631938019800488012951)
              ·
                refine ⟨18626447907029700732019427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12417631938019800488012951 18626447907029700732019427)
                ·
                  refine ⟨27939671860544551098029141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18626447907029700732019427 27939671860544551098029141)
                  ·
                    refine ⟨327418029615756458180029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27939671860544551098029141 327418029615756458180029)
                    ·
                      rfl

theorem cell23_1912933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1912933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912933 prefixEnd_1912933 := by exact prefixLift 1912933
  have htrace : WordTrace (prefixWord ++ tailWord_1912933) baseStart_1912933 baseEnd_1912933 := by
    simpa [prefixWord, tailWord_1912933, baseEnd_1912933] using wordTrace_append hprefix tailTrace_1912933
  have hstable : (prefixWord ++ tailWord_1912933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912933).length < 2 ^ (prefixWord ++ tailWord_1912933).sum := by decide
  have hdescent : baseEnd_1912933 < baseStart_1912933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912957 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_1912957 : Nat := 118140960795 + 1912957 * 2 ^ 59
def prefixEnd_1912957 : Nat := 4983230072969 + 3 ^ 40 * 1912957 * 2
def baseEnd_1912957 : Nat := 982266412382977280639977

theorem tailTrace_1912957 : CollatzResearch.WordTrace tailWord_1912957 prefixEnd_1912957 982266412382977280639977 := by
  unfold tailWord_1912957
  simp only [CollatzResearch.WordTrace]
  refine ⟨69771273730690970890233125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46514182487127313926822083 69771273730690970890233125)
  ·
    refine ⟨13082113824504557041918711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69771273730690970890233125 13082113824504557041918711)
    ·
      refine ⟨19623170736756835562878067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13082113824504557041918711 19623170736756835562878067)
      ·
        refine ⟨29434756105135253344317101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623170736756835562878067 29434756105135253344317101)
        ·
          refine ⟨11038033539425720004118913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29434756105135253344317101 11038033539425720004118913)
          ·
            refine ⟨8278525154569290003089185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11038033539425720004118913 8278525154569290003089185)
            ·
              refine ⟨6208893865926967502316889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278525154569290003089185 6208893865926967502316889)
              ·
                refine ⟨4656670399445225626737667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208893865926967502316889 4656670399445225626737667)
                ·
                  refine ⟨6985005599167838440106501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656670399445225626737667 6985005599167838440106501)
                  ·
                    refine ⟨1309688549843969707519969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985005599167838440106501 1309688549843969707519969)
                    ·
                      refine ⟨982266412382977280639977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309688549843969707519969 982266412382977280639977)
                      ·
                        rfl

theorem cell23_1912957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_1912957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912957 prefixEnd_1912957 := by exact prefixLift 1912957
  have htrace : WordTrace (prefixWord ++ tailWord_1912957) baseStart_1912957 baseEnd_1912957 := by
    simpa [prefixWord, tailWord_1912957, baseEnd_1912957] using wordTrace_append hprefix tailTrace_1912957
  have hstable : (prefixWord ++ tailWord_1912957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912957).length < 2 ^ (prefixWord ++ tailWord_1912957).sum := by decide
  have hdescent : baseEnd_1912957 < baseStart_1912957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912970 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1912970 : Nat := 118140960795 + 1912970 * 2 ^ 59
def prefixEnd_1912970 : Nat := 4983230072969 + 3 ^ 40 * 1912970 * 2
def baseEnd_1912970 : Nat := 982273087631485729777417

theorem tailTrace_1912970 : CollatzResearch.WordTrace tailWord_1912970 prefixEnd_1912970 982273087631485729777417 := by
  unfold tailWord_1912970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442936969910968527614091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46514498586429249406970909 17442936969910968527614091)
  ·
    refine ⟨26164405454866452791421137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442936969910968527614091 26164405454866452791421137)
    ·
      refine ⟨19623304091149839593565853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26164405454866452791421137 19623304091149839593565853)
      ·
        refine ⟨7358739034181189847587195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19623304091149839593565853 7358739034181189847587195)
        ·
          refine ⟨11038108551271784771380793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358739034181189847587195 11038108551271784771380793)
          ·
            refine ⟨8278581413453838578535595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11038108551271784771380793 8278581413453838578535595)
            ·
              refine ⟨12417872120180757867803393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278581413453838578535595 12417872120180757867803393)
              ·
                refine ⟨9313404090135568400852545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417872120180757867803393 9313404090135568400852545)
                ·
                  refine ⟨6985053067601676300639409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9313404090135568400852545 6985053067601676300639409)
                  ·
                    refine ⟨5238789800701257225479557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985053067601676300639409 5238789800701257225479557)
                    ·
                      refine ⟨982273087631485729777417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5238789800701257225479557 982273087631485729777417)
                      ·
                        rfl

theorem cell23_1912970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1912970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1912970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1912970 prefixEnd_1912970 := by exact prefixLift 1912970
  have htrace : WordTrace (prefixWord ++ tailWord_1912970) baseStart_1912970 baseEnd_1912970 := by
    simpa [prefixWord, tailWord_1912970, baseEnd_1912970] using wordTrace_append hprefix tailTrace_1912970
  have hstable : (prefixWord ++ tailWord_1912970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912970).length < 2 ^ (prefixWord ++ tailWord_1912970).sum := by decide
  have hdescent : baseEnd_1912970 < baseStart_1912970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913010 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1913010 : Nat := 118140960795 + 1913010 * 2 ^ 59
def prefixEnd_1913010 : Nat := 4983230072969 + 3 ^ 40 * 1913010 * 2
def baseEnd_1913010 : Nat := 327431208952555191092411

theorem tailTrace_1913010 : CollatzResearch.WordTrace tailWord_1913010 prefixEnd_1913010 327431208952555191092411 := by
  unfold tailWord_1913010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443301699874740235478121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46515471199665973961274989 17443301699874740235478121)
  ·
    refine ⟨13082476274906055176608591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17443301699874740235478121 13082476274906055176608591)
    ·
      refine ⟨19623714412359082764912887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13082476274906055176608591 19623714412359082764912887)
      ·
        refine ⟨29435571618538624147369331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623714412359082764912887 29435571618538624147369331)
        ·
          refine ⟨44153357427807936221053997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435571618538624147369331 44153357427807936221053997)
          ·
            refine ⟨16557509035427976082895249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44153357427807936221053997 16557509035427976082895249)
            ·
              refine ⟨12418131776570982062171437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16557509035427976082895249 12418131776570982062171437)
              ·
                refine ⟨4656799416214118273314289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12418131776570982062171437 4656799416214118273314289)
                ·
                  refine ⟨3492599562160588704985717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656799416214118273314289 3492599562160588704985717)
                  ·
                    refine ⟨327431208952555191092411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3492599562160588704985717 327431208952555191092411)
                    ·
                      rfl

theorem cell23_1913010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1913010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913010 prefixEnd_1913010 := by exact prefixLift 1913010
  have htrace : WordTrace (prefixWord ++ tailWord_1913010) baseStart_1913010 baseEnd_1913010 := by
    simpa [prefixWord, tailWord_1913010, baseEnd_1913010] using wordTrace_append hprefix tailTrace_1913010
  have hstable : (prefixWord ++ tailWord_1913010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913010).length < 2 ^ (prefixWord ++ tailWord_1913010).sum := by decide
  have hdescent : baseEnd_1913010 < baseStart_1913010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913033 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1913033 : Nat := 118140960795 + 1913033 * 2 ^ 59
def prefixEnd_1913033 : Nat := 4983230072969 + 3 ^ 40 * 1913033 * 2
def baseEnd_1913033 : Nat := 982305436912718983289627

theorem tailTrace_1913033 : CollatzResearch.WordTrace tailWord_1913033 prefixEnd_1913033 982305436912718983289627 := by
  unfold tailWord_1913033
  simp only [CollatzResearch.WordTrace]
  refine ⟨69774045678415635869999753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516030452277090579999835 69774045678415635869999753)
  ·
    refine ⟨52330534258811726902499815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69774045678415635869999753 52330534258811726902499815)
    ·
      refine ⟨78495801388217590353749723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52330534258811726902499815 78495801388217590353749723)
      ·
        refine ⟨117743702082326385530624585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78495801388217590353749723 117743702082326385530624585)
        ·
          refine ⟨88307776561744789147968439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117743702082326385530624585 88307776561744789147968439)
          ·
            refine ⟨132461664842617183721952659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88307776561744789147968439 132461664842617183721952659)
            ·
              refine ⟨198692497263925775582928989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132461664842617183721952659 198692497263925775582928989)
              ·
                refine ⟨74509686473972165843598371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198692497263925775582928989 74509686473972165843598371)
                ·
                  refine ⟨111764529710958248765397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74509686473972165843598371 111764529710958248765397557)
                  ·
                    refine ⟨10477924660402335821756021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111764529710958248765397557 10477924660402335821756021)
                    ·
                      refine ⟨982305436912718983289627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10477924660402335821756021 982305436912718983289627)
                      ·
                        rfl

theorem cell23_1913033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1913033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913033 prefixEnd_1913033 := by exact prefixLift 1913033
  have htrace : WordTrace (prefixWord ++ tailWord_1913033) baseStart_1913033 baseEnd_1913033 := by
    simpa [prefixWord, tailWord_1913033, baseEnd_1913033] using wordTrace_append hprefix tailTrace_1913033
  have hstable : (prefixWord ++ tailWord_1913033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913033).length < 2 ^ (prefixWord ++ tailWord_1913033).sum := by decide
  have hdescent : baseEnd_1913033 < baseStart_1913033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913050 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1913050 : Nat := 118140960795 + 1913050 * 2 ^ 59
def prefixEnd_1913050 : Nat := 4983230072969 + 3 ^ 40 * 1913050 * 2
def baseEnd_1913050 : Nat := 982314166083845416777049

theorem tailTrace_1913050 : CollatzResearch.WordTrace tailWord_1913050 prefixEnd_1913050 982314166083845416777049 := by
  unfold tailWord_1913050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443666429838511943342151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46516443812902698515579069 17443666429838511943342151)
  ·
    refine ⟨26165499644757767915013227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443666429838511943342151 26165499644757767915013227)
    ·
      refine ⟨39248249467136651872519841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165499644757767915013227 39248249467136651872519841)
      ·
        refine ⟨29436187100352488904389881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39248249467136651872519841 29436187100352488904389881)
        ·
          refine ⟨22077140325264366678292411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29436187100352488904389881 22077140325264366678292411)
          ·
            refine ⟨33115710487896550017438617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22077140325264366678292411 33115710487896550017438617)
            ·
              refine ⟨24836782865922412513078963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33115710487896550017438617 24836782865922412513078963)
              ·
                refine ⟨37255174298883618769618445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836782865922412513078963 37255174298883618769618445)
                ·
                  refine ⟨13970690362081357038606917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37255174298883618769618445 13970690362081357038606917)
                  ·
                    refine ⟨2619504442890254444738797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13970690362081357038606917 2619504442890254444738797)
                    ·
                      refine ⟨982314166083845416777049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619504442890254444738797 982314166083845416777049)
                      ·
                        rfl

theorem cell23_1913050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1913050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913050 prefixEnd_1913050 := by exact prefixLift 1913050
  have htrace : WordTrace (prefixWord ++ tailWord_1913050) baseStart_1913050 baseEnd_1913050 := by
    simpa [prefixWord, tailWord_1913050, baseEnd_1913050] using wordTrace_append hprefix tailTrace_1913050
  have hstable : (prefixWord ++ tailWord_1913050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913050).length < 2 ^ (prefixWord ++ tailWord_1913050).sum := by decide
  have hdescent : baseEnd_1913050 < baseStart_1913050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913067 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3]
def baseStart_1913067 : Nat := 118140960795 + 1913067 * 2 ^ 59
def prefixEnd_1913067 : Nat := 4983230072969 + 3 ^ 40 * 1913067 * 2
def baseEnd_1913067 : Nat := 982322895254971850264471

theorem tailTrace_1913067 : CollatzResearch.WordTrace tailWord_1913067 prefixEnd_1913067 982322895254971850264471 := by
  unfold tailWord_1913067
  simp only [CollatzResearch.WordTrace]
  refine ⟨69775285760292459676737455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516857173528306451158303 69775285760292459676737455)
  ·
    refine ⟨104662928640438689515106183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69775285760292459676737455 104662928640438689515106183)
    ·
      refine ⟨156994392960658034272659275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104662928640438689515106183 156994392960658034272659275)
      ·
        refine ⟨235491589440987051408988913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156994392960658034272659275 235491589440987051408988913)
        ·
          refine ⟨176618692080740288556741685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235491589440987051408988913 176618692080740288556741685)
          ·
            refine ⟨16558002382569402052194533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176618692080740288556741685 16558002382569402052194533)
            ·
              refine ⟨3104625446731762884786475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16558002382569402052194533 3104625446731762884786475)
              ·
                refine ⟨4656938170097644327179713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104625446731762884786475 4656938170097644327179713)
                ·
                  refine ⟨3492703627573233245384785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656938170097644327179713 3492703627573233245384785)
                  ·
                    refine ⟨2619527720679924934038589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492703627573233245384785 2619527720679924934038589)
                    ·
                      refine ⟨982322895254971850264471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619527720679924934038589 982322895254971850264471)
                      ·
                        rfl

theorem cell23_1913067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].length) (baseStart_1913067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913067 prefixEnd_1913067 := by exact prefixLift 1913067
  have htrace : WordTrace (prefixWord ++ tailWord_1913067) baseStart_1913067 baseEnd_1913067 := by
    simpa [prefixWord, tailWord_1913067, baseEnd_1913067] using wordTrace_append hprefix tailTrace_1913067
  have hstable : (prefixWord ++ tailWord_1913067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913067).length < 2 ^ (prefixWord ++ tailWord_1913067).sum := by decide
  have hdescent : baseEnd_1913067 < baseStart_1913067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913100 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1913100 : Nat := 118140960795 + 1913100 * 2 ^ 59
def prefixEnd_1913100 : Nat := 4983230072969 + 3 ^ 40 * 1913100 * 2
def baseEnd_1913100 : Nat := 327446613372190073717273

theorem tailTrace_1913100 : CollatzResearch.WordTrace tailWord_1913100 prefixEnd_1913100 327446613372190073717273 := by
  unfold tailWord_1913100
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888244684586453156344377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46517659579448604208459169 34888244684586453156344377)
  ·
    refine ⟨26166183513439839867258283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34888244684586453156344377 26166183513439839867258283)
    ·
      refine ⟨39249275270159759800887425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26166183513439839867258283 39249275270159759800887425)
      ·
        refine ⟨29436956452619819850665569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39249275270159759800887425 29436956452619819850665569)
        ·
          refine ⟨22077717339464864887999177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29436956452619819850665569 22077717339464864887999177)
          ·
            refine ⟨16558288004598648665999383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22077717339464864887999177 16558288004598648665999383)
            ·
              refine ⟨24837432006897972998999075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558288004598648665999383 24837432006897972998999075)
              ·
                refine ⟨37256148010346959498498613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24837432006897972998999075 37256148010346959498498613)
                ·
                  refine ⟨3492763875970027452984245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37256148010346959498498613 3492763875970027452984245)
                  ·
                    refine ⟨327446613372190073717273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3492763875970027452984245 327446613372190073717273)
                    ·
                      rfl

theorem cell23_1913100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1913100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913100 prefixEnd_1913100 := by exact prefixLift 1913100
  have htrace : WordTrace (prefixWord ++ tailWord_1913100) baseStart_1913100 baseEnd_1913100 := by
    simpa [prefixWord, tailWord_1913100, baseEnd_1913100] using wordTrace_append hprefix tailTrace_1913100
  have hstable : (prefixWord ++ tailWord_1913100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913100).length < 2 ^ (prefixWord ++ tailWord_1913100).sum := by decide
  have hdescent : baseEnd_1913100 < baseStart_1913100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 4, 3, 2]
def baseStart_1913107 : Nat := 118140960795 + 1913107 * 2 ^ 59
def prefixEnd_1913107 : Nat := 4983230072969 + 3 ^ 40 * 1913107 * 2
def baseEnd_1913107 : Nat := 982343434481151693764287

theorem tailTrace_1913107 : CollatzResearch.WordTrace tailWord_1913107 prefixEnd_1913107 982343434481151693764287 := by
  unfold tailWord_1913107
  simp only [CollatzResearch.WordTrace]
  refine ⟨69776744680147546508193575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46517829786765031005462383 69776744680147546508193575)
  ·
    refine ⟨104665117020221319762290363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69776744680147546508193575 104665117020221319762290363)
    ·
      refine ⟨156997675530331979643435545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104665117020221319762290363 156997675530331979643435545)
      ·
        refine ⟨117748256647748984732576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156997675530331979643435545 117748256647748984732576659)
        ·
          refine ⟨176622384971623477098864989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117748256647748984732576659 176622384971623477098864989)
          ·
            refine ⟨66233394364358803912074371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176622384971623477098864989 66233394364358803912074371)
            ·
              refine ⟨99350091546538205868111557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66233394364358803912074371 99350091546538205868111557)
              ·
                refine ⟨18628142164975913600270917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99350091546538205868111557 18628142164975913600270917)
                ·
                  refine ⟨3492776655932983800050797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18628142164975913600270917 3492776655932983800050797)
                  ·
                    refine ⟨1309791245974868925019049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492776655932983800050797 1309791245974868925019049)
                    ·
                      refine ⟨982343434481151693764287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309791245974868925019049 982343434481151693764287)
                      ·
                        rfl

theorem cell23_1913107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3, 2].length) (baseStart_1913107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913107 prefixEnd_1913107 := by exact prefixLift 1913107
  have htrace : WordTrace (prefixWord ++ tailWord_1913107) baseStart_1913107 baseEnd_1913107 := by
    simpa [prefixWord, tailWord_1913107, baseEnd_1913107] using wordTrace_append hprefix tailTrace_1913107
  have hstable : (prefixWord ++ tailWord_1913107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913107).length < 2 ^ (prefixWord ++ tailWord_1913107).sum := by decide
  have hdescent : baseEnd_1913107 < baseStart_1913107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913118 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1913118 : Nat := 118140960795 + 1913118 * 2 ^ 59
def prefixEnd_1913118 : Nat := 4983230072969 + 3 ^ 40 * 1913118 * 2
def baseEnd_1913118 : Nat := 982349082768351150726737

theorem tailTrace_1913118 : CollatzResearch.WordTrace tailWord_1913118 prefixEnd_1913118 982349082768351150726737 := by
  unfold tailWord_1913118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722143235388461923355501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46518097255405130257896005 8722143235388461923355501)
  ·
    refine ⟨3270803713270673221258313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8722143235388461923355501 3270803713270673221258313)
    ·
      refine ⟨2453102784953004915943735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270803713270673221258313 2453102784953004915943735)
      ·
        refine ⟨3679654177429507373915603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453102784953004915943735 3679654177429507373915603)
        ·
          refine ⟨5519481266144261060873405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679654177429507373915603 5519481266144261060873405)
          ·
            refine ⟨2069805474804097897827527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5519481266144261060873405 2069805474804097897827527)
            ·
              refine ⟨3104708212206146846741291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069805474804097897827527 3104708212206146846741291)
              ·
                refine ⟨4657062318309220270111937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104708212206146846741291 4657062318309220270111937)
                ·
                  refine ⟨3492796738731915202583953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657062318309220270111937 3492796738731915202583953)
                  ·
                    refine ⟨2619597554048936401937965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492796738731915202583953 2619597554048936401937965)
                    ·
                      refine ⟨982349082768351150726737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619597554048936401937965 982349082768351150726737)
                      ·
                        rfl

theorem cell23_1913118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1913118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913118 prefixEnd_1913118 := by exact prefixLift 1913118
  have htrace : WordTrace (prefixWord ++ tailWord_1913118) baseStart_1913118 baseEnd_1913118 := by
    simpa [prefixWord, tailWord_1913118, baseEnd_1913118] using wordTrace_append hprefix tailTrace_1913118
  have hstable : (prefixWord ++ tailWord_1913118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913118).length < 2 ^ (prefixWord ++ tailWord_1913118).sum := by decide
  have hdescent : baseEnd_1913118 < baseStart_1913118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913124 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_1913124 : Nat := 118140960795 + 1913124 * 2 ^ 59
def prefixEnd_1913124 : Nat := 4983230072969 + 3 ^ 40 * 1913124 * 2
def baseEnd_1913124 : Nat := 982352163652278127251709

theorem tailTrace_1913124 : CollatzResearch.WordTrace tailWord_1913124 prefixEnd_1913124 982352163652278127251709 := by
  unfold tailWord_1913124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888682360542979205781213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46518243147390638941041617 34888682360542979205781213)
  ·
    refine ⟨13083255885203617202167955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34888682360542979205781213 13083255885203617202167955)
    ·
      refine ⟨19624883827805425803251933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13083255885203617202167955 19624883827805425803251933)
      ·
        refine ⟨7359331435427034676219475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19624883827805425803251933 7359331435427034676219475)
        ·
          refine ⟨11038997153140552014329213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359331435427034676219475 11038997153140552014329213)
          ·
            refine ⟨4139623932427707005373455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11038997153140552014329213 4139623932427707005373455)
            ·
              refine ⟨6209435898641560508060183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139623932427707005373455 6209435898641560508060183)
              ·
                refine ⟨9314153847962340762090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209435898641560508060183 9314153847962340762090275)
                ·
                  refine ⟨13971230771943511143135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314153847962340762090275 13971230771943511143135413)
                  ·
                    refine ⟨1309802884869704169668945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13971230771943511143135413 1309802884869704169668945)
                    ·
                      refine ⟨982352163652278127251709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309802884869704169668945 982352163652278127251709)
                      ·
                        rfl

theorem cell23_1913124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_1913124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913124 prefixEnd_1913124 := by exact prefixLift 1913124
  have htrace : WordTrace (prefixWord ++ tailWord_1913124) baseStart_1913124 baseEnd_1913124 := by
    simpa [prefixWord, tailWord_1913124, baseEnd_1913124] using wordTrace_append hprefix tailTrace_1913124
  have hstable : (prefixWord ++ tailWord_1913124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913124).length < 2 ^ (prefixWord ++ tailWord_1913124).sum := by decide
  have hdescent : baseEnd_1913124 < baseStart_1913124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913187 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1913187 : Nat := 118140960795 + 1913187 * 2 ^ 59
def prefixEnd_1913187 : Nat := 4983230072969 + 3 ^ 40 * 1913187 * 2
def baseEnd_1913187 : Nat := 982384512933511380763919

theorem tailTrace_1913187 : CollatzResearch.WordTrace tailWord_1913187 prefixEnd_1913187 982384512933511380763919 := by
  unfold tailWord_1913187
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779662519857720171105815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46519775013238480114070543 69779662519857720171105815)
  ·
    refine ⟨104669493779786580256658723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69779662519857720171105815 104669493779786580256658723)
    ·
      refine ⟨157004240669679870384988085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104669493779786580256658723 157004240669679870384988085)
      ·
        refine ⟨14719147562782487848592633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157004240669679870384988085 14719147562782487848592633)
        ·
          refine ⟨11039360672086865886444475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14719147562782487848592633 11039360672086865886444475)
          ·
            refine ⟨16559041008130298829666713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039360672086865886444475 16559041008130298829666713)
            ·
              refine ⟨12419280756097724122250035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16559041008130298829666713 12419280756097724122250035)
              ·
                refine ⟨18628921134146586183375053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12419280756097724122250035 18628921134146586183375053)
                ·
                  refine ⟨6985845425304969818765645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18628921134146586183375053 6985845425304969818765645)
                  ·
                    refine ⟨2619692034489363682037117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6985845425304969818765645 2619692034489363682037117)
                    ·
                      refine ⟨982384512933511380763919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619692034489363682037117 982384512933511380763919)
                      ·
                        rfl

theorem cell23_1913187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1913187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913187 prefixEnd_1913187 := by exact prefixLift 1913187
  have htrace : WordTrace (prefixWord ++ tailWord_1913187) baseStart_1913187 baseEnd_1913187 := by
    simpa [prefixWord, tailWord_1913187, baseEnd_1913187] using wordTrace_append hprefix tailTrace_1913187
  have hstable : (prefixWord ++ tailWord_1913187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913187).length < 2 ^ (prefixWord ++ tailWord_1913187).sum := by decide
  have hdescent : baseEnd_1913187 < baseStart_1913187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913247 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1913247 : Nat := 118140960795 + 1913247 * 2 ^ 59
def prefixEnd_1913247 : Nat := 4983230072969 + 3 ^ 40 * 1913247 * 2
def baseEnd_1913247 : Nat := 982415321772781146013643

theorem tailTrace_1913247 : CollatzResearch.WordTrace tailWord_1913247 prefixEnd_1913247 982415321772781146013643 := by
  unfold tailWord_1913247
  simp only [CollatzResearch.WordTrace]
  refine ⟨69781850899640350418289995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46521233933093566945526663 69781850899640350418289995)
  ·
    refine ⟨104672776349460525627434993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69781850899640350418289995 104672776349460525627434993)
    ·
      refine ⟨78504582262095394220576245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104672776349460525627434993 78504582262095394220576245)
      ·
        refine ⟨7359804587071443208179023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78504582262095394220576245 7359804587071443208179023)
        ·
          refine ⟨11039706880607164812268535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359804587071443208179023 11039706880607164812268535)
          ·
            refine ⟨16559560320910747218402803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039706880607164812268535 16559560320910747218402803)
            ·
              refine ⟨24839340481366120827604205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16559560320910747218402803 24839340481366120827604205)
              ·
                refine ⟨9314752680512295310351577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24839340481366120827604205 9314752680512295310351577)
                ·
                  refine ⟨6986064510384221482763683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9314752680512295310351577 6986064510384221482763683)
                  ·
                    refine ⟨10479096765576332224145525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986064510384221482763683 10479096765576332224145525)
                    ·
                      refine ⟨982415321772781146013643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10479096765576332224145525 982415321772781146013643)
                      ·
                        rfl

theorem cell23_1913247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1913247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913247 prefixEnd_1913247 := by exact prefixLift 1913247
  have htrace : WordTrace (prefixWord ++ tailWord_1913247) baseStart_1913247 baseEnd_1913247 := by
    simpa [prefixWord, tailWord_1913247, baseEnd_1913247] using wordTrace_append hprefix tailTrace_1913247
  have hstable : (prefixWord ++ tailWord_1913247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913247).length < 2 ^ (prefixWord ++ tailWord_1913247).sum := by decide
  have hdescent : baseEnd_1913247 < baseStart_1913247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913248 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2]
def baseStart_1913248 : Nat := 118140960795 + 1913248 * 2 ^ 59
def prefixEnd_1913248 : Nat := 4983230072969 + 3 ^ 40 * 1913248 * 2
def baseEnd_1913248 : Nat := 982415835253435642101139

theorem tailTrace_1913248 : CollatzResearch.WordTrace tailWord_1913248 prefixEnd_1913248 982415835253435642101139 := by
  unfold tailWord_1913248
  simp only [CollatzResearch.WordTrace]
  refine ⟨34890943686318363794538199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46521258248424485059384265 34890943686318363794538199)
  ·
    refine ⟨52336415529477545691807299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34890943686318363794538199 52336415529477545691807299)
    ·
      refine ⟨78504623294216318537710949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52336415529477545691807299 78504623294216318537710949)
      ·
        refine ⟨14719616867665559725820803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78504623294216318537710949 14719616867665559725820803)
        ·
          refine ⟨22079425301498339588731205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14719616867665559725820803 22079425301498339588731205)
          ·
            refine ⟨4139892244030938672887101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22079425301498339588731205 4139892244030938672887101)
            ·
              refine ⟨1552459591511602002332663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4139892244030938672887101 1552459591511602002332663)
              ·
                refine ⟨2328689387267403003498995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552459591511602002332663 2328689387267403003498995)
                ·
                  refine ⟨3493034080901104505248493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328689387267403003498995 3493034080901104505248493)
                  ·
                    refine ⟨1309887780337914189468185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493034080901104505248493 1309887780337914189468185)
                    ·
                      refine ⟨982415835253435642101139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309887780337914189468185 982415835253435642101139)
                      ·
                        rfl

theorem cell23_1913248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_1913248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913248 prefixEnd_1913248 := by exact prefixLift 1913248
  have htrace : WordTrace (prefixWord ++ tailWord_1913248) baseStart_1913248 baseEnd_1913248 := by
    simpa [prefixWord, tailWord_1913248, baseEnd_1913248] using wordTrace_append hprefix tailTrace_1913248
  have hstable : (prefixWord ++ tailWord_1913248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913248).length < 2 ^ (prefixWord ++ tailWord_1913248).sum := by decide
  have hdescent : baseEnd_1913248 < baseStart_1913248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913278 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1913278 : Nat := 118140960795 + 1913278 * 2 ^ 59
def prefixEnd_1913278 : Nat := 4983230072969 + 3 ^ 40 * 1913278 * 2
def baseEnd_1913278 : Nat := 982431239673070524726001

theorem tailTrace_1913278 : CollatzResearch.WordTrace tailWord_1913278 prefixEnd_1913278 982431239673070524726001 := by
  unfold tailWord_1913278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722872695316005339083561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46521987708352028475112325 8722872695316005339083561)
  ·
    refine ⟨6542154521487004004312671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8722872695316005339083561 6542154521487004004312671)
    ·
      refine ⟨9813231782230506006469007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542154521487004004312671 9813231782230506006469007)
      ·
        refine ⟨14719847673345759009703511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813231782230506006469007 14719847673345759009703511)
        ·
          refine ⟨22079771510018638514555267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14719847673345759009703511 22079771510018638514555267)
          ·
            refine ⟨33119657265027957771832901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22079771510018638514555267 33119657265027957771832901)
            ·
              refine ⟨6209935737192742082218669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33119657265027957771832901 6209935737192742082218669)
              ·
                refine ⟨2328725901447278280832001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6209935737192742082218669 2328725901447278280832001)
                ·
                  refine ⟨1746544426085458710624001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328725901447278280832001 1746544426085458710624001)
                  ·
                    refine ⟨1309908319564094032968001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1746544426085458710624001 1309908319564094032968001)
                    ·
                      refine ⟨982431239673070524726001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1309908319564094032968001 982431239673070524726001)
                      ·
                        rfl

theorem cell23_1913278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1913278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913278 prefixEnd_1913278 := by exact prefixLift 1913278
  have htrace : WordTrace (prefixWord ++ tailWord_1913278) baseStart_1913278 baseEnd_1913278 := by
    simpa [prefixWord, tailWord_1913278, baseEnd_1913278] using wordTrace_append hprefix tailTrace_1913278
  have hstable : (prefixWord ++ tailWord_1913278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913278).length < 2 ^ (prefixWord ++ tailWord_1913278).sum := by decide
  have hdescent : baseEnd_1913278 < baseStart_1913278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913301 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 5]
def baseStart_1913301 : Nat := 118140960795 + 1913301 * 2 ^ 59
def prefixEnd_1913301 : Nat := 4983230072969 + 3 ^ 40 * 1913301 * 2
def baseEnd_1913301 : Nat := 109160338858680437193155

theorem tailTrace_1913301 : CollatzResearch.WordTrace tailWord_1913301 prefixEnd_1913301 109160338858680437193155 := by
  unfold tailWord_1913301
  simp only [CollatzResearch.WordTrace]
  refine ⟨69783820441444717640755757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46522546960963145093837171 69783820441444717640755757)
  ·
    refine ⟨26168932665541769115283409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69783820441444717640755757 26168932665541769115283409)
    ·
      refine ⟨19626699499156326836462557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26168932665541769115283409 19626699499156326836462557)
      ·
        refine ⟨7360012312183622563673459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19626699499156326836462557 7360012312183622563673459)
        ·
          refine ⟨11040018468275433845510189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360012312183622563673459 11040018468275433845510189)
          ·
            refine ⟨4140006925603287692066321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11040018468275433845510189 4140006925603287692066321)
            ·
              refine ⟨3105005194202465769049741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140006925603287692066321 3105005194202465769049741)
              ·
                refine ⟨1164376947825924663393653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105005194202465769049741 1164376947825924663393653)
                ·
                  refine ⟨109160338858680437193155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164376947825924663393653 109160338858680437193155)
                  ·
                    rfl

theorem cell23_1913301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_1913301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913301 prefixEnd_1913301 := by exact prefixLift 1913301
  have htrace : WordTrace (prefixWord ++ tailWord_1913301) baseStart_1913301 baseEnd_1913301 := by
    simpa [prefixWord, tailWord_1913301, baseEnd_1913301] using wordTrace_append hprefix tailTrace_1913301
  have hstable : (prefixWord ++ tailWord_1913301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913301).length < 2 ^ (prefixWord ++ tailWord_1913301).sum := by decide
  have hdescent : baseEnd_1913301 < baseStart_1913301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913334 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1913334 : Nat := 118140960795 + 1913334 * 2 ^ 59
def prefixEnd_1913334 : Nat := 4983230072969 + 3 ^ 40 * 1913334 * 2
def baseEnd_1913334 : Nat := 982459994589722305625743

theorem tailTrace_1913334 : CollatzResearch.WordTrace tailWord_1913334 prefixEnd_1913334 982459994589722305625743 := by
  unfold tailWord_1913334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361564003145322767294191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46523349366883442851138037 4361564003145322767294191)
  ·
    refine ⟨6542346004717984150941287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361564003145322767294191 6542346004717984150941287)
    ·
      refine ⟨9813519007076976226411931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542346004717984150941287 9813519007076976226411931)
      ·
        refine ⟨14720278510615464339617897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813519007076976226411931 14720278510615464339617897)
        ·
          refine ⟨11040208882961598254713423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720278510615464339617897 11040208882961598254713423)
          ·
            refine ⟨16560313324442397382070135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040208882961598254713423 16560313324442397382070135)
            ·
              refine ⟨24840469986663596073105203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560313324442397382070135 24840469986663596073105203)
              ·
                refine ⟨37260704979995394109657805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24840469986663596073105203 37260704979995394109657805)
                ·
                  refine ⟨13972764367498272791121677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37260704979995394109657805 13972764367498272791121677)
                  ·
                    refine ⟨5239786637811852296670629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13972764367498272791121677 5239786637811852296670629)
                    ·
                      refine ⟨982459994589722305625743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5239786637811852296670629 982459994589722305625743)
                      ·
                        rfl

theorem cell23_1913334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1913334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913334 prefixEnd_1913334 := by exact prefixLift 1913334
  have htrace : WordTrace (prefixWord ++ tailWord_1913334) baseStart_1913334 baseEnd_1913334 := by
    simpa [prefixWord, tailWord_1913334, baseEnd_1913334] using wordTrace_append hprefix tailTrace_1913334
  have hstable : (prefixWord ++ tailWord_1913334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913334).length < 2 ^ (prefixWord ++ tailWord_1913334).sum := by decide
  have hdescent : baseEnd_1913334 < baseStart_1913334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913347 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_1913347 : Nat := 118140960795 + 1913347 * 2 ^ 59
def prefixEnd_1913347 : Nat := 4983230072969 + 3 ^ 40 * 1913347 * 2
def baseEnd_1913347 : Nat := 982466669838230754763183

theorem tailTrace_1913347 : CollatzResearch.WordTrace tailWord_1913347 prefixEnd_1913347 982466669838230754763183 := by
  unfold tailWord_1913347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69785498199278067496930295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46523665466185378331286863 69785498199278067496930295)
  ·
    refine ⟨104678247298917101245395443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69785498199278067496930295 104678247298917101245395443)
    ·
      refine ⟨157017370948375651868093165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104678247298917101245395443 157017370948375651868093165)
      ·
        refine ⟨58881514105640869450534937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157017370948375651868093165 58881514105640869450534937)
        ·
          refine ⟨44161135579230652087901203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58881514105640869450534937 44161135579230652087901203)
          ·
            refine ⟨66241703368845978131851805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44161135579230652087901203 66241703368845978131851805)
            ·
              refine ⟨24840638763317241799444427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66241703368845978131851805 24840638763317241799444427)
              ·
                refine ⟨37260958144975862699166641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24840638763317241799444427 37260958144975862699166641)
                ·
                  refine ⟨27945718608731897024374981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37260958144975862699166641 27945718608731897024374981)
                  ·
                    refine ⟨5239822239137230692070309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27945718608731897024374981 5239822239137230692070309)
                    ·
                      refine ⟨982466669838230754763183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5239822239137230692070309 982466669838230754763183)
                      ·
                        rfl

theorem cell23_1913347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_1913347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913347 prefixEnd_1913347 := by exact prefixLift 1913347
  have htrace : WordTrace (prefixWord ++ tailWord_1913347) baseStart_1913347 baseEnd_1913347 := by
    simpa [prefixWord, tailWord_1913347, baseEnd_1913347] using wordTrace_append hprefix tailTrace_1913347
  have hstable : (prefixWord ++ tailWord_1913347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913347).length < 2 ^ (prefixWord ++ tailWord_1913347).sum := by decide
  have hdescent : baseEnd_1913347 < baseStart_1913347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913354 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1913354 : Nat := 118140960795 + 1913354 * 2 ^ 59
def prefixEnd_1913354 : Nat := 4983230072969 + 3 ^ 40 * 1913354 * 2
def baseEnd_1913354 : Nat := 982470264202812227375651

theorem tailTrace_1913354 : CollatzResearch.WordTrace tailWord_1913354 prefixEnd_1913354 982470264202812227375651 := by
  unfold tailWord_1913354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446438377563176923108779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46523835673501805128290077 17446438377563176923108779)
  ·
    refine ⟨26169657566344765384663169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17446438377563176923108779 26169657566344765384663169)
    ·
      refine ⟨19627243174758574038497377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26169657566344765384663169 19627243174758574038497377)
      ·
        refine ⟨14720432381068930528873033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19627243174758574038497377 14720432381068930528873033)
        ·
          refine ⟨11040324285801697896654775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720432381068930528873033 11040324285801697896654775)
          ·
            refine ⟨16560486428702546844982163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040324285801697896654775 16560486428702546844982163)
            ·
              refine ⟨24840729643053820267473245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560486428702546844982163 24840729643053820267473245)
              ·
                refine ⟨9315273616145182600302467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24840729643053820267473245 9315273616145182600302467)
                ·
                  refine ⟨13972910424217773900453701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315273616145182600302467 13972910424217773900453701)
                  ·
                    refine ⟨2619920704540832606335069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13972910424217773900453701 2619920704540832606335069)
                    ·
                      refine ⟨982470264202812227375651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619920704540832606335069 982470264202812227375651)
                      ·
                        rfl

theorem cell23_1913354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1913354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913354 prefixEnd_1913354 := by exact prefixLift 1913354
  have htrace : WordTrace (prefixWord ++ tailWord_1913354) baseStart_1913354 baseEnd_1913354 := by
    simpa [prefixWord, tailWord_1913354, baseEnd_1913354] using wordTrace_append hprefix tailTrace_1913354
  have hstable : (prefixWord ++ tailWord_1913354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913354).length < 2 ^ (prefixWord ++ tailWord_1913354).sum := by decide
  have hdescent : baseEnd_1913354 < baseStart_1913354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913361 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 1, 4]
def baseStart_1913361 : Nat := 118140960795 + 1913361 * 2 ^ 59
def prefixEnd_1913361 : Nat := 4983230072969 + 3 ^ 40 * 1913361 * 2
def baseEnd_1913361 : Nat := 327491286189131233329373

theorem tailTrace_1913361 : CollatzResearch.WordTrace tailWord_1913361 prefixEnd_1913361 327491286189131233329373 := by
  unfold tailWord_1913361
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786008821227347887939937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46524005880818231925293291 69786008821227347887939937)
  ·
    refine ⟨52339506615920510915954953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69786008821227347887939937 52339506615920510915954953)
    ·
      refine ⟨39254629961940383186966215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52339506615920510915954953 39254629961940383186966215)
      ·
        refine ⟨58881944942910574780449323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39254629961940383186966215 58881944942910574780449323)
        ·
          refine ⟨88322917414365862170673985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58881944942910574780449323 88322917414365862170673985)
          ·
            refine ⟨66242188060774396628005489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88322917414365862170673985 66242188060774396628005489)
            ·
              refine ⟨49681641045580797471004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66242188060774396628005489 49681641045580797471004117)
              ·
                refine ⟨1164413462005799940726659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49681641045580797471004117 1164413462005799940726659)
                ·
                  refine ⟨1746620193008699911089989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164413462005799940726659 1746620193008699911089989)
                  ·
                    refine ⟨327491286189131233329373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746620193008699911089989 327491286189131233329373)
                    ·
                      rfl

theorem cell23_1913361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_1913361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913361 prefixEnd_1913361 := by exact prefixLift 1913361
  have htrace : WordTrace (prefixWord ++ tailWord_1913361) baseStart_1913361 baseEnd_1913361 := by
    simpa [prefixWord, tailWord_1913361, baseEnd_1913361] using wordTrace_append hprefix tailTrace_1913361
  have hstable : (prefixWord ++ tailWord_1913361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913361).length < 2 ^ (prefixWord ++ tailWord_1913361).sum := by decide
  have hdescent : baseEnd_1913361 < baseStart_1913361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913401 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1913401 : Nat := 118140960795 + 1913401 * 2 ^ 59
def prefixEnd_1913401 : Nat := 4983230072969 + 3 ^ 40 * 1913401 * 2
def baseEnd_1913401 : Nat := 982494397793573543487935

theorem tailTrace_1913401 : CollatzResearch.WordTrace tailWord_1913401 prefixEnd_1913401 982494397793573543487935 := by
  unfold tailWord_1913401
  simp only [CollatzResearch.WordTrace]
  refine ⟨69787467741082434719396057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46524978494054956479597371 69787467741082434719396057)
  ·
    refine ⟨52340600805811826039547043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69787467741082434719396057 52340600805811826039547043)
    ·
      refine ⟨78510901208717739059320565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52340600805811826039547043 78510901208717739059320565)
      ·
        refine ⟨7360396988317288036811303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78510901208717739059320565 7360396988317288036811303)
        ·
          refine ⟨11040595482475932055216955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360396988317288036811303 11040595482475932055216955)
          ·
            refine ⟨16560893223713898082825433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040595482475932055216955 16560893223713898082825433)
            ·
              refine ⟨12420669917785423562119075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16560893223713898082825433 12420669917785423562119075)
              ·
                refine ⟨18631004876678135343178613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420669917785423562119075 18631004876678135343178613)
                ·
                  refine ⟨1746656707188575188422995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18631004876678135343178613 1746656707188575188422995)
                  ·
                    refine ⟨2619985060782862782634493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746656707188575188422995 2619985060782862782634493)
                    ·
                      refine ⟨982494397793573543487935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2619985060782862782634493 982494397793573543487935)
                      ·
                        rfl

theorem cell23_1913401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1913401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913401 prefixEnd_1913401 := by exact prefixLift 1913401
  have htrace : WordTrace (prefixWord ++ tailWord_1913401) baseStart_1913401 baseEnd_1913401 := by
    simpa [prefixWord, tailWord_1913401, baseEnd_1913401] using wordTrace_append hprefix tailTrace_1913401
  have hstable : (prefixWord ++ tailWord_1913401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913401).length < 2 ^ (prefixWord ++ tailWord_1913401).sum := by decide
  have hdescent : baseEnd_1913401 < baseStart_1913401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913428 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1913428 : Nat := 118140960795 + 1913428 * 2 ^ 59
def prefixEnd_1913428 : Nat := 4983230072969 + 3 ^ 40 * 1913428 * 2
def baseEnd_1913428 : Nat := 982508261771244937850311

theorem tailTrace_1913428 : CollatzResearch.WordTrace tailWord_1913428 prefixEnd_1913428 982508261771244937850311 := by
  unfold tailWord_1913428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34894226255992309165314469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46525635007989745553752625 34894226255992309165314469)
  ·
    refine ⟨6542667422998557968496463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34894226255992309165314469 6542667422998557968496463)
    ·
      refine ⟨9814001134497836952744695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542667422998557968496463 9814001134497836952744695)
      ·
        refine ⟨14721001701746755429117043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814001134497836952744695 14721001701746755429117043)
        ·
          refine ⟨22081502552620133143675565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14721001701746755429117043 22081502552620133143675565)
          ·
            refine ⟨8280563457232549928878337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22081502552620133143675565 8280563457232549928878337)
            ·
              refine ⟨6210422592924412446658753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8280563457232549928878337 6210422592924412446658753)
              ·
                refine ⟨4657816944693309334994065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6210422592924412446658753 4657816944693309334994065)
                ·
                  refine ⟨3493362708519982001245549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657816944693309334994065 3493362708519982001245549)
                  ·
                    refine ⟨1310011015694993250467081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493362708519982001245549 1310011015694993250467081)
                    ·
                      refine ⟨982508261771244937850311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310011015694993250467081 982508261771244937850311)
                      ·
                        rfl

theorem cell23_1913428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1913428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913428 prefixEnd_1913428 := by exact prefixLift 1913428
  have htrace : WordTrace (prefixWord ++ tailWord_1913428) baseStart_1913428 baseEnd_1913428 := by
    simpa [prefixWord, tailWord_1913428, baseEnd_1913428] using wordTrace_append hprefix tailTrace_1913428
  have hstable : (prefixWord ++ tailWord_1913428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913428).length < 2 ^ (prefixWord ++ tailWord_1913428).sum := by decide
  have hdescent : baseEnd_1913428 < baseStart_1913428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913444 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1913444 : Nat := 118140960795 + 1913444 * 2 ^ 59
def prefixEnd_1913444 : Nat := 4983230072969 + 3 ^ 40 * 1913444 * 2
def baseEnd_1913444 : Nat := 982516477461716875250237

theorem tailTrace_1913444 : CollatzResearch.WordTrace tailWord_1913444 prefixEnd_1913444 982516477461716875250237 := by
  unfold tailWord_1913444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34894518039963326531605693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46526024053284435375474257 34894518039963326531605693)
  ·
    refine ⟨13085444264986247449352135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34894518039963326531605693 13085444264986247449352135)
    ·
      refine ⟨19628166397479371174028203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13085444264986247449352135 19628166397479371174028203)
      ·
        refine ⟨29442249596219056761042305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19628166397479371174028203 29442249596219056761042305)
        ·
          refine ⟨22081687197164292570781729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29442249596219056761042305 22081687197164292570781729)
          ·
            refine ⟨16561265397873219428086297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22081687197164292570781729 16561265397873219428086297)
            ·
              refine ⟨12420949048404914571064723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16561265397873219428086297 12420949048404914571064723)
              ·
                refine ⟨18631423572607371856597085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420949048404914571064723 18631423572607371856597085)
                ·
                  refine ⟨6986783839727764446223907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18631423572607371856597085 6986783839727764446223907)
                  ·
                    refine ⟨10480175759591646669335861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6986783839727764446223907 10480175759591646669335861)
                    ·
                      refine ⟨982516477461716875250237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10480175759591646669335861 982516477461716875250237)
                      ·
                        rfl

theorem cell23_1913444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1913444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913444 prefixEnd_1913444 := by exact prefixLift 1913444
  have htrace : WordTrace (prefixWord ++ tailWord_1913444) baseStart_1913444 baseEnd_1913444 := by
    simpa [prefixWord, tailWord_1913444, baseEnd_1913444] using wordTrace_append hprefix tailTrace_1913444
  have hstable : (prefixWord ++ tailWord_1913444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913444).length < 2 ^ (prefixWord ++ tailWord_1913444).sum := by decide
  have hdescent : baseEnd_1913444 < baseStart_1913444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913462 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1913462 : Nat := 118140960795 + 1913462 * 2 ^ 59
def prefixEnd_1913462 : Nat := 4983230072969 + 3 ^ 40 * 1913462 * 2
def baseEnd_1913462 : Nat := 982525720113497804825155

theorem tailTrace_1913462 : CollatzResearch.WordTrace tailWord_1913462 prefixEnd_1913462 982525720113497804825155 := by
  unfold tailWord_1913462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361855787116340133585415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46526461729240961424911093 4361855787116340133585415)
  ·
    refine ⟨6542783680674510200378123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361855787116340133585415 6542783680674510200378123)
    ·
      refine ⟨9814175521011765300567185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542783680674510200378123 9814175521011765300567185)
      ·
        refine ⟨7360631640758823975425389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9814175521011765300567185 7360631640758823975425389)
        ·
          refine ⟨2760236865284558990784521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7360631640758823975425389 2760236865284558990784521)
          ·
            refine ⟨2070177648963419243088391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760236865284558990784521 2070177648963419243088391)
            ·
              refine ⟨3105266473445128864632587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070177648963419243088391 3105266473445128864632587)
              ·
                refine ⟨4657899710167693296948881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105266473445128864632587 4657899710167693296948881)
                ·
                  refine ⟨3493424782625769972711661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657899710167693296948881 3493424782625769972711661)
                  ·
                    refine ⟨1310034293484663739766873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493424782625769972711661 1310034293484663739766873)
                    ·
                      refine ⟨982525720113497804825155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310034293484663739766873 982525720113497804825155)
                      ·
                        rfl

theorem cell23_1913462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1913462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913462 prefixEnd_1913462 := by exact prefixLift 1913462
  have htrace : WordTrace (prefixWord ++ tailWord_1913462) baseStart_1913462 baseEnd_1913462 := by
    simpa [prefixWord, tailWord_1913462, baseEnd_1913462] using wordTrace_append hprefix tailTrace_1913462
  have hstable : (prefixWord ++ tailWord_1913462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913462).length < 2 ^ (prefixWord ++ tailWord_1913462).sum := by decide
  have hdescent : baseEnd_1913462 < baseStart_1913462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913475 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 1, 2, 2]
def baseStart_1913475 : Nat := 118140960795 + 1913475 * 2 ^ 59
def prefixEnd_1913475 : Nat := 4983230072969 + 3 ^ 40 * 1913475 * 2
def baseEnd_1913475 : Nat := 982532395362006253962595

theorem tailTrace_1913475 : CollatzResearch.WordTrace tailWord_1913475 prefixEnd_1913475 982532395362006253962595 := by
  unfold tailWord_1913475
  simp only [CollatzResearch.WordTrace]
  refine ⟨69790166742814345357589879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46526777828542896905059919 69790166742814345357589879)
  ·
    refine ⟨104685250114221518036384819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69790166742814345357589879 104685250114221518036384819)
    ·
      refine ⟨157027875171332277054577229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104685250114221518036384819 157027875171332277054577229)
      ·
        refine ⟨58885453189249603895466461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157027875171332277054577229 58885453189249603895466461)
        ·
          refine ⟨22082044945968601460799923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58885453189249603895466461 22082044945968601460799923)
          ·
            refine ⟨33123067418952902191199885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22082044945968601460799923 33123067418952902191199885)
            ·
              refine ⟨12421150282107338321699957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33123067418952902191199885 12421150282107338321699957)
              ·
                refine ⟨1164482838947562967659371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12421150282107338321699957 1164482838947562967659371)
                ·
                  refine ⟨1746724258421344451489057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164482838947562967659371 1746724258421344451489057)
                  ·
                    refine ⟨1310043193816008338616793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1746724258421344451489057 1310043193816008338616793)
                    ·
                      refine ⟨982532395362006253962595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310043193816008338616793 982532395362006253962595)
                      ·
                        rfl

theorem cell23_1913475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_1913475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913475 prefixEnd_1913475 := by exact prefixLift 1913475
  have htrace : WordTrace (prefixWord ++ tailWord_1913475) baseStart_1913475 baseEnd_1913475 := by
    simpa [prefixWord, tailWord_1913475, baseEnd_1913475] using wordTrace_append hprefix tailTrace_1913475
  have hstable : (prefixWord ++ tailWord_1913475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913475).length < 2 ^ (prefixWord ++ tailWord_1913475).sum := by decide
  have hdescent : baseEnd_1913475 < baseStart_1913475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913491 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 3]
def baseStart_1913491 : Nat := 118140960795 + 1913491 * 2 ^ 59
def prefixEnd_1913491 : Nat := 4983230072969 + 3 ^ 40 * 1913491 * 2
def baseEnd_1913491 : Nat := 982540611052478191362521

theorem tailTrace_1913491 : CollatzResearch.WordTrace tailWord_1913491 prefixEnd_1913491 982540611052478191362521 := by
  unfold tailWord_1913491
  simp only [CollatzResearch.WordTrace]
  refine ⟨69790750310756380090172327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46527166873837586726781551 69790750310756380090172327)
  ·
    refine ⟨104686125466134570135258491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69790750310756380090172327 104686125466134570135258491)
    ·
      refine ⟨157029188199201855202887737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104686125466134570135258491 157029188199201855202887737)
      ·
        refine ⟨117771891149401391402165803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157029188199201855202887737 117771891149401391402165803)
        ·
          refine ⟨176657836724102087103248705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117771891149401391402165803 176657836724102087103248705)
          ·
            refine ⟨132493377543076565327436529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176657836724102087103248705 132493377543076565327436529)
            ·
              refine ⟨99370033157307423995577397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132493377543076565327436529 99370033157307423995577397)
              ·
                refine ⟨9315940608497570999585381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99370033157307423995577397 9315940608497570999585381)
                ·
                  refine ⟨1746738864093294562422259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9315940608497570999585381 1746738864093294562422259)
                  ·
                    refine ⟨2620108296139941843633389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746738864093294562422259 2620108296139941843633389)
                    ·
                      refine ⟨982540611052478191362521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620108296139941843633389 982540611052478191362521)
                      ·
                        rfl

theorem cell23_1913491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_1913491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913491 prefixEnd_1913491 := by exact prefixLift 1913491
  have htrace : WordTrace (prefixWord ++ tailWord_1913491) baseStart_1913491 baseEnd_1913491 := by
    simpa [prefixWord, tailWord_1913491, baseEnd_1913491] using wordTrace_append hprefix tailTrace_1913491
  have hstable : (prefixWord ++ tailWord_1913491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913491).length < 2 ^ (prefixWord ++ tailWord_1913491).sum := by decide
  have hdescent : baseEnd_1913491 < baseStart_1913491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913492 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1913492 : Nat := 118140960795 + 1913492 * 2 ^ 59
def prefixEnd_1913492 : Nat := 4983230072969 + 3 ^ 40 * 1913492 * 2
def baseEnd_1913492 : Nat := 982541124533132687450017

theorem tailTrace_1913492 : CollatzResearch.WordTrace tailWord_1913492 prefixEnd_1913492 982541124533132687450017 := by
  unfold tailWord_1913492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34895393391876378630479365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46527191189168504840639153 34895393391876378630479365)
  ·
    refine ⟨6542886260976820993214881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34895393391876378630479365 6542886260976820993214881)
    ·
      refine ⟨4907164695732615744911161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6542886260976820993214881 4907164695732615744911161)
      ·
        refine ⟨3680373521799461808683371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4907164695732615744911161 3680373521799461808683371)
        ·
          refine ⟨5520560282699192713025057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680373521799461808683371 5520560282699192713025057)
          ·
            refine ⟨4140420212024394534768793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5520560282699192713025057 4140420212024394534768793)
            ·
              refine ⟨3105315159018295901076595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140420212024394534768793 3105315159018295901076595)
              ·
                refine ⟨4657972738527443851614893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105315159018295901076595 4657972738527443851614893)
                ·
                  refine ⟨1746739776947791444355585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4657972738527443851614893 1746739776947791444355585)
                  ·
                    refine ⟨1310054832710843583266689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1746739776947791444355585 1310054832710843583266689)
                    ·
                      refine ⟨982541124533132687450017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310054832710843583266689 982541124533132687450017)
                      ·
                        rfl

theorem cell23_1913492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1913492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913492 prefixEnd_1913492 := by exact prefixLift 1913492
  have htrace : WordTrace (prefixWord ++ tailWord_1913492) baseStart_1913492 baseEnd_1913492 := by
    simpa [prefixWord, tailWord_1913492, baseEnd_1913492] using wordTrace_append hprefix tailTrace_1913492
  have hstable : (prefixWord ++ tailWord_1913492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913492).length < 2 ^ (prefixWord ++ tailWord_1913492).sum := by decide
  have hdescent : baseEnd_1913492 < baseStart_1913492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913505 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1913505 : Nat := 118140960795 + 1913505 * 2 ^ 59
def prefixEnd_1913505 : Nat := 4983230072969 + 3 ^ 40 * 1913505 * 2
def baseEnd_1913505 : Nat := 982547799781641136587457

theorem tailTrace_1913505 : CollatzResearch.WordTrace tailWord_1913505 prefixEnd_1913505 982547799781641136587457 := by
  unfold tailWord_1913505
  simp only [CollatzResearch.WordTrace]
  refine ⟨69791260932705660481181969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46527507288470440320787979 69791260932705660481181969)
  ·
    refine ⟨52343445699529245360886477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69791260932705660481181969 52343445699529245360886477)
    ·
      refine ⟨19628792137323467010332429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52343445699529245360886477 19628792137323467010332429)
      ·
        refine ⟨7360797051496300128874661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19628792137323467010332429 7360797051496300128874661)
        ·
          refine ⟨1380149447155556274163999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7360797051496300128874661 1380149447155556274163999)
          ·
            refine ⟨2070224170733334411245999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380149447155556274163999 2070224170733334411245999)
            ·
              refine ⟨3105336256100001616868999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070224170733334411245999 3105336256100001616868999)
              ·
                refine ⟨4658004384150002425303499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105336256100001616868999 4658004384150002425303499)
                ·
                  refine ⟨6987006576225003637955249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658004384150002425303499 6987006576225003637955249)
                  ·
                    refine ⟨5240254932168752728466437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6987006576225003637955249 5240254932168752728466437)
                    ·
                      refine ⟨982547799781641136587457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5240254932168752728466437 982547799781641136587457)
                      ·
                        rfl

theorem cell23_1913505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1913505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913505 prefixEnd_1913505 := by exact prefixLift 1913505
  have htrace : WordTrace (prefixWord ++ tailWord_1913505) baseStart_1913505 baseEnd_1913505 := by
    simpa [prefixWord, tailWord_1913505, baseEnd_1913505] using wordTrace_append hprefix tailTrace_1913505
  have hstable : (prefixWord ++ tailWord_1913505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913505).length < 2 ^ (prefixWord ++ tailWord_1913505).sum := by decide
  have hdescent : baseEnd_1913505 < baseStart_1913505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913608 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_1913608 : Nat := 118140960795 + 1913608 * 2 ^ 59
def prefixEnd_1913608 : Nat := 4983230072969 + 3 ^ 40 * 1913608 * 2
def baseEnd_1913608 : Nat := 982600688289054233599483

theorem tailTrace_1913608 : CollatzResearch.WordTrace tailWord_1913608 prefixEnd_1913608 982600688289054233599483 := by
  unfold tailWord_1913608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897508825666254536090739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46530011767555006048120985 34897508825666254536090739)
  ·
    refine ⟨52346263238499381804136109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34897508825666254536090739 52346263238499381804136109)
    ·
      refine ⟨19629848714437268176551041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52346263238499381804136109 19629848714437268176551041)
      ·
        refine ⟨14722386535827951132413281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19629848714437268176551041 14722386535827951132413281)
        ·
          refine ⟨11041789901870963349309961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14722386535827951132413281 11041789901870963349309961)
          ·
            refine ⟨8281342426403222511982471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11041789901870963349309961 8281342426403222511982471)
            ·
              refine ⟨12422013639604833767973707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281342426403222511982471 12422013639604833767973707)
              ·
                refine ⟨18633020459407250651960561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422013639604833767973707 18633020459407250651960561)
                ·
                  refine ⟨13974765344555437988970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633020459407250651960561 13974765344555437988970421)
                  ·
                    refine ⟨1310134251052072311465977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13974765344555437988970421 1310134251052072311465977)
                    ·
                      refine ⟨982600688289054233599483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310134251052072311465977 982600688289054233599483)
                      ·
                        rfl

theorem cell23_1913608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_1913608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913608 prefixEnd_1913608 := by exact prefixLift 1913608
  have htrace : WordTrace (prefixWord ++ tailWord_1913608) baseStart_1913608 baseEnd_1913608 := by
    simpa [prefixWord, tailWord_1913608, baseEnd_1913608] using wordTrace_append hprefix tailTrace_1913608
  have hstable : (prefixWord ++ tailWord_1913608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913608).length < 2 ^ (prefixWord ++ tailWord_1913608).sum := by decide
  have hdescent : baseEnd_1913608 < baseStart_1913608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913621 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1913621 : Nat := 118140960795 + 1913621 * 2 ^ 59
def prefixEnd_1913621 : Nat := 4983230072969 + 3 ^ 40 * 1913621 * 2
def baseEnd_1913621 : Nat := 982607363537562682736923

theorem tailTrace_1913621 : CollatzResearch.WordTrace tailWord_1913621 prefixEnd_1913621 982607363537562682736923 := by
  unfold tailWord_1913621
  simp only [CollatzResearch.WordTrace]
  refine ⟨69795491800285412292404717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46530327866856941528269811 69795491800285412292404717)
  ·
    refine ⟨26173309425107029609651769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69795491800285412292404717 26173309425107029609651769)
    ·
      refine ⟨19629982068830272207238827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26173309425107029609651769 19629982068830272207238827)
      ·
        refine ⟨29444973103245408310858241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19629982068830272207238827 29444973103245408310858241)
        ·
          refine ⟨22083729827434056233143681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29444973103245408310858241 22083729827434056233143681)
          ·
            refine ⟨16562797370575542174857761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22083729827434056233143681 16562797370575542174857761)
            ·
              refine ⟨12422098027931656631143321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16562797370575542174857761 12422098027931656631143321)
              ·
                refine ⟨9316573520948742473357491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422098027931656631143321 9316573520948742473357491)
                ·
                  refine ⟨13974860281423113710036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316573520948742473357491 13974860281423113710036237)
                  ·
                    refine ⟨5240572605533667641263589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13974860281423113710036237 5240572605533667641263589)
                    ·
                      refine ⟨982607363537562682736923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5240572605533667641263589 982607363537562682736923)
                      ·
                        rfl

theorem cell23_1913621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1913621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913621 prefixEnd_1913621 := by exact prefixLift 1913621
  have htrace : WordTrace (prefixWord ++ tailWord_1913621) baseStart_1913621 baseEnd_1913621 := by
    simpa [prefixWord, tailWord_1913621, baseEnd_1913621] using wordTrace_append hprefix tailTrace_1913621
  have hstable : (prefixWord ++ tailWord_1913621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913621).length < 2 ^ (prefixWord ++ tailWord_1913621).sum := by decide
  have hdescent : baseEnd_1913621 < baseStart_1913621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913641 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_1913641 : Nat := 118140960795 + 1913641 * 2 ^ 59
def prefixEnd_1913641 : Nat := 4983230072969 + 3 ^ 40 * 1913641 * 2
def baseEnd_1913641 : Nat := 982617633150652604486831

theorem tailTrace_1913641 : CollatzResearch.WordTrace tailWord_1913641 prefixEnd_1913641 982617633150652604486831 := by
  unfold tailWord_1913641
  simp only [CollatzResearch.WordTrace]
  refine ⟨69796221260212955708132777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46530814173475303805421851 69796221260212955708132777)
  ·
    refine ⟨52347165945159716781099583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69796221260212955708132777 52347165945159716781099583)
    ·
      refine ⟨78520748917739575171649375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52347165945159716781099583 78520748917739575171649375)
      ·
        refine ⟨117781123376609362757474063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78520748917739575171649375 117781123376609362757474063)
        ·
          refine ⟨176671685064914044136211095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117781123376609362757474063 176671685064914044136211095)
          ·
            refine ⟨265007527597371066204316643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176671685064914044136211095 265007527597371066204316643)
            ·
              refine ⟨397511291396056599306474965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265007527597371066204316643 397511291396056599306474965)
              ·
                refine ⟨9316670892095076546245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397511291396056599306474965 9316670892095076546245507)
                ·
                  refine ⟨13975006338142614819368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316670892095076546245507 13975006338142614819368261)
                  ·
                    refine ⟨2620313688401740278631549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13975006338142614819368261 2620313688401740278631549)
                    ·
                      refine ⟨982617633150652604486831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620313688401740278631549 982617633150652604486831)
                      ·
                        rfl

theorem cell23_1913641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_1913641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913641 prefixEnd_1913641 := by exact prefixLift 1913641
  have htrace : WordTrace (prefixWord ++ tailWord_1913641) baseStart_1913641 baseEnd_1913641 := by
    simpa [prefixWord, tailWord_1913641, baseEnd_1913641] using wordTrace_append hprefix tailTrace_1913641
  have hstable : (prefixWord ++ tailWord_1913641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913641).length < 2 ^ (prefixWord ++ tailWord_1913641).sum := by decide
  have hdescent : baseEnd_1913641 < baseStart_1913641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913651 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_1913651 : Nat := 118140960795 + 1913651 * 2 ^ 59
def prefixEnd_1913651 : Nat := 4983230072969 + 3 ^ 40 * 1913651 * 2
def baseEnd_1913651 : Nat := 982622767957197565361785

theorem tailTrace_1913651 : CollatzResearch.WordTrace tailWord_1913651 prefixEnd_1913651 982622767957197565361785 := by
  unfold tailWord_1913651
  simp only [CollatzResearch.WordTrace]
  refine ⟨69796585990176727415996807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46531057326784484943997871 69796585990176727415996807)
  ·
    refine ⟨104694878985265091123995211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69796585990176727415996807 104694878985265091123995211)
    ·
      refine ⟨157042318477897636685992817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104694878985265091123995211 157042318477897636685992817)
      ·
        refine ⟨117781738858423227514494613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157042318477897636685992817 117781738858423227514494613)
        ·
          refine ⟨5521019008988588789741935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117781738858423227514494613 5521019008988588789741935)
          ·
            refine ⟨8281528513482883184612903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521019008988588789741935 8281528513482883184612903)
            ·
              refine ⟨12422292770224324776919355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281528513482883184612903 12422292770224324776919355)
              ·
                refine ⟨18633439155336487165379033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12422292770224324776919355 18633439155336487165379033)
                ·
                  refine ⟨13975079366502365374034275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18633439155336487165379033 13975079366502365374034275)
                  ·
                    refine ⟨20962619049753548061051413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13975079366502365374034275 20962619049753548061051413)
                    ·
                      refine ⟨982622767957197565361785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20962619049753548061051413 982622767957197565361785)
                      ·
                        rfl

theorem cell23_1913651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_1913651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913651 prefixEnd_1913651 := by exact prefixLift 1913651
  have htrace : WordTrace (prefixWord ++ tailWord_1913651) baseStart_1913651 baseEnd_1913651 := by
    simpa [prefixWord, tailWord_1913651, baseEnd_1913651] using wordTrace_append hprefix tailTrace_1913651
  have hstable : (prefixWord ++ tailWord_1913651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913651).length < 2 ^ (prefixWord ++ tailWord_1913651).sum := by decide
  have hdescent : baseEnd_1913651 < baseStart_1913651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913708 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1913708 : Nat := 118140960795 + 1913708 * 2 ^ 59
def prefixEnd_1913708 : Nat := 4983230072969 + 3 ^ 40 * 1913708 * 2
def baseEnd_1913708 : Nat := 327550678784834614116341

theorem tailTrace_1913708 : CollatzResearch.WordTrace tailWord_1913708 prefixEnd_1913708 327550678784834614116341 := by
  unfold tailWord_1913708
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899332475485113075410889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46532443300646817433881185 34899332475485113075410889)
  ·
    refine ⟨26174499356613834806558167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34899332475485113075410889 26174499356613834806558167)
    ·
      refine ⟨39261749034920752209837251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26174499356613834806558167 39261749034920752209837251)
      ·
        refine ⟨58892623552381128314755877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39261749034920752209837251 58892623552381128314755877)
        ·
          refine ⟨11042366916071461559016727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58892623552381128314755877 11042366916071461559016727)
          ·
            refine ⟨16563550374107192338525091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11042366916071461559016727 16563550374107192338525091)
            ·
              refine ⟨24845325561160788507787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16563550374107192338525091 24845325561160788507787637)
              ·
                refine ⟨2329249271358823922605091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24845325561160788507787637 2329249271358823922605091)
                ·
                  refine ⟨3493873907038235883907637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329249271358823922605091 3493873907038235883907637)
                  ·
                    refine ⟨327550678784834614116341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3493873907038235883907637 327550678784834614116341)
                    ·
                      rfl

theorem cell23_1913708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1913708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913708 prefixEnd_1913708 := by exact prefixLift 1913708
  have htrace : WordTrace (prefixWord ++ tailWord_1913708) baseStart_1913708 baseEnd_1913708 := by
    simpa [prefixWord, tailWord_1913708, baseEnd_1913708] using wordTrace_append hprefix tailTrace_1913708
  have hstable : (prefixWord ++ tailWord_1913708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913708).length < 2 ^ (prefixWord ++ tailWord_1913708).sum := by decide
  have hdescent : baseEnd_1913708 < baseStart_1913708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913728 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2]
def baseStart_1913728 : Nat := 118140960795 + 1913728 * 2 ^ 59
def prefixEnd_1913728 : Nat := 4983230072969 + 3 ^ 40 * 1913728 * 2
def baseEnd_1913728 : Nat := 982662305967593764098931

theorem tailTrace_1913728 : CollatzResearch.WordTrace tailWord_1913728 prefixEnd_1913728 982662305967593764098931 := by
  unfold tailWord_1913728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899697205448884783274919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46532929607265179711033225 34899697205448884783274919)
  ·
    refine ⟨52349545808173327174912379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34899697205448884783274919 52349545808173327174912379)
    ·
      refine ⟨78524318712259990762368569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52349545808173327174912379 78524318712259990762368569)
      ·
        refine ⟨58893239034194993071776427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78524318712259990762368569 58893239034194993071776427)
        ·
          refine ⟨88339858551292489607664641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58893239034194993071776427 88339858551292489607664641)
          ·
            refine ⟨66254893913469367205748481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88339858551292489607664641 66254893913469367205748481)
            ·
              refine ⟨49691170435102025404311361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66254893913469367205748481 49691170435102025404311361)
              ·
                refine ⟨37268377826326519053233521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49691170435102025404311361 37268377826326519053233521)
                ·
                  refine ⟨27951283369744889289925141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37268377826326519053233521 27951283369744889289925141)
                  ·
                    refine ⟨1310216407956791685465241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27951283369744889289925141 1310216407956791685465241)
                    ·
                      refine ⟨982662305967593764098931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310216407956791685465241 982662305967593764098931)
                      ·
                        rfl

theorem cell23_1913728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_1913728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913728 prefixEnd_1913728 := by exact prefixLift 1913728
  have htrace : WordTrace (prefixWord ++ tailWord_1913728) baseStart_1913728 baseEnd_1913728 := by
    simpa [prefixWord, tailWord_1913728, baseEnd_1913728] using wordTrace_append hprefix tailTrace_1913728
  have hstable : (prefixWord ++ tailWord_1913728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913728).length < 2 ^ (prefixWord ++ tailWord_1913728).sum := by decide
  have hdescent : baseEnd_1913728 < baseStart_1913728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913745 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_1913745 : Nat := 118140960795 + 1913745 * 2 ^ 59
def prefixEnd_1913745 : Nat := 4983230072969 + 3 ^ 40 * 1913745 * 2
def baseEnd_1913745 : Nat := 982671035138720197586353

theorem tailTrace_1913745 : CollatzResearch.WordTrace tailWord_1913745 prefixEnd_1913745 982671035138720197586353 := by
  unfold tailWord_1913745
  simp only [CollatzResearch.WordTrace]
  refine ⟨69800014451836181469918689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46533342967890787646612459 69800014451836181469918689)
  ·
    refine ⟨52350010838877136102439017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69800014451836181469918689 52350010838877136102439017)
    ·
      refine ⟨39262508129157852076829263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52350010838877136102439017 39262508129157852076829263)
      ·
        refine ⟨58893762193736778115243895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39262508129157852076829263 58893762193736778115243895)
        ·
          refine ⟨88340643290605167172865843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58893762193736778115243895 88340643290605167172865843)
          ·
            refine ⟨132510964935907750759298765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88340643290605167172865843 132510964935907750759298765)
            ·
              refine ⟨49691611850965406534737037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132510964935907750759298765 49691611850965406534737037)
              ·
                refine ⟨18634354444112027450526389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49691611850965406534737037 18634354444112027450526389)
                ·
                  refine ⟨1746970729135502573486849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18634354444112027450526389 1746970729135502573486849)
                  ·
                    refine ⟨1310228046851626930115137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1746970729135502573486849 1310228046851626930115137)
                    ·
                      refine ⟨982671035138720197586353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310228046851626930115137 982671035138720197586353)
                      ·
                        rfl

theorem cell23_1913745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_1913745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913745 prefixEnd_1913745 := by exact prefixLift 1913745
  have htrace : WordTrace (prefixWord ++ tailWord_1913745) baseStart_1913745 baseEnd_1913745 := by
    simpa [prefixWord, tailWord_1913745, baseEnd_1913745] using wordTrace_append hprefix tailTrace_1913745
  have hstable : (prefixWord ++ tailWord_1913745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913745).length < 2 ^ (prefixWord ++ tailWord_1913745).sum := by decide
  have hdescent : baseEnd_1913745 < baseStart_1913745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913751 : List Nat := [1, 1, 3, 3, 1, 2, 1, 11]
def baseStart_1913751 : Nat := 118140960795 + 1913751 * 2 ^ 59
def prefixEnd_1913751 : Nat := 4983230072969 + 3 ^ 40 * 1913751 * 2
def baseEnd_1913751 : Nat := 36395337630468413855975

theorem tailTrace_1913751 : CollatzResearch.WordTrace tailWord_1913751 prefixEnd_1913751 36395337630468413855975 := by
  unfold tailWord_1913751
  simp only [CollatzResearch.WordTrace]
  refine ⟨69800233289814444494637107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46533488859876296329758071 69800233289814444494637107)
  ·
    refine ⟨104700349934721666741955661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69800233289814444494637107 104700349934721666741955661)
    ·
      refine ⟨39262631225520625028233373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104700349934721666741955661 39262631225520625028233373)
      ·
        refine ⟨14723486709570234385587515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39262631225520625028233373 14723486709570234385587515)
        ·
          refine ⟨22085230064355351578381273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14723486709570234385587515 22085230064355351578381273)
          ·
            refine ⟨16563922548266513683785955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22085230064355351578381273 16563922548266513683785955)
            ·
              refine ⟨24845883822399770525678933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16563922548266513683785955 24845883822399770525678933)
              ·
                refine ⟨36395337630468413855975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24845883822399770525678933 36395337630468413855975)
                ·
                  rfl

theorem cell23_1913751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 11].length) (baseStart_1913751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913751 prefixEnd_1913751 := by exact prefixLift 1913751
  have htrace : WordTrace (prefixWord ++ tailWord_1913751) baseStart_1913751 baseEnd_1913751 := by
    simpa [prefixWord, tailWord_1913751, baseEnd_1913751] using wordTrace_append hprefix tailTrace_1913751
  have hstable : (prefixWord ++ tailWord_1913751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913751).length < 2 ^ (prefixWord ++ tailWord_1913751).sum := by decide
  have hdescent : baseEnd_1913751 < baseStart_1913751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913796 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1913796 : Nat := 118140960795 + 1913796 * 2 ^ 59
def prefixEnd_1913796 : Nat := 4983230072969 + 3 ^ 40 * 1913796 * 2
def baseEnd_1913796 : Nat := 982697222652099498048619

theorem tailTrace_1913796 : CollatzResearch.WordTrace tailWord_1913796 prefixEnd_1913796 982697222652099498048619 := by
  unfold tailWord_1913796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34900937287325708590012621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46534583049767611453350161 34900937287325708590012621)
  ·
    refine ⟨13087851482747140721254733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34900937287325708590012621 13087851482747140721254733)
    ·
      refine ⟨4907944306030177770470525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13087851482747140721254733 4907944306030177770470525)
      ·
        refine ⟨1840479114761316663926447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4907944306030177770470525 1840479114761316663926447)
        ·
          refine ⟨2760718672141974995889671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840479114761316663926447 2760718672141974995889671)
          ·
            refine ⟨4141078008212962493834507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760718672141974995889671 4141078008212962493834507)
            ·
              refine ⟨6211617012319443740751761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141078008212962493834507 6211617012319443740751761)
              ·
                refine ⟨4658712759239582805563821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211617012319443740751761 4658712759239582805563821)
                ·
                  refine ⟨1747017284714843552086433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4658712759239582805563821 1747017284714843552086433)
                  ·
                    refine ⟨1310262963536132664064825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747017284714843552086433 1310262963536132664064825)
                    ·
                      refine ⟨982697222652099498048619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310262963536132664064825 982697222652099498048619)
                      ·
                        rfl

theorem cell23_1913796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1913796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913796 prefixEnd_1913796 := by exact prefixLift 1913796
  have htrace : WordTrace (prefixWord ++ tailWord_1913796) baseStart_1913796 baseEnd_1913796 := by
    simpa [prefixWord, tailWord_1913796, baseEnd_1913796] using wordTrace_append hprefix tailTrace_1913796
  have hstable : (prefixWord ++ tailWord_1913796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913796).length < 2 ^ (prefixWord ++ tailWord_1913796).sum := by decide
  have hdescent : baseEnd_1913796 < baseStart_1913796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913801 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1913801 : Nat := 118140960795 + 1913801 * 2 ^ 59
def prefixEnd_1913801 : Nat := 4983230072969 + 3 ^ 40 * 1913801 * 2
def baseEnd_1913801 : Nat := 982699790055371978486095

theorem tailTrace_1913801 : CollatzResearch.WordTrace tailWord_1913801 prefixEnd_1913801 982699790055371978486095 := by
  unfold tailWord_1913801
  simp only [CollatzResearch.WordTrace]
  refine ⟨69802056939633303033957257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46534704626422202022638171 69802056939633303033957257)
  ·
    refine ⟨52351542704724977275467943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69802056939633303033957257 52351542704724977275467943)
    ·
      refine ⟨78527314057087465913201915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52351542704724977275467943 78527314057087465913201915)
      ·
        refine ⟨117790971085631198869802873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78527314057087465913201915 117790971085631198869802873)
        ·
          refine ⟨88343228314223399152352155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117790971085631198869802873 88343228314223399152352155)
          ·
            refine ⟨132514842471335098728528233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88343228314223399152352155 132514842471335098728528233)
            ·
              refine ⟨99386131853501324046396175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132514842471335098728528233 99386131853501324046396175)
              ·
                refine ⟨149079197780251986069594263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99386131853501324046396175 149079197780251986069594263)
                ·
                  refine ⟨223618796670377979104391395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149079197780251986069594263 223618796670377979104391395)
                  ·
                    refine ⟨335428195005566968656587093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223618796670377979104391395 335428195005566968656587093)
                    ·
                      refine ⟨982699790055371978486095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 335428195005566968656587093 982699790055371978486095)
                      ·
                        rfl

theorem cell23_1913801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1913801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913801 prefixEnd_1913801 := by exact prefixLift 1913801
  have htrace : WordTrace (prefixWord ++ tailWord_1913801) baseStart_1913801 baseEnd_1913801 := by
    simpa [prefixWord, tailWord_1913801, baseEnd_1913801] using wordTrace_append hprefix tailTrace_1913801
  have hstable : (prefixWord ++ tailWord_1913801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913801).length < 2 ^ (prefixWord ++ tailWord_1913801).sum := by decide
  have hdescent : baseEnd_1913801 < baseStart_1913801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913829 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1913829 : Nat := 118140960795 + 1913829 * 2 ^ 59
def prefixEnd_1913829 : Nat := 4983230072969 + 3 ^ 40 * 1913829 * 2
def baseEnd_1913829 : Nat := 982714167513697868935967

theorem tailTrace_1913829 : CollatzResearch.WordTrace tailWord_1913829 prefixEnd_1913829 982714167513697868935967 := by
  unfold tailWord_1913829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803078183531863815976541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46535385455687909210651027 69803078183531863815976541)
  ·
    refine ⟨26176154318824448930991203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69803078183531863815976541 26176154318824448930991203)
    ·
      refine ⟨39264231478236673396486805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26176154318824448930991203 39264231478236673396486805)
      ·
        refine ⟨1840510850542344065460319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39264231478236673396486805 1840510850542344065460319)
        ·
          refine ⟨2760766275813516098190479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840510850542344065460319 2760766275813516098190479)
          ·
            refine ⟨4141149413720274147285719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760766275813516098190479 4141149413720274147285719)
            ·
              refine ⟨6211724120580411220928579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141149413720274147285719 6211724120580411220928579)
              ·
                refine ⟨9317586180870616831392869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211724120580411220928579 9317586180870616831392869)
                ·
                  refine ⟨1747047408913240655886163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9317586180870616831392869 1747047408913240655886163)
                  ·
                    refine ⟨2620571113369860983829245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747047408913240655886163 2620571113369860983829245)
                    ·
                      refine ⟨982714167513697868935967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620571113369860983829245 982714167513697868935967)
                      ·
                        rfl

theorem cell23_1913829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1913829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913829 prefixEnd_1913829 := by exact prefixLift 1913829
  have htrace : WordTrace (prefixWord ++ tailWord_1913829) baseStart_1913829 baseEnd_1913829 := by
    simpa [prefixWord, tailWord_1913829, baseEnd_1913829] using wordTrace_append hprefix tailTrace_1913829
  have hstable : (prefixWord ++ tailWord_1913829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913829).length < 2 ^ (prefixWord ++ tailWord_1913829).sum := by decide
  have hdescent : baseEnd_1913829 < baseStart_1913829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913846 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1913846 : Nat := 118140960795 + 1913846 * 2 ^ 59
def prefixEnd_1913846 : Nat := 4983230072969 + 3 ^ 40 * 1913846 * 2
def baseEnd_1913846 : Nat := 982722896684824302423389

theorem tailTrace_1913846 : CollatzResearch.WordTrace tailWord_1913846 prefixEnd_1913846 982722896684824302423389 := by
  unfold tailWord_1913846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362731139029392232459087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46535798816313517146230261 4362731139029392232459087)
  ·
    refine ⟨6544096708544088348688631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4362731139029392232459087 6544096708544088348688631)
    ·
      refine ⟨9816145062816132523032947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544096708544088348688631 9816145062816132523032947)
      ·
        refine ⟨14724217594224198784549421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816145062816132523032947 14724217594224198784549421)
        ·
          refine ⟨5521581597834074544206033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14724217594224198784549421 5521581597834074544206033)
          ·
            refine ⟨4141186198375555908154525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521581597834074544206033 4141186198375555908154525)
            ·
              refine ⟨1552944824390833465557947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4141186198375555908154525 1552944824390833465557947)
              ·
                refine ⟨2329417236586250198336921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552944824390833465557947 2329417236586250198336921)
                ·
                  refine ⟨1747062927439687648752691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329417236586250198336921 1747062927439687648752691)
                  ·
                    refine ⟨2620594391159531473129037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747062927439687648752691 2620594391159531473129037)
                    ·
                      refine ⟨982722896684824302423389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620594391159531473129037 982722896684824302423389)
                      ·
                        rfl

theorem cell23_1913846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1913846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913846 prefixEnd_1913846 := by exact prefixLift 1913846
  have htrace : WordTrace (prefixWord ++ tailWord_1913846) baseStart_1913846 baseEnd_1913846 := by
    simpa [prefixWord, tailWord_1913846, baseEnd_1913846] using wordTrace_append hprefix tailTrace_1913846
  have hstable : (prefixWord ++ tailWord_1913846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913846).length < 2 ^ (prefixWord ++ tailWord_1913846).sum := by decide
  have hdescent : baseEnd_1913846 < baseStart_1913846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913852 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_1913852 : Nat := 118140960795 + 1913852 * 2 ^ 59
def prefixEnd_1913852 : Nat := 4983230072969 + 3 ^ 40 * 1913852 * 2
def baseEnd_1913852 : Nat := 982725977568751278948361

theorem tailTrace_1913852 : CollatzResearch.WordTrace tailWord_1913852 prefixEnd_1913852 982725977568751278948361 := by
  unfold tailWord_1913852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34901958531224269372031905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46535944708299025829375873 34901958531224269372031905)
  ·
    refine ⟨26176468898418202029023929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34901958531224269372031905 26176468898418202029023929)
    ·
      refine ⟨19632351673813651521767947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26176468898418202029023929 19632351673813651521767947)
      ·
        refine ⟨29448527510720477282651921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19632351673813651521767947 29448527510720477282651921)
        ·
          refine ⟨22086395633040357961988941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29448527510720477282651921 22086395633040357961988941)
          ·
            refine ⟨8282398362390134235745853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22086395633040357961988941 8282398362390134235745853)
            ·
              refine ⟨3105899385896300338404695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8282398362390134235745853 3105899385896300338404695)
              ·
                refine ⟨4658849078844450507607043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105899385896300338404695 4658849078844450507607043)
                ·
                  refine ⟨6988273618266675761410565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658849078844450507607043 6988273618266675761410565)
                  ·
                    refine ⟨1310301303425001705264481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988273618266675761410565 1310301303425001705264481)
                    ·
                      refine ⟨982725977568751278948361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310301303425001705264481 982725977568751278948361)
                      ·
                        rfl

theorem cell23_1913852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_1913852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913852 prefixEnd_1913852 := by exact prefixLift 1913852
  have htrace : WordTrace (prefixWord ++ tailWord_1913852) baseStart_1913852 baseEnd_1913852 := by
    simpa [prefixWord, tailWord_1913852, baseEnd_1913852] using wordTrace_append hprefix tailTrace_1913852
  have hstable : (prefixWord ++ tailWord_1913852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913852).length < 2 ^ (prefixWord ++ tailWord_1913852).sum := by decide
  have hdescent : baseEnd_1913852 < baseStart_1913852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913892 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 7]
def baseStart_1913892 : Nat := 118140960795 + 1913892 * 2 ^ 59
def prefixEnd_1913892 : Nat := 4983230072969 + 3 ^ 40 * 1913892 * 2
def baseEnd_1913892 : Nat := 109194057421659013605353

theorem tailTrace_1913892 : CollatzResearch.WordTrace tailWord_1913892 prefixEnd_1913892 109194057421659013605353 := by
  unfold tailWord_1913892
  simp only [CollatzResearch.WordTrace]
  refine ⟨34902687991151812787759965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46536917321535750383679953 34902687991151812787759965)
  ·
    refine ⟨13088507996681929795409987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34902687991151812787759965 13088507996681929795409987)
    ·
      refine ⟨19632761995022894693114981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13088507996681929795409987 19632761995022894693114981)
      ·
        refine ⟨3681142874066792754959059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19632761995022894693114981 3681142874066792754959059)
        ·
          refine ⟨5521714311100189132438589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681142874066792754959059 5521714311100189132438589)
          ·
            refine ⟨2070642866662570924664471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5521714311100189132438589 2070642866662570924664471)
            ·
              refine ⟨3105964299993856386996707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070642866662570924664471 3105964299993856386996707)
              ·
                refine ⟨4658946449990784580495061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105964299993856386996707 4658946449990784580495061)
                ·
                  refine ⟨109194057421659013605353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4658946449990784580495061 109194057421659013605353)
                  ·
                    rfl

theorem cell23_1913892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_1913892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913892 prefixEnd_1913892 := by exact prefixLift 1913892
  have htrace : WordTrace (prefixWord ++ tailWord_1913892) baseStart_1913892 baseEnd_1913892 := by
    simpa [prefixWord, tailWord_1913892, baseEnd_1913892] using wordTrace_append hprefix tailTrace_1913892
  have hstable : (prefixWord ++ tailWord_1913892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913892).length < 2 ^ (prefixWord ++ tailWord_1913892).sum := by decide
  have hdescent : baseEnd_1913892 < baseStart_1913892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913925 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1913925 : Nat := 118140960795 + 1913925 * 2 ^ 59
def prefixEnd_1913925 : Nat := 4983230072969 + 3 ^ 40 * 1913925 * 2
def baseEnd_1913925 : Nat := 982763461656529493335525

theorem tailTrace_1913925 : CollatzResearch.WordTrace tailWord_1913925 prefixEnd_1913925 982763461656529493335525 := by
  unfold tailWord_1913925
  simp only [CollatzResearch.WordTrace]
  refine ⟨69806579591184072211471229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46537719727456048140980819 69806579591184072211471229)
  ·
    refine ⟨26177467346694027079301711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69806579591184072211471229 26177467346694027079301711)
    ·
      refine ⟨39266201020041040618952567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26177467346694027079301711 39266201020041040618952567)
      ·
        refine ⟨58899301530061560928428851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39266201020041040618952567 58899301530061560928428851)
        ·
          refine ⟨88348952295092341392643277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58899301530061560928428851 88348952295092341392643277)
          ·
            refine ⟨33130857110659628022241229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88348952295092341392643277 33130857110659628022241229)
            ·
              refine ⟨12424071416497360508340461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33130857110659628022241229 12424071416497360508340461)
              ·
                refine ⟨4659026781186510190627673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12424071416497360508340461 4659026781186510190627673)
                ·
                  refine ⟨3494270085889882642970755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659026781186510190627673 3494270085889882642970755)
                  ·
                    refine ⟨5241405128834823964456133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3494270085889882642970755 5241405128834823964456133)
                    ·
                      refine ⟨982763461656529493335525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5241405128834823964456133 982763461656529493335525)
                      ·
                        rfl

theorem cell23_1913925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1913925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913925 prefixEnd_1913925 := by exact prefixLift 1913925
  have htrace : WordTrace (prefixWord ++ tailWord_1913925) baseStart_1913925 baseEnd_1913925 := by
    simpa [prefixWord, tailWord_1913925, baseEnd_1913925] using wordTrace_append hprefix tailTrace_1913925
  have hstable : (prefixWord ++ tailWord_1913925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913925).length < 2 ^ (prefixWord ++ tailWord_1913925).sum := by decide
  have hdescent : baseEnd_1913925 < baseStart_1913925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913945 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1913945 : Nat := 118140960795 + 1913945 * 2 ^ 59
def prefixEnd_1913945 : Nat := 4983230072969 + 3 ^ 40 * 1913945 * 2
def baseEnd_1913945 : Nat := 982773731269619415085433

theorem tailTrace_1913945 : CollatzResearch.WordTrace tailWord_1913945 prefixEnd_1913945 982773731269619415085433 := by
  unfold tailWord_1913945
  simp only [CollatzResearch.WordTrace]
  refine ⟨69807309051111615627199289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46538206034074410418132859 69807309051111615627199289)
  ·
    refine ⟨52355481788333711720399467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69807309051111615627199289 52355481788333711720399467)
    ·
      refine ⟨78533222682500567580599201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52355481788333711720399467 78533222682500567580599201)
      ·
        refine ⟨58899917011875425685449401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78533222682500567580599201 58899917011875425685449401)
        ·
          refine ⟨44174937758906569264087051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58899917011875425685449401 44174937758906569264087051)
          ·
            refine ⟨66262406638359853896130577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44174937758906569264087051 66262406638359853896130577)
            ·
              refine ⟨49696804978769890422097933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66262406638359853896130577 49696804978769890422097933)
              ·
                refine ⟨18636301867038708908286725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49696804978769890422097933 18636301867038708908286725)
                ·
                  refine ⟨3494306600069757920303761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18636301867038708908286725 3494306600069757920303761)
                  ·
                    refine ⟨2620729950052318440227821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494306600069757920303761 2620729950052318440227821)
                    ·
                      refine ⟨982773731269619415085433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620729950052318440227821 982773731269619415085433)
                      ·
                        rfl

theorem cell23_1913945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1913945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1913945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1913945 prefixEnd_1913945 := by exact prefixLift 1913945
  have htrace : WordTrace (prefixWord ++ tailWord_1913945) baseStart_1913945 baseEnd_1913945 := by
    simpa [prefixWord, tailWord_1913945, baseEnd_1913945] using wordTrace_append hprefix tailTrace_1913945
  have hstable : (prefixWord ++ tailWord_1913945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913945).length < 2 ^ (prefixWord ++ tailWord_1913945).sum := by decide
  have hdescent : baseEnd_1913945 < baseStart_1913945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914026 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1914026 : Nat := 118140960795 + 1914026 * 2 ^ 59
def prefixEnd_1914026 : Nat := 4983230072969 + 3 ^ 40 * 1914026 * 2
def baseEnd_1914026 : Nat := 982815323202633598172561

theorem tailTrace_1914026 : CollatzResearch.WordTrace tailWord_1914026 prefixEnd_1914026 982815323202633598172561 := by
  unfold tailWord_1914026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452565840954541615224483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46540175575878777640598621 17452565840954541615224483)
  ·
    refine ⟨26178848761431812422836725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17452565840954541615224483 26178848761431812422836725)
    ·
      refine ⟨2454267071384232414640943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26178848761431812422836725 2454267071384232414640943)
      ·
        refine ⟨3681400607076348621961415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454267071384232414640943 3681400607076348621961415)
        ·
          refine ⟨5522100910614522932942123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681400607076348621961415 5522100910614522932942123)
          ·
            refine ⟨8283151365921784399413185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522100910614522932942123 8283151365921784399413185)
            ·
              refine ⟨6212363524441338299559889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283151365921784399413185 6212363524441338299559889)
              ·
                refine ⟨4659272643331003724669917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6212363524441338299559889 4659272643331003724669917)
                ·
                  refine ⟨1747227241249126396751219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4659272643331003724669917 1747227241249126396751219)
                  ·
                    refine ⟨2620840861873689595126829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747227241249126396751219 2620840861873689595126829)
                    ·
                      refine ⟨982815323202633598172561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620840861873689595126829 982815323202633598172561)
                      ·
                        rfl

theorem cell23_1914026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1914026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914026 prefixEnd_1914026 := by exact prefixLift 1914026
  have htrace : WordTrace (prefixWord ++ tailWord_1914026) baseStart_1914026 baseEnd_1914026 := by
    simpa [prefixWord, tailWord_1914026, baseEnd_1914026] using wordTrace_append hprefix tailTrace_1914026
  have hstable : (prefixWord ++ tailWord_1914026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914026).length < 2 ^ (prefixWord ++ tailWord_1914026).sum := by decide
  have hdescent : baseEnd_1914026 < baseStart_1914026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914072 : List Nat := [2, 1, 2, 2, 5, 1, 2, 8]
def baseStart_1914072 : Nat := 118140960795 + 1914072 * 2 ^ 59
def prefixEnd_1914072 : Nat := 4983230072969 + 3 ^ 40 * 1914072 * 2
def baseEnd_1914072 : Nat := 36401442344916311785087

theorem tailTrace_1914072 : CollatzResearch.WordTrace tailWord_1914072 prefixEnd_1914072 36401442344916311785087 := by
  unfold tailWord_1914072
  simp only [CollatzResearch.WordTrace]
  refine ⟨34905970560825758158536235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46541294081101010878048313 34905970560825758158536235)
  ·
    refine ⟨52358955841238637237804353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34905970560825758158536235 52358955841238637237804353)
    ·
      refine ⟨39269216880928977928353265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52358955841238637237804353 39269216880928977928353265)
      ·
        refine ⟨29451912660696733446264949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39269216880928977928353265 29451912660696733446264949)
        ·
          refine ⟨2761116811940318760587339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29451912660696733446264949 2761116811940318760587339)
          ·
            refine ⟨4141675217910478140881009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761116811940318760587339 4141675217910478140881009)
            ·
              refine ⟨3106256413432858605660757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141675217910478140881009 3106256413432858605660757)
              ·
                refine ⟨36401442344916311785087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3106256413432858605660757 36401442344916311785087)
                ·
                  rfl

theorem cell23_1914072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 8].length) (baseStart_1914072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914072 prefixEnd_1914072 := by exact prefixLift 1914072
  have htrace : WordTrace (prefixWord ++ tailWord_1914072) baseStart_1914072 baseEnd_1914072 := by
    simpa [prefixWord, tailWord_1914072, baseEnd_1914072] using wordTrace_append hprefix tailTrace_1914072
  have hstable : (prefixWord ++ tailWord_1914072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914072).length < 2 ^ (prefixWord ++ tailWord_1914072).sum := by decide
  have hdescent : baseEnd_1914072 < baseStart_1914072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914116 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1914116 : Nat := 118140960795 + 1914116 * 2 ^ 59
def prefixEnd_1914116 : Nat := 4983230072969 + 3 ^ 40 * 1914116 * 2
def baseEnd_1914116 : Nat := 982861536461538246047147

theorem tailTrace_1914116 : CollatzResearch.WordTrace tailWord_1914116 prefixEnd_1914116 982861536461538246047147 := by
  unfold tailWord_1914116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34906772966746055915837101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46542363955661407887782801 34906772966746055915837101)
  ·
    refine ⟨13090039862529770968438913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34906772966746055915837101 13090039862529770968438913)
    ·
      refine ⟨9817529896897328226329185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13090039862529770968438913 9817529896897328226329185)
      ·
        refine ⟨7363147422672996169746889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9817529896897328226329185 7363147422672996169746889)
        ·
          refine ⟨5522360567004747127310167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7363147422672996169746889 5522360567004747127310167)
          ·
            refine ⟨8283540850507120690965251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522360567004747127310167 8283540850507120690965251)
            ·
              refine ⟨12425311275760681036447877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283540850507120690965251 12425311275760681036447877)
              ·
                refine ⟨2329745864205127694333977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12425311275760681036447877 2329745864205127694333977)
                ·
                  refine ⟨1747309398153845770750483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329745864205127694333977 1747309398153845770750483)
                  ·
                    refine ⟨2620964097230768656125725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747309398153845770750483 2620964097230768656125725)
                    ·
                      refine ⟨982861536461538246047147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2620964097230768656125725 982861536461538246047147)
                      ·
                        rfl

theorem cell23_1914116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1914116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914116 prefixEnd_1914116 := by exact prefixLift 1914116
  have htrace : WordTrace (prefixWord ++ tailWord_1914116) baseStart_1914116 baseEnd_1914116 := by
    simpa [prefixWord, tailWord_1914116, baseEnd_1914116] using wordTrace_append hprefix tailTrace_1914116
  have hstable : (prefixWord ++ tailWord_1914116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914116).length < 2 ^ (prefixWord ++ tailWord_1914116).sum := by decide
  have hdescent : baseEnd_1914116 < baseStart_1914116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914139 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 6, 2, 2]
def baseStart_1914139 : Nat := 118140960795 + 1914139 * 2 ^ 59
def prefixEnd_1914139 : Nat := 4983230072969 + 3 ^ 40 * 1914139 * 2
def baseEnd_1914139 : Nat := 982873346516591656059541

theorem tailTrace_1914139 : CollatzResearch.WordTrace tailWord_1914139 prefixEnd_1914139 982873346516591656059541 := by
  unfold tailWord_1914139
  simp only [CollatzResearch.WordTrace]
  refine ⟨69814384812408786759761471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46542923208272524506507647 69814384812408786759761471)
  ·
    refine ⟨104721577218613180139642207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69814384812408786759761471 104721577218613180139642207)
    ·
      refine ⟨157082365827919770209463311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104721577218613180139642207 157082365827919770209463311)
      ·
        refine ⟨235623548741879655314194967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157082365827919770209463311 235623548741879655314194967)
        ·
          refine ⟨353435323112819482971292451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235623548741879655314194967 353435323112819482971292451)
          ·
            refine ⟨530152984669229224456938677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353435323112819482971292451 530152984669229224456938677)
            ·
              refine ⟨49701842312740239792838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 530152984669229224456938677 49701842312740239792838001)
              ·
                refine ⟨37276381734555179844628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49701842312740239792838001 37276381734555179844628501)
                ·
                  refine ⟨1747330393807274055216961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37276381734555179844628501 1747330393807274055216961)
                  ·
                    refine ⟨1310497795355455541412721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747330393807274055216961 1310497795355455541412721)
                    ·
                      refine ⟨982873346516591656059541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310497795355455541412721 982873346516591656059541)
                      ·
                        rfl

theorem cell23_1914139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2, 2].length) (baseStart_1914139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914139 prefixEnd_1914139 := by exact prefixLift 1914139
  have htrace : WordTrace (prefixWord ++ tailWord_1914139) baseStart_1914139 baseEnd_1914139 := by
    simpa [prefixWord, tailWord_1914139, baseEnd_1914139] using wordTrace_append hprefix tailTrace_1914139
  have hstable : (prefixWord ++ tailWord_1914139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914139).length < 2 ^ (prefixWord ++ tailWord_1914139).sum := by decide
  have hdescent : baseEnd_1914139 < baseStart_1914139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914232 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1914232 : Nat := 118140960795 + 1914232 * 2 ^ 59
def prefixEnd_1914232 : Nat := 4983230072969 + 3 ^ 40 * 1914232 * 2
def baseEnd_1914232 : Nat := 982921100217459792196613

theorem tailTrace_1914232 : CollatzResearch.WordTrace tailWord_1914232 prefixEnd_1914232 982921100217459792196613 := by
  unfold tailWord_1914232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34908888400535931821448475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46545184534047909095264633 34908888400535931821448475)
  ·
    refine ⟨52363332600803897732172713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34908888400535931821448475 52363332600803897732172713)
    ·
      refine ⟨39272499450602923299129535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52363332600803897732172713 39272499450602923299129535)
      ·
        refine ⟨58908749175904384948694303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39272499450602923299129535 58908749175904384948694303)
        ·
          refine ⟨88363123763856577423041455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58908749175904384948694303 88363123763856577423041455)
          ·
            refine ⟨132544685645784866134562183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88363123763856577423041455 132544685645784866134562183)
            ·
              refine ⟨198817028468677299201843275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132544685645784866134562183 198817028468677299201843275)
              ·
                refine ⟨298225542703015948802764913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198817028468677299201843275 298225542703015948802764913)
                ·
                  refine ⟨223669157027261961602073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298225542703015948802764913 223669157027261961602073685)
                  ·
                    refine ⟨2621122933913226112524301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 223669157027261961602073685 2621122933913226112524301)
                    ·
                      refine ⟨982921100217459792196613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621122933913226112524301 982921100217459792196613)
                      ·
                        rfl

theorem cell23_1914232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1914232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914232 prefixEnd_1914232 := by exact prefixLift 1914232
  have htrace : WordTrace (prefixWord ++ tailWord_1914232) baseStart_1914232 baseEnd_1914232 := by
    simpa [prefixWord, tailWord_1914232, baseEnd_1914232] using wordTrace_append hprefix tailTrace_1914232
  have hstable : (prefixWord ++ tailWord_1914232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914232).length < 2 ^ (prefixWord ++ tailWord_1914232).sum := by decide
  have hdescent : baseEnd_1914232 < baseStart_1914232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914266 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1914266 : Nat := 118140960795 + 1914266 * 2 ^ 59
def prefixEnd_1914266 : Nat := 4983230072969 + 3 ^ 40 * 1914266 * 2
def baseEnd_1914266 : Nat := 982938558559712659171457

theorem tailTrace_1914266 : CollatzResearch.WordTrace tailWord_1914266 prefixEnd_1914266 982938558559712659171457 := by
  unfold tailWord_1914266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454754220737171862408663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46546011255299124966423101 17454754220737171862408663)
  ·
    refine ⟨26182131331105757793612995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17454754220737171862408663 26182131331105757793612995)
    ·
      refine ⟨39273196996658636690419493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26182131331105757793612995 39273196996658636690419493)
      ·
        refine ⟨7363724436873494379453655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39273196996658636690419493 7363724436873494379453655)
        ·
          refine ⟨11045586655310241569180483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363724436873494379453655 11045586655310241569180483)
          ·
            refine ⟨16568379982965362353770725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045586655310241569180483 16568379982965362353770725)
            ·
              refine ⟨3106571246806005441332011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16568379982965362353770725 3106571246806005441332011)
              ·
                refine ⟨4659856870209008161998017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106571246806005441332011 4659856870209008161998017)
                ·
                  refine ⟨3494892652656756121498513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659856870209008161998017 3494892652656756121498513)
                  ·
                    refine ⟨2621169489492567091123885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3494892652656756121498513 2621169489492567091123885)
                    ·
                      refine ⟨982938558559712659171457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621169489492567091123885 982938558559712659171457)
                      ·
                        rfl

theorem cell23_1914266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1914266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914266 prefixEnd_1914266 := by exact prefixLift 1914266
  have htrace : WordTrace (prefixWord ++ tailWord_1914266) baseStart_1914266 baseEnd_1914266 := by
    simpa [prefixWord, tailWord_1914266, baseEnd_1914266] using wordTrace_append hprefix tailTrace_1914266
  have hstable : (prefixWord ++ tailWord_1914266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914266).length < 2 ^ (prefixWord ++ tailWord_1914266).sum := by decide
  have hdescent : baseEnd_1914266 < baseStart_1914266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914319 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_1914319 : Nat := 118140960795 + 1914319 * 2 ^ 59
def prefixEnd_1914319 : Nat := 4983230072969 + 3 ^ 40 * 1914319 * 2
def baseEnd_1914319 : Nat := 982965773034400951808713

theorem tailTrace_1914319 : CollatzResearch.WordTrace tailWord_1914319 prefixEnd_1914319 982965773034400951808713 := by
  unfold tailWord_1914319
  simp only [CollatzResearch.WordTrace]
  refine ⟨69820949951756677501314011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46547299967837785000876007 69820949951756677501314011)
  ·
    refine ⟨104731424927635016251971017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69820949951756677501314011 104731424927635016251971017)
    ·
      refine ⟨78548568695726262188978263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104731424927635016251971017 78548568695726262188978263)
      ·
        refine ⟨117822853043589393283467395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78548568695726262188978263 117822853043589393283467395)
        ·
          refine ⟨176734279565384089925201093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117822853043589393283467395 176734279565384089925201093)
          ·
            refine ⟨33137677418509516860975205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176734279565384089925201093 33137677418509516860975205)
            ·
              refine ⟨6213314515970534411432851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33137677418509516860975205 6213314515970534411432851)
              ·
                refine ⟨9319971773955801617149277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213314515970534411432851 9319971773955801617149277)
                ·
                  refine ⟨3494989415233425606430979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9319971773955801617149277 3494989415233425606430979)
                  ·
                    refine ⟨5242484122850138409646469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3494989415233425606430979 5242484122850138409646469)
                    ·
                      refine ⟨982965773034400951808713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5242484122850138409646469 982965773034400951808713)
                      ·
                        rfl

theorem cell23_1914319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_1914319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914319 prefixEnd_1914319 := by exact prefixLift 1914319
  have htrace : WordTrace (prefixWord ++ tailWord_1914319) baseStart_1914319 baseEnd_1914319 := by
    simpa [prefixWord, tailWord_1914319, baseEnd_1914319] using wordTrace_append hprefix tailTrace_1914319
  have hstable : (prefixWord ++ tailWord_1914319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914319).length < 2 ^ (prefixWord ++ tailWord_1914319).sum := by decide
  have hdescent : baseEnd_1914319 < baseStart_1914319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914329 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_1914329 : Nat := 118140960795 + 1914329 * 2 ^ 59
def prefixEnd_1914329 : Nat := 4983230072969 + 3 ^ 40 * 1914329 * 2
def baseEnd_1914329 : Nat := 327656969280315304227889

theorem tailTrace_1914329 : CollatzResearch.WordTrace tailWord_1914329 prefixEnd_1914329 327656969280315304227889 := by
  unfold tailWord_1914329
  simp only [CollatzResearch.WordTrace]
  refine ⟨69821314681720449209178041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46547543121146966139452027 69821314681720449209178041)
  ·
    refine ⟨52365986011290336906883531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69821314681720449209178041 52365986011290336906883531)
    ·
      refine ⟨78548979016935505360325297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52365986011290336906883531 78548979016935505360325297)
      ·
        refine ⟨58911734262701629020243973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78548979016935505360325297 58911734262701629020243973)
        ·
          refine ⟨11045950174256555441295745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58911734262701629020243973 11045950174256555441295745)
          ·
            refine ⟨8284462630692416580971809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045950174256555441295745 8284462630692416580971809)
            ·
              refine ⟨6213346973019312435728857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284462630692416580971809 6213346973019312435728857)
              ·
                refine ⟨4660010229764484326796643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213346973019312435728857 4660010229764484326796643)
                ·
                  refine ⟨6990015344646726490194965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660010229764484326796643 6990015344646726490194965)
                  ·
                    refine ⟨327656969280315304227889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6990015344646726490194965 327656969280315304227889)
                    ·
                      rfl

theorem cell23_1914329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_1914329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914329 prefixEnd_1914329 := by exact prefixLift 1914329
  have htrace : WordTrace (prefixWord ++ tailWord_1914329) baseStart_1914329 baseEnd_1914329 := by
    simpa [prefixWord, tailWord_1914329, baseEnd_1914329] using wordTrace_append hprefix tailTrace_1914329
  have hstable : (prefixWord ++ tailWord_1914329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914329).length < 2 ^ (prefixWord ++ tailWord_1914329).sum := by decide
  have hdescent : baseEnd_1914329 < baseStart_1914329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914330 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_1914330 : Nat := 118140960795 + 1914330 * 2 ^ 59
def prefixEnd_1914330 : Nat := 4983230072969 + 3 ^ 40 * 1914330 * 2
def baseEnd_1914330 : Nat := 982971421321600408771163

theorem tailTrace_1914330 : CollatzResearch.WordTrace tailWord_1914330 prefixEnd_1914330 982971421321600408771163 := by
  unfold tailWord_1914330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455337788679206594991111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46547567436477884253309629 17455337788679206594991111)
  ·
    refine ⟨26183006683018809892486667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455337788679206594991111 26183006683018809892486667)
    ·
      refine ⟨39274510024528214838730001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26183006683018809892486667 39274510024528214838730001)
      ·
        refine ⟨29455882518396161129047501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39274510024528214838730001 29455882518396161129047501)
        ·
          refine ⟨11045955944398560423392813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29455882518396161129047501 11045955944398560423392813)
          ·
            refine ⟨4142233479149460158772305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11045955944398560423392813 4142233479149460158772305)
            ·
              refine ⟨3106675109362095119079229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142233479149460158772305 3106675109362095119079229)
              ·
                refine ⟨1165003166010785669654711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106675109362095119079229 1165003166010785669654711)
                ·
                  refine ⟨1747504749016178504482067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165003166010785669654711 1747504749016178504482067)
                  ·
                    refine ⟨2621257123524267756723101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747504749016178504482067 2621257123524267756723101)
                    ·
                      refine ⟨982971421321600408771163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621257123524267756723101 982971421321600408771163)
                      ·
                        rfl

theorem cell23_1914330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_1914330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914330 prefixEnd_1914330 := by exact prefixLift 1914330
  have htrace : WordTrace (prefixWord ++ tailWord_1914330) baseStart_1914330 baseEnd_1914330 := by
    simpa [prefixWord, tailWord_1914330, baseEnd_1914330] using wordTrace_append hprefix tailTrace_1914330
  have hstable : (prefixWord ++ tailWord_1914330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914330).length < 2 ^ (prefixWord ++ tailWord_1914330).sum := by decide
  have hdescent : baseEnd_1914330 < baseStart_1914330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914333 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1914333 : Nat := 118140960795 + 1914333 * 2 ^ 59
def prefixEnd_1914333 : Nat := 4983230072969 + 3 ^ 40 * 1914333 * 2
def baseEnd_1914333 : Nat := 327657653921187965677883

theorem tailTrace_1914333 : CollatzResearch.WordTrace tailWord_1914333 prefixEnd_1914333 327657653921187965677883 := by
  unfold tailWord_1914333
  simp only [CollatzResearch.WordTrace]
  refine ⟨69821460573705957892323653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46547640382470638594882435 69821460573705957892323653)
  ·
    refine ⟨13091523857569867104810685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69821460573705957892323653 13091523857569867104810685)
    ·
      refine ⟨4909321446588700164304007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13091523857569867104810685 4909321446588700164304007)
      ·
        refine ⟨7363982169883050246456011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909321446588700164304007 7363982169883050246456011)
        ·
          refine ⟨11045973254824575369684017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363982169883050246456011 11045973254824575369684017)
          ·
            refine ⟨8284479941118431527263013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045973254824575369684017 8284479941118431527263013)
            ·
              refine ⟨1553339988959705911361815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8284479941118431527263013 1553339988959705911361815)
              ·
                refine ⟨2330009983439558867042723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553339988959705911361815 2330009983439558867042723)
                ·
                  refine ⟨3495014975159338300564085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330009983439558867042723 3495014975159338300564085)
                  ·
                    refine ⟨327657653921187965677883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3495014975159338300564085 327657653921187965677883)
                    ·
                      rfl

theorem cell23_1914333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1914333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914333 prefixEnd_1914333 := by exact prefixLift 1914333
  have htrace : WordTrace (prefixWord ++ tailWord_1914333) baseStart_1914333 baseEnd_1914333 := by
    simpa [prefixWord, tailWord_1914333, baseEnd_1914333] using wordTrace_append hprefix tailTrace_1914333
  have hstable : (prefixWord ++ tailWord_1914333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914333).length < 2 ^ (prefixWord ++ tailWord_1914333).sum := by decide
  have hdescent : baseEnd_1914333 < baseStart_1914333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914353 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_1914353 : Nat := 118140960795 + 1914353 * 2 ^ 59
def prefixEnd_1914353 : Nat := 4983230072969 + 3 ^ 40 * 1914353 * 2
def baseEnd_1914353 : Nat := 982983231376653818783557

theorem tailTrace_1914353 : CollatzResearch.WordTrace tailWord_1914353 prefixEnd_1914353 982983231376653818783557 := by
  unfold tailWord_1914353
  simp only [CollatzResearch.WordTrace]
  refine ⟨69822190033633501308051713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46548126689089000872034475 69822190033633501308051713)
  ·
    refine ⟨52366642525225125981038785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69822190033633501308051713 52366642525225125981038785)
    ·
      refine ⟨39274981893918844485779089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52366642525225125981038785 39274981893918844485779089)
      ·
        refine ⟨29456236420439133364334317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39274981893918844485779089 29456236420439133364334317)
        ·
          refine ⟨11046088657664675011625369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29456236420439133364334317 11046088657664675011625369)
          ·
            refine ⟨8284566493248506258719027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046088657664675011625369 8284566493248506258719027)
            ·
              refine ⟨12426849739872759388078541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284566493248506258719027 12426849739872759388078541)
              ·
                refine ⟨4660068652452284770529453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12426849739872759388078541 4660068652452284770529453)
                ·
                  refine ⟨1747525744669606788948545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4660068652452284770529453 1747525744669606788948545)
                  ·
                    refine ⟨1310644308502205091711409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747525744669606788948545 1310644308502205091711409)
                    ·
                      refine ⟨982983231376653818783557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310644308502205091711409 982983231376653818783557)
                      ·
                        rfl

theorem cell23_1914353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_1914353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914353 prefixEnd_1914353 := by exact prefixLift 1914353
  have htrace : WordTrace (prefixWord ++ tailWord_1914353) baseStart_1914353 baseEnd_1914353 := by
    simpa [prefixWord, tailWord_1914353, baseEnd_1914353] using wordTrace_append hprefix tailTrace_1914353
  have hstable : (prefixWord ++ tailWord_1914353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914353).length < 2 ^ (prefixWord ++ tailWord_1914353).sum := by decide
  have hdescent : baseEnd_1914353 < baseStart_1914353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914370 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1914370 : Nat := 118140960795 + 1914370 * 2 ^ 59
def prefixEnd_1914370 : Nat := 4983230072969 + 3 ^ 40 * 1914370 * 2
def baseEnd_1914370 : Nat := 982991960547780252270979

theorem tailTrace_1914370 : CollatzResearch.WordTrace tailWord_1914370 prefixEnd_1914370 982991960547780252270979 := by
  unfold tailWord_1914370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455702518642978302855141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46548540049714608807613709 17455702518642978302855141)
  ·
    refine ⟨3272944222245558431785339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17455702518642978302855141 3272944222245558431785339)
    ·
      refine ⟨4909416333368337647678009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272944222245558431785339 4909416333368337647678009)
      ·
        refine ⟨3682062250026253235758507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4909416333368337647678009 3682062250026253235758507)
        ·
          refine ⟨5523093375039379853637761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682062250026253235758507 5523093375039379853637761)
          ·
            refine ⟨4142320031279534890228321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523093375039379853637761 4142320031279534890228321)
            ·
              refine ⟨3106740023459651167671241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142320031279534890228321 3106740023459651167671241)
              ·
                refine ⟨2330055017594738375753431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106740023459651167671241 2330055017594738375753431)
                ·
                  refine ⟨3495082526392107563630147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330055017594738375753431 3495082526392107563630147)
                  ·
                    refine ⟨5242623789588161345445221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495082526392107563630147 5242623789588161345445221)
                    ·
                      refine ⟨982991960547780252270979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5242623789588161345445221 982991960547780252270979)
                      ·
                        rfl

theorem cell23_1914370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1914370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914370 prefixEnd_1914370 := by exact prefixLift 1914370
  have htrace : WordTrace (prefixWord ++ tailWord_1914370) baseStart_1914370 baseEnd_1914370 := by
    simpa [prefixWord, tailWord_1914370, baseEnd_1914370] using wordTrace_append hprefix tailTrace_1914370
  have hstable : (prefixWord ++ tailWord_1914370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914370).length < 2 ^ (prefixWord ++ tailWord_1914370).sum := by decide
  have hdescent : baseEnd_1914370 < baseStart_1914370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914381 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1914381 : Nat := 118140960795 + 1914381 * 2 ^ 59
def prefixEnd_1914381 : Nat := 4983230072969 + 3 ^ 40 * 1914381 * 2
def baseEnd_1914381 : Nat := 982997608834979709233429

theorem tailTrace_1914381 : CollatzResearch.WordTrace tailWord_1914381 prefixEnd_1914381 982997608834979709233429 := by
  unfold tailWord_1914381
  simp only [CollatzResearch.WordTrace]
  refine ⟨69823211277532062090070997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46548807518354708060047331 69823211277532062090070997)
  ·
    refine ⟨1636481514317157705236039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69823211277532062090070997 1636481514317157705236039)
    ·
      refine ⟨2454722271475736557854059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636481514317157705236039 2454722271475736557854059)
      ·
        refine ⟨3682083407213604836781089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454722271475736557854059 3682083407213604836781089)
        ·
          refine ⟨2761562555410203627585817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682083407213604836781089 2761562555410203627585817)
          ·
            refine ⟨2071171916557652720689363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761562555410203627585817 2071171916557652720689363)
            ·
              refine ⟨3106757874836479081034045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071171916557652720689363 3106757874836479081034045)
              ·
                refine ⟨1165034203063679655387767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106757874836479081034045 1165034203063679655387767)
                ·
                  refine ⟨1747551304595519483081651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165034203063679655387767 1747551304595519483081651)
                  ·
                    refine ⟨2621326956893279224622477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747551304595519483081651 2621326956893279224622477)
                    ·
                      refine ⟨982997608834979709233429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621326956893279224622477 982997608834979709233429)
                      ·
                        rfl

theorem cell23_1914381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1914381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914381 prefixEnd_1914381 := by exact prefixLift 1914381
  have htrace : WordTrace (prefixWord ++ tailWord_1914381) baseStart_1914381 baseEnd_1914381 := by
    simpa [prefixWord, tailWord_1914381, baseEnd_1914381] using wordTrace_append hprefix tailTrace_1914381
  have hstable : (prefixWord ++ tailWord_1914381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914381).length < 2 ^ (prefixWord ++ tailWord_1914381).sum := by decide
  have hdescent : baseEnd_1914381 < baseStart_1914381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914387 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 1, 2, 2]
def baseStart_1914387 : Nat := 118140960795 + 1914387 * 2 ^ 59
def prefixEnd_1914387 : Nat := 4983230072969 + 3 ^ 40 * 1914387 * 2
def baseEnd_1914387 : Nat := 983000689718906685758401

theorem tailTrace_1914387 : CollatzResearch.WordTrace tailWord_1914387 prefixEnd_1914387 983000689718906685758401 := by
  unfold tailWord_1914387
  simp only [CollatzResearch.WordTrace]
  refine ⟨69823430115510325114789415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46548953410340216743192943 69823430115510325114789415)
  ·
    refine ⟨104735145173265487672184123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69823430115510325114789415 104735145173265487672184123)
    ·
      refine ⟨157102717759898231508276185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104735145173265487672184123 157102717759898231508276185)
      ·
        refine ⟨117827038319923673631207139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157102717759898231508276185 117827038319923673631207139)
        ·
          refine ⟨176740557479885510446810709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117827038319923673631207139 176740557479885510446810709)
          ·
            refine ⟨2071178407967408325548563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 176740557479885510446810709 2071178407967408325548563)
            ·
              refine ⟨3106767611951112488322845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071178407967408325548563 3106767611951112488322845)
              ·
                refine ⟨1165037854481667183121067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106767611951112488322845 1165037854481667183121067)
                ·
                  refine ⟨1747556781722500774681601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165037854481667183121067 1747556781722500774681601)
                  ·
                    refine ⟨1310667586291875581011201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747556781722500774681601 1310667586291875581011201)
                    ·
                      refine ⟨983000689718906685758401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310667586291875581011201 983000689718906685758401)
                      ·
                        rfl

theorem cell23_1914387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 2, 2].length) (baseStart_1914387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914387 prefixEnd_1914387 := by exact prefixLift 1914387
  have htrace : WordTrace (prefixWord ++ tailWord_1914387) baseStart_1914387 baseEnd_1914387 := by
    simpa [prefixWord, tailWord_1914387, baseEnd_1914387] using wordTrace_append hprefix tailTrace_1914387
  have hstable : (prefixWord ++ tailWord_1914387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914387).length < 2 ^ (prefixWord ++ tailWord_1914387).sum := by decide
  have hdescent : baseEnd_1914387 < baseStart_1914387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914398 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1914398 : Nat := 118140960795 + 1914398 * 2 ^ 59
def prefixEnd_1914398 : Nat := 4983230072969 + 3 ^ 40 * 1914398 * 2
def baseEnd_1914398 : Nat := 983006338006106142720851

theorem tailTrace_1914398 : CollatzResearch.WordTrace tailWord_1914398 prefixEnd_1914398 983006338006106142720851 := by
  unfold tailWord_1914398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727978914808809249179981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46549220878980315995626565 8727978914808809249179981)
  ·
    refine ⟨3272992093053303468442493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8727978914808809249179981 3272992093053303468442493)
    ·
      refine ⟨1227372034894988800665935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3272992093053303468442493 1227372034894988800665935)
      ·
        refine ⟨1841058052342483200998903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227372034894988800665935 1841058052342483200998903)
        ·
          refine ⟨2761587078513724801498355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841058052342483200998903 2761587078513724801498355)
          ·
            refine ⟨4142380617770587202247533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761587078513724801498355 4142380617770587202247533)
            ·
              refine ⟨1553392731663970200842825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4142380617770587202247533 1553392731663970200842825)
              ·
                refine ⟨1165044548747977650632119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553392731663970200842825 1165044548747977650632119)
                ·
                  refine ⟨1747566823121966475948179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165044548747977650632119 1747566823121966475948179)
                  ·
                    refine ⟨2621350234682949713922269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747566823121966475948179 2621350234682949713922269)
                    ·
                      refine ⟨983006338006106142720851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621350234682949713922269 983006338006106142720851)
                      ·
                        rfl

theorem cell23_1914398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1914398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914398 prefixEnd_1914398 := by exact prefixLift 1914398
  have htrace : WordTrace (prefixWord ++ tailWord_1914398) baseStart_1914398 baseEnd_1914398 := by
    simpa [prefixWord, tailWord_1914398, baseEnd_1914398] using wordTrace_append hprefix tailTrace_1914398
  have hstable : (prefixWord ++ tailWord_1914398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914398).length < 2 ^ (prefixWord ++ tailWord_1914398).sum := by decide
  have hdescent : baseEnd_1914398 < baseStart_1914398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914479 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 7]
def baseStart_1914479 : Nat := 118140960795 + 1914479 * 2 ^ 59
def prefixEnd_1914479 : Nat := 4983230072969 + 3 ^ 40 * 1914479 * 2
def baseEnd_1914479 : Nat := 327682643313040108602659

theorem tailTrace_1914479 : CollatzResearch.WordTrace tailWord_1914479 prefixEnd_1914479 327682643313040108602659 := by
  unfold tailWord_1914479
  simp only [CollatzResearch.WordTrace]
  refine ⟨69826785631177024827138491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46551190420784683218092327 69826785631177024827138491)
  ·
    refine ⟨104740178446765537240707737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69826785631177024827138491 104740178446765537240707737)
    ·
      refine ⟨78555133835074152930530803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104740178446765537240707737 78555133835074152930530803)
      ·
        refine ⟨117832700752611229395796205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78555133835074152930530803 117832700752611229395796205)
        ·
          refine ⟨44187262782229211023423577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117832700752611229395796205 44187262782229211023423577)
          ·
            refine ⟨33140447086671908267567683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44187262782229211023423577 33140447086671908267567683)
            ·
              refine ⟨49710670630007862401351525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33140447086671908267567683 49710670630007862401351525)
              ·
                refine ⟨9320750743126474200253411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49710670630007862401351525 9320750743126474200253411)
                ·
                  refine ⟨13981126114689711300380117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320750743126474200253411 13981126114689711300380117)
                  ·
                    refine ⟨327682643313040108602659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13981126114689711300380117 327682643313040108602659)
                    ·
                      rfl

theorem cell23_1914479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_1914479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914479 prefixEnd_1914479 := by exact prefixLift 1914479
  have htrace : WordTrace (prefixWord ++ tailWord_1914479) baseStart_1914479 baseEnd_1914479 := by
    simpa [prefixWord, tailWord_1914479, baseEnd_1914479] using wordTrace_append hprefix tailTrace_1914479
  have hstable : (prefixWord ++ tailWord_1914479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914479).length < 2 ^ (prefixWord ++ tailWord_1914479).sum := by decide
  have hdescent : baseEnd_1914479 < baseStart_1914479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914500 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 5]
def baseStart_1914500 : Nat := 118140960795 + 1914500 * 2 ^ 59
def prefixEnd_1914500 : Nat := 4983230072969 + 3 ^ 40 * 1914500 * 2
def baseEnd_1914500 : Nat := 109228745892540527071709

theorem tailTrace_1914500 : CollatzResearch.WordTrace tailWord_1914500 prefixEnd_1914500 109228745892540527071709 := by
  unfold tailWord_1914500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34913775782050472706826477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46551701042733963609101969 34913775782050472706826477)
  ·
    refine ⟨13092665918268927265059929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34913775782050472706826477 13092665918268927265059929)
    ·
      refine ⟨9819499438701695448794947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13092665918268927265059929 9819499438701695448794947)
      ·
        refine ⟨14729249158052543173192421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9819499438701695448794947 14729249158052543173192421)
        ·
          refine ⟨2761734217134851844973579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14729249158052543173192421 2761734217134851844973579)
          ·
            refine ⟨4142601325702277767460369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761734217134851844973579 4142601325702277767460369)
            ·
              refine ⟨3106950994276708325595277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142601325702277767460369 3106950994276708325595277)
              ·
                refine ⟨1165106622853765622098229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106950994276708325595277 1165106622853765622098229)
                ·
                  refine ⟨109228745892540527071709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165106622853765622098229 109228745892540527071709)
                  ·
                    rfl

theorem cell23_1914500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_1914500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914500 prefixEnd_1914500 := by exact prefixLift 1914500
  have htrace : WordTrace (prefixWord ++ tailWord_1914500) baseStart_1914500 baseEnd_1914500 := by
    simpa [prefixWord, tailWord_1914500, baseEnd_1914500] using wordTrace_append hprefix tailTrace_1914500
  have hstable : (prefixWord ++ tailWord_1914500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914500).length < 2 ^ (prefixWord ++ tailWord_1914500).sum := by decide
  have hdescent : baseEnd_1914500 < baseStart_1914500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914533 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_1914533 : Nat := 118140960795 + 1914533 * 2 ^ 59
def prefixEnd_1914533 : Nat := 4983230072969 + 3 ^ 40 * 1914533 * 2
def baseEnd_1914533 : Nat := 983075657894463114532729

theorem tailTrace_1914533 : CollatzResearch.WordTrace tailWord_1914533 prefixEnd_1914533 983075657894463114532729 := by
  unfold tailWord_1914533
  simp only [CollatzResearch.WordTrace]
  refine ⟨69828755172981392049604253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46552503448654261366402835 69828755172981392049604253)
  ·
    refine ⟨26185783189868022018601595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69828755172981392049604253 26185783189868022018601595)
    ·
      refine ⟨39278674784802033027902393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26185783189868022018601595 39278674784802033027902393)
      ·
        refine ⟨29459006088601524770926795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39278674784802033027902393 29459006088601524770926795)
        ·
          refine ⟨44188509132902287156390193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29459006088601524770926795 44188509132902287156390193)
          ·
            refine ⟨33141381849676715367292645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44188509132902287156390193 33141381849676715367292645)
            ·
              refine ⟨6214009096814384131367371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33141381849676715367292645 6214009096814384131367371)
              ·
                refine ⟨9321013645221576197051057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214009096814384131367371 9321013645221576197051057)
                ·
                  refine ⟨6990760233916182147788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9321013645221576197051057 6990760233916182147788293)
                  ·
                    refine ⟨1310767543859284152710305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990760233916182147788293 1310767543859284152710305)
                    ·
                      refine ⟨983075657894463114532729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310767543859284152710305 983075657894463114532729)
                      ·
                        rfl

theorem cell23_1914533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_1914533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914533 prefixEnd_1914533 := by exact prefixLift 1914533
  have htrace : WordTrace (prefixWord ++ tailWord_1914533) baseStart_1914533 baseEnd_1914533 := by
    simpa [prefixWord, tailWord_1914533, baseEnd_1914533] using wordTrace_append hprefix tailTrace_1914533
  have hstable : (prefixWord ++ tailWord_1914533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914533).length < 2 ^ (prefixWord ++ tailWord_1914533).sum := by decide
  have hdescent : baseEnd_1914533 < baseStart_1914533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914550 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1914550 : Nat := 118140960795 + 1914550 * 2 ^ 59
def prefixEnd_1914550 : Nat := 4983230072969 + 3 ^ 40 * 1914550 * 2
def baseEnd_1914550 : Nat := 983084387065589548020151

theorem tailTrace_1914550 : CollatzResearch.WordTrace tailWord_1914550 prefixEnd_1914550 983084387065589548020151 := by
  unfold tailWord_1914550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364335950869987747060819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46552916809279869301982069 4364335950869987747060819)
  ·
    refine ⟨6546503926304981620591229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364335950869987747060819 6546503926304981620591229)
    ·
      refine ⟨2454938972364368107721711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6546503926304981620591229 2454938972364368107721711)
      ·
        refine ⟨3682408458546552161582567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454938972364368107721711 3682408458546552161582567)
        ·
          refine ⟨5523612687819828242373851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682408458546552161582567 5523612687819828242373851)
          ·
            refine ⟨8285419031729742363560777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523612687819828242373851 8285419031729742363560777)
            ·
              refine ⟨6214064273797306772670583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285419031729742363560777 6214064273797306772670583)
              ·
                refine ⟨9321096410695960159005875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214064273797306772670583 9321096410695960159005875)
                ·
                  refine ⟨13981644616043940238508813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321096410695960159005875 13981644616043940238508813)
                  ·
                    refine ⟨5243116731016477589440805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13981644616043940238508813 5243116731016477589440805)
                    ·
                      refine ⟨983084387065589548020151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5243116731016477589440805 983084387065589548020151)
                      ·
                        rfl

theorem cell23_1914550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1914550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914550 prefixEnd_1914550 := by exact prefixLift 1914550
  have htrace : WordTrace (prefixWord ++ tailWord_1914550) baseStart_1914550 baseEnd_1914550 := by
    simpa [prefixWord, tailWord_1914550, baseEnd_1914550] using wordTrace_append hprefix tailTrace_1914550
  have hstable : (prefixWord ++ tailWord_1914550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914550).length < 2 ^ (prefixWord ++ tailWord_1914550).sum := by decide
  have hdescent : baseEnd_1914550 < baseStart_1914550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914556 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 8]
def baseStart_1914556 : Nat := 118140960795 + 1914556 * 2 ^ 59
def prefixEnd_1914556 : Nat := 4983230072969 + 3 ^ 40 * 1914556 * 2
def baseEnd_1914556 : Nat := 109231940883279613838347

theorem tailTrace_1914556 : CollatzResearch.WordTrace tailWord_1914556 prefixEnd_1914556 109231940883279613838347 := by
  unfold tailWord_1914556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34914797025949033488845761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46553062701265377985127681 34914797025949033488845761)
  ·
    refine ⟨26186097769461775116634321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34914797025949033488845761 26186097769461775116634321)
    ·
      refine ⟨19639573327096331337475741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26186097769461775116634321 19639573327096331337475741)
      ·
        refine ⟨7364839997661124251553403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19639573327096331337475741 7364839997661124251553403)
        ·
          refine ⟨11047259996491686377330105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364839997661124251553403 11047259996491686377330105)
          ·
            refine ⟨8285444997368764782997579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11047259996491686377330105 8285444997368764782997579)
            ·
              refine ⟨12428167496053147174496369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285444997368764782997579 12428167496053147174496369)
              ·
                refine ⟨9321125622039860380872277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12428167496053147174496369 9321125622039860380872277)
                ·
                  refine ⟨109231940883279613838347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9321125622039860380872277 109231940883279613838347)
                  ·
                    rfl

theorem cell23_1914556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_1914556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914556 prefixEnd_1914556 := by exact prefixLift 1914556
  have htrace : WordTrace (prefixWord ++ tailWord_1914556) baseStart_1914556 baseEnd_1914556 := by
    simpa [prefixWord, tailWord_1914556, baseEnd_1914556] using wordTrace_append hprefix tailTrace_1914556
  have hstable : (prefixWord ++ tailWord_1914556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914556).length < 2 ^ (prefixWord ++ tailWord_1914556).sum := by decide
  have hdescent : baseEnd_1914556 < baseStart_1914556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914570 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_1914570 : Nat := 118140960795 + 1914570 * 2 ^ 59
def prefixEnd_1914570 : Nat := 4983230072969 + 3 ^ 40 * 1914570 * 2
def baseEnd_1914570 : Nat := 983094656678679469770059

theorem tailTrace_1914570 : CollatzResearch.WordTrace tailWord_1914570 prefixEnd_1914570 983094656678679469770059 := by
  unfold tailWord_1914570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457526168461836842175291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46553403115898231579134109 17457526168461836842175291)
  ·
    refine ⟨26186289252692755263262937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17457526168461836842175291 26186289252692755263262937)
    ·
      refine ⟨19639716939519566447447203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26186289252692755263262937 19639716939519566447447203)
      ·
        refine ⟨29459575409279349671170805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639716939519566447447203 29459575409279349671170805)
        ·
          refine ⟨2761835194619939031672263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29459575409279349671170805 2761835194619939031672263)
          ·
            refine ⟨4142752791929908547508395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761835194619939031672263 4142752791929908547508395)
            ·
              refine ⟨6214129187894862821262593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142752791929908547508395 6214129187894862821262593)
              ·
                refine ⟨4660596890921147115946945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6214129187894862821262593 4660596890921147115946945)
                ·
                  refine ⟨3495447668190860336960209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4660596890921147115946945 3495447668190860336960209)
                  ·
                    refine ⟨2621585751143145252720157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495447668190860336960209 2621585751143145252720157)
                    ·
                      refine ⟨983094656678679469770059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621585751143145252720157 983094656678679469770059)
                      ·
                        rfl

theorem cell23_1914570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_1914570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914570 prefixEnd_1914570 := by exact prefixLift 1914570
  have htrace : WordTrace (prefixWord ++ tailWord_1914570) baseStart_1914570 baseEnd_1914570 := by
    simpa [prefixWord, tailWord_1914570, baseEnd_1914570] using wordTrace_append hprefix tailTrace_1914570
  have hstable : (prefixWord ++ tailWord_1914570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914570).length < 2 ^ (prefixWord ++ tailWord_1914570).sum := by decide
  have hdescent : baseEnd_1914570 < baseStart_1914570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914577 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 1, 4]
def baseStart_1914577 : Nat := 118140960795 + 1914577 * 2 ^ 59
def prefixEnd_1914577 : Nat := 4983230072969 + 3 ^ 40 * 1914577 * 2
def baseEnd_1914577 : Nat := 327699417014420314127509

theorem tailTrace_1914577 : CollatzResearch.WordTrace tailWord_1914577 prefixEnd_1914577 327699417014420314127509 := by
  unfold tailWord_1914577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69830359984821987564205985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46553573323214658376137323 69830359984821987564205985)
  ·
    refine ⟨52372769988616490673154489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69830359984821987564205985 52372769988616490673154489)
    ·
      refine ⟨39279577491462368004865867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52372769988616490673154489 39279577491462368004865867)
      ·
        refine ⟨58919366237193552007298801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39279577491462368004865867 58919366237193552007298801)
        ·
          refine ⟨44189524677895164005474101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58919366237193552007298801 44189524677895164005474101)
          ·
            refine ⟨4142767938552671625513197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44189524677895164005474101 4142767938552671625513197)
            ·
              refine ⟨1553537976957251859567449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4142767938552671625513197 1553537976957251859567449)
              ·
                refine ⟨1165153482717938894675587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553537976957251859567449 1165153482717938894675587)
                ·
                  refine ⟨1747730224076908342013381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165153482717938894675587 1747730224076908342013381)
                  ·
                    refine ⟨327699417014420314127509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747730224076908342013381 327699417014420314127509)
                    ·
                      rfl

theorem cell23_1914577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_1914577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914577 prefixEnd_1914577 := by exact prefixLift 1914577
  have htrace : WordTrace (prefixWord ++ tailWord_1914577) baseStart_1914577 baseEnd_1914577 := by
    simpa [prefixWord, tailWord_1914577, baseEnd_1914577] using wordTrace_append hprefix tailTrace_1914577
  have hstable : (prefixWord ++ tailWord_1914577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914577).length < 2 ^ (prefixWord ++ tailWord_1914577).sum := by decide
  have hdescent : baseEnd_1914577 < baseStart_1914577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914603 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 1, 5]
def baseStart_1914603 : Nat := 118140960795 + 1914603 * 2 ^ 59
def prefixEnd_1914603 : Nat := 4983230072969 + 3 ^ 40 * 1914603 * 2
def baseEnd_1914603 : Nat := 327703867180092613552469

theorem tailTrace_1914603 : CollatzResearch.WordTrace tailWord_1914603 prefixEnd_1914603 327703867180092613552469 := by
  unfold tailWord_1914603
  simp only [CollatzResearch.WordTrace]
  refine ⟨69831308282727794004652463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46554205521818529336434975 69831308282727794004652463)
  ·
    refine ⟨104746962424091691006978695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69831308282727794004652463 104746962424091691006978695)
    ·
      refine ⟨157120443636137536510468043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104746962424091691006978695 157120443636137536510468043)
      ·
        refine ⟨235680665454206304765702065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157120443636137536510468043 235680665454206304765702065)
        ·
          refine ⟨176760499090654728574276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235680665454206304765702065 176760499090654728574276549)
          ·
            refine ⟨33142593579497761607676853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176760499090654728574276549 33142593579497761607676853)
            ·
              refine ⟨3107118148077915150719705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33142593579497761607676853 3107118148077915150719705)
              ·
                refine ⟨2330338611058436363039779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107118148077915150719705 2330338611058436363039779)
                ·
                  refine ⟨3495507916587654544559669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330338611058436363039779 3495507916587654544559669)
                  ·
                    refine ⟨327703867180092613552469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3495507916587654544559669 327703867180092613552469)
                    ·
                      rfl

theorem cell23_1914603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 5].length) (baseStart_1914603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914603 prefixEnd_1914603 := by exact prefixLift 1914603
  have htrace : WordTrace (prefixWord ++ tailWord_1914603) baseStart_1914603 baseEnd_1914603 := by
    simpa [prefixWord, tailWord_1914603, baseEnd_1914603] using wordTrace_append hprefix tailTrace_1914603
  have hstable : (prefixWord ++ tailWord_1914603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914603).length < 2 ^ (prefixWord ++ tailWord_1914603).sum := by decide
  have hdescent : baseEnd_1914603 < baseStart_1914603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914620 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1914620 : Nat := 118140960795 + 1914620 * 2 ^ 59
def prefixEnd_1914620 : Nat := 4983230072969 + 3 ^ 40 * 1914620 * 2
def baseEnd_1914620 : Nat := 327706776903801424714943

theorem tailTrace_1914620 : CollatzResearch.WordTrace tailWord_1914620 prefixEnd_1914620 327706776903801424714943 := by
  unfold tailWord_1914620
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915964161833102954010657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46554618882444137272014209 34915964161833102954010657)
  ·
    refine ⟨26186973121374827215507993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34915964161833102954010657 26186973121374827215507993)
    ·
      refine ⟨19640229841031120411630995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26186973121374827215507993 19640229841031120411630995)
      ·
        refine ⟨29460344761546680617446493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19640229841031120411630995 29460344761546680617446493)
        ·
          refine ⟨11047629285580005231542435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29460344761546680617446493 11047629285580005231542435)
          ·
            refine ⟨16571443928370007847313653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047629285580005231542435 16571443928370007847313653)
            ·
              refine ⟨1553572868284688235685655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16571443928370007847313653 1553572868284688235685655)
              ·
                refine ⟨2330359302427032353528483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553572868284688235685655 2330359302427032353528483)
                ·
                  refine ⟨3495538953640548530292725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330359302427032353528483 3495538953640548530292725)
                  ·
                    refine ⟨327706776903801424714943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3495538953640548530292725 327706776903801424714943)
                    ·
                      rfl

theorem cell23_1914620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1914620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914620 prefixEnd_1914620 := by exact prefixLift 1914620
  have htrace : WordTrace (prefixWord ++ tailWord_1914620) baseStart_1914620 baseEnd_1914620 := by
    simpa [prefixWord, tailWord_1914620, baseEnd_1914620] using wordTrace_append hprefix tailTrace_1914620
  have hstable : (prefixWord ++ tailWord_1914620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914620).length < 2 ^ (prefixWord ++ tailWord_1914620).sum := by decide
  have hdescent : baseEnd_1914620 < baseStart_1914620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914623 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_1914623 : Nat := 118140960795 + 1914623 * 2 ^ 59
def prefixEnd_1914623 : Nat := 4983230072969 + 3 ^ 40 * 1914623 * 2
def baseEnd_1914623 : Nat := 983121871153367762407315

theorem tailTrace_1914623 : CollatzResearch.WordTrace tailWord_1914623 prefixEnd_1914623 983121871153367762407315 := by
  unfold tailWord_1914623
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832037742655337420380523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46554691828436891613587015 69832037742655337420380523)
  ·
    refine ⟨104748056613983006130570785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69832037742655337420380523 104748056613983006130570785)
    ·
      refine ⟨78561042460487254597928089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104748056613983006130570785 78561042460487254597928089)
      ·
        refine ⟨58920781845365440948446067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78561042460487254597928089 58920781845365440948446067)
        ·
          refine ⟨88381172768048161422669101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58920781845365440948446067 88381172768048161422669101)
          ·
            refine ⟨33142939788018060533500913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88381172768048161422669101 33142939788018060533500913)
            ·
              refine ⟨24857204841013545400125685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33142939788018060533500913 24857204841013545400125685)
              ·
                refine ⟨2330362953845019881261783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24857204841013545400125685 2330362953845019881261783)
                ·
                  refine ⟨3495544430767529821892675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330362953845019881261783 3495544430767529821892675)
                  ·
                    refine ⟨5243316646151294732839013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495544430767529821892675 5243316646151294732839013)
                    ·
                      refine ⟨983121871153367762407315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5243316646151294732839013 983121871153367762407315)
                      ·
                        rfl

theorem cell23_1914623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_1914623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914623 prefixEnd_1914623 := by exact prefixLift 1914623
  have htrace : WordTrace (prefixWord ++ tailWord_1914623) baseStart_1914623 baseEnd_1914623 := by
    simpa [prefixWord, tailWord_1914623, baseEnd_1914623] using wordTrace_append hprefix tailTrace_1914623
  have hstable : (prefixWord ++ tailWord_1914623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914623).length < 2 ^ (prefixWord ++ tailWord_1914623).sum := by decide
  have hdescent : baseEnd_1914623 < baseStart_1914623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914634 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1914634 : Nat := 118140960795 + 1914634 * 2 ^ 59
def prefixEnd_1914634 : Nat := 4983230072969 + 3 ^ 40 * 1914634 * 2
def baseEnd_1914634 : Nat := 983127519440567219369765

theorem tailTrace_1914634 : CollatzResearch.WordTrace tailWord_1914634 prefixEnd_1914634 983127519440567219369765 := by
  unfold tailWord_1914634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458109736403871574757739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46554959297076990866020637 17458109736403871574757739)
  ·
    refine ⟨26187164604605807362136609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458109736403871574757739 26187164604605807362136609)
    ·
      refine ⟨19640373453454355521602457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26187164604605807362136609 19640373453454355521602457)
      ·
        refine ⟨14730280090090766641201843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19640373453454355521602457 14730280090090766641201843)
        ·
          refine ⟨22095420135136149961802765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730280090090766641201843 22095420135136149961802765)
          ·
            refine ⟨8285782550676056235676037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22095420135136149961802765 8285782550676056235676037)
            ·
              refine ⟨1553584228251760544189257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8285782550676056235676037 1553584228251760544189257)
              ·
                refine ⟨1165188171188820408141943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553584228251760544189257 1165188171188820408141943)
                ·
                  refine ⟨1747782256783230612212915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165188171188820408141943 1747782256783230612212915)
                  ·
                    refine ⟨2621673385174845918319373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747782256783230612212915 2621673385174845918319373)
                    ·
                      refine ⟨983127519440567219369765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621673385174845918319373 983127519440567219369765)
                      ·
                        rfl

theorem cell23_1914634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1914634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914634 prefixEnd_1914634 := by exact prefixLift 1914634
  have htrace : WordTrace (prefixWord ++ tailWord_1914634) baseStart_1914634 baseEnd_1914634 := by
    simpa [prefixWord, tailWord_1914634, baseEnd_1914634] using wordTrace_append hprefix tailTrace_1914634
  have hstable : (prefixWord ++ tailWord_1914634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914634).length < 2 ^ (prefixWord ++ tailWord_1914634).sum := by decide
  have hdescent : baseEnd_1914634 < baseStart_1914634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914636 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1914636 : Nat := 118140960795 + 1914636 * 2 ^ 59
def prefixEnd_1914636 : Nat := 4983230072969 + 3 ^ 40 * 1914636 * 2
def baseEnd_1914636 : Nat := 983128546401876211544755

theorem tailTrace_1914636 : CollatzResearch.WordTrace tailWord_1914636 prefixEnd_1914636 983128546401876211544755 := by
  unfold tailWord_1914636
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916255945804120320301881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46555007927738827093735841 34916255945804120320301881)
  ·
    refine ⟨26187191959353090240226411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34916255945804120320301881 26187191959353090240226411)
    ·
      refine ⟨39280787939029635360339617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187191959353090240226411 39280787939029635360339617)
      ·
        refine ⟨29460590954272226520254713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39280787939029635360339617 29460590954272226520254713)
        ·
          refine ⟨22095443215704169890191035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29460590954272226520254713 22095443215704169890191035)
          ·
            refine ⟨33143164823556254835286553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22095443215704169890191035 33143164823556254835286553)
            ·
              refine ⟨24857373617667191126464915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33143164823556254835286553 24857373617667191126464915)
              ·
                refine ⟨37286060426500786689697373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24857373617667191126464915 37286060426500786689697373)
                ·
                  refine ⟨13982272659937795008636515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37286060426500786689697373 13982272659937795008636515)
                  ·
                    refine ⟨20973408989906692512954773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13982272659937795008636515 20973408989906692512954773)
                    ·
                      refine ⟨983128546401876211544755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20973408989906692512954773 983128546401876211544755)
                      ·
                        rfl

theorem cell23_1914636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1914636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914636 prefixEnd_1914636 := by exact prefixLift 1914636
  have htrace : WordTrace (prefixWord ++ tailWord_1914636) baseStart_1914636 baseEnd_1914636 := by
    simpa [prefixWord, tailWord_1914636, baseEnd_1914636] using wordTrace_append hprefix tailTrace_1914636
  have hstable : (prefixWord ++ tailWord_1914636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914636).length < 2 ^ (prefixWord ++ tailWord_1914636).sum := by decide
  have hdescent : baseEnd_1914636 < baseStart_1914636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914650 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1914650 : Nat := 118140960795 + 1914650 * 2 ^ 59
def prefixEnd_1914650 : Nat := 4983230072969 + 3 ^ 40 * 1914650 * 2
def baseEnd_1914650 : Nat := 327711911710346385589897

theorem tailTrace_1914650 : CollatzResearch.WordTrace tailWord_1914650 prefixEnd_1914650 327711911710346385589897 := by
  unfold tailWord_1914650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458255628389380257903351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46555348342371680687742269 17458255628389380257903351)
  ·
    refine ⟨26187383442584070386855027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458255628389380257903351 26187383442584070386855027)
    ·
      refine ⟨39281075163876105580282541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187383442584070386855027 39281075163876105580282541)
      ·
        refine ⟨14730403186453539592605953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39281075163876105580282541 14730403186453539592605953)
        ·
          refine ⟨11047802389840154694454465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14730403186453539592605953 11047802389840154694454465)
          ·
            refine ⟨8285851792380116020840849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11047802389840154694454465 8285851792380116020840849)
            ·
              refine ⟨6214388844285087015630637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285851792380116020840849 6214388844285087015630637)
              ·
                refine ⟨2330395816606907630861489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6214388844285087015630637 2330395816606907630861489)
                ·
                  refine ⟨1747796862455180723146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330395816606907630861489 1747796862455180723146117)
                  ·
                    refine ⟨327711911710346385589897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747796862455180723146117 327711911710346385589897)
                    ·
                      rfl

theorem cell23_1914650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1914650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914650 prefixEnd_1914650 := by exact prefixLift 1914650
  have htrace : WordTrace (prefixWord ++ tailWord_1914650) baseStart_1914650 baseEnd_1914650 := by
    simpa [prefixWord, tailWord_1914650, baseEnd_1914650] using wordTrace_append hprefix tailTrace_1914650
  have hstable : (prefixWord ++ tailWord_1914650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914650).length < 2 ^ (prefixWord ++ tailWord_1914650).sum := by decide
  have hdescent : baseEnd_1914650 < baseStart_1914650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914657 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1914657 : Nat := 118140960795 + 1914657 * 2 ^ 59
def prefixEnd_1914657 : Nat := 4983230072969 + 3 ^ 40 * 1914657 * 2
def baseEnd_1914657 : Nat := 983139329495620629382159

theorem tailTrace_1914657 : CollatzResearch.WordTrace tailWord_1914657 prefixEnd_1914657 983139329495620629382159 := by
  unfold tailWord_1914657
  simp only [CollatzResearch.WordTrace]
  refine ⟨69833277824532161227118225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46555518549688107484745483 69833277824532161227118225)
  ·
    refine ⟨52374958368399120920338669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69833277824532161227118225 52374958368399120920338669)
    ·
      refine ⟨19640609388149670345127001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52374958368399120920338669 19640609388149670345127001)
      ·
        refine ⟨14730457041112252758845251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19640609388149670345127001 14730457041112252758845251)
        ·
          refine ⟨22095685561668379138267877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730457041112252758845251 22095685561668379138267877)
          ·
            refine ⟨4142941042812821088425227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22095685561668379138267877 4142941042812821088425227)
            ·
              refine ⟨6214411564219231632637841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142941042812821088425227 6214411564219231632637841)
              ·
                refine ⟨4660808673164423724478381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6214411564219231632637841 4660808673164423724478381)
                ·
                  refine ⟨1747803252436658896679393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4660808673164423724478381 1747803252436658896679393)
                  ·
                    refine ⟨1310852439327494172509545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747803252436658896679393 1310852439327494172509545)
                    ·
                      refine ⟨983139329495620629382159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310852439327494172509545 983139329495620629382159)
                      ·
                        rfl

theorem cell23_1914657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1914657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914657 prefixEnd_1914657 := by exact prefixLift 1914657
  have htrace : WordTrace (prefixWord ++ tailWord_1914657) baseStart_1914657 baseEnd_1914657 := by
    simpa [prefixWord, tailWord_1914657, baseEnd_1914657] using wordTrace_append hprefix tailTrace_1914657
  have hstable : (prefixWord ++ tailWord_1914657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914657).length < 2 ^ (prefixWord ++ tailWord_1914657).sum := by decide
  have hdescent : baseEnd_1914657 < baseStart_1914657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914660 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1914660 : Nat := 118140960795 + 1914660 * 2 ^ 59
def prefixEnd_1914660 : Nat := 4983230072969 + 3 ^ 40 * 1914660 * 2
def baseEnd_1914660 : Nat := 983140869937584117644645

theorem tailTrace_1914660 : CollatzResearch.WordTrace tailWord_1914660 prefixEnd_1914660 983140869937584117644645 := by
  unfold tailWord_1914660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916693621760646369738717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46555591495680861826318289 34916693621760646369738717)
  ·
    refine ⟨13093760108160242388652019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34916693621760646369738717 13093760108160242388652019)
    ·
      refine ⟨19640640162240363582978029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093760108160242388652019 19640640162240363582978029)
      ·
        refine ⟨7365240060840136343616761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19640640162240363582978029 7365240060840136343616761)
        ·
          refine ⟨5523930045630102257712571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365240060840136343616761 5523930045630102257712571)
          ·
            refine ⟨8285895068445153386568857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523930045630102257712571 8285895068445153386568857)
            ·
              refine ⟨6214421301333865039926643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285895068445153386568857 6214421301333865039926643)
              ·
                refine ⟨9321631952000797559889965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214421301333865039926643 9321631952000797559889965)
                ·
                  refine ⟨3495611982000299084958737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9321631952000797559889965 3495611982000299084958737)
                  ·
                    refine ⟨2621708986500224313719053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495611982000299084958737 2621708986500224313719053)
                    ·
                      refine ⟨983140869937584117644645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621708986500224313719053 983140869937584117644645)
                      ·
                        rfl

theorem cell23_1914660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1914660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914660 prefixEnd_1914660 := by exact prefixLift 1914660
  have htrace : WordTrace (prefixWord ++ tailWord_1914660) baseStart_1914660 baseEnd_1914660 := by
    simpa [prefixWord, tailWord_1914660, baseEnd_1914660] using wordTrace_append hprefix tailTrace_1914660
  have hstable : (prefixWord ++ tailWord_1914660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914660).length < 2 ^ (prefixWord ++ tailWord_1914660).sum := by decide
  have hdescent : baseEnd_1914660 < baseStart_1914660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914674 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_1914674 : Nat := 118140960795 + 1914674 * 2 ^ 59
def prefixEnd_1914674 : Nat := 4983230072969 + 3 ^ 40 * 1914674 * 2
def baseEnd_1914674 : Nat := 983148058666747062869581

theorem tailTrace_1914674 : CollatzResearch.WordTrace tailWord_1914674 prefixEnd_1914674 983148058666747062869581 := by
  unfold tailWord_1914674
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458474466367643282621769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46555931910313715420324717 17458474466367643282621769)
  ·
    refine ⟨13093855849775732461966327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17458474466367643282621769 13093855849775732461966327)
    ·
      refine ⟨19640783774663598692949491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093855849775732461966327 19640783774663598692949491)
      ·
        refine ⟨29461175661995398039424237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19640783774663598692949491 29461175661995398039424237)
        ·
          refine ⟨11047940873248274264784089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29461175661995398039424237 11047940873248274264784089)
          ·
            refine ⟨8285955654936205698588067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11047940873248274264784089 8285955654936205698588067)
            ·
              refine ⟨12428933482404308547882101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285955654936205698588067 12428933482404308547882101)
              ·
                refine ⟨1165212513975403926363947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12428933482404308547882101 1165212513975403926363947)
                ·
                  refine ⟨1747818770963105889545921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165212513975403926363947 1747818770963105889545921)
                  ·
                    refine ⟨1310864078222329417159441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747818770963105889545921 1310864078222329417159441)
                    ·
                      refine ⟨983148058666747062869581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310864078222329417159441 983148058666747062869581)
                      ·
                        rfl

theorem cell23_1914674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_1914674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914674 prefixEnd_1914674 := by exact prefixLift 1914674
  have htrace : WordTrace (prefixWord ++ tailWord_1914674) baseStart_1914674 baseEnd_1914674 := by
    simpa [prefixWord, tailWord_1914674, baseEnd_1914674] using wordTrace_append hprefix tailTrace_1914674
  have hstable : (prefixWord ++ tailWord_1914674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914674).length < 2 ^ (prefixWord ++ tailWord_1914674).sum := by decide
  have hdescent : baseEnd_1914674 < baseStart_1914674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914677 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1914677 : Nat := 118140960795 + 1914677 * 2 ^ 59
def prefixEnd_1914677 : Nat := 4983230072969 + 3 ^ 40 * 1914677 * 2
def baseEnd_1914677 : Nat := 983149599108710551132067

theorem tailTrace_1914677 : CollatzResearch.WordTrace tailWord_1914677 prefixEnd_1914677 983149599108710551132067 := by
  unfold tailWord_1914677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69834007284459704642846285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46556004856306469761897523 69834007284459704642846285)
  ·
    refine ⟨26187752731672389241067357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69834007284459704642846285 26187752731672389241067357)
    ·
      refine ⟨9820407274377145965400259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26187752731672389241067357 9820407274377145965400259)
      ·
        refine ⟨14730610911565718948100389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9820407274377145965400259 14730610911565718948100389)
        ·
          refine ⟨2761989545918572302768823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14730610911565718948100389 2761989545918572302768823)
          ·
            refine ⟨4142984318877858454153235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761989545918572302768823 4142984318877858454153235)
            ·
              refine ⟨6214476478316787681229853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142984318877858454153235 6214476478316787681229853)
              ·
                refine ⟨2330428679368795380461195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6214476478316787681229853 2330428679368795380461195)
                ·
                  refine ⟨3495643019053193070691793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330428679368795380461195 3495643019053193070691793)
                  ·
                    refine ⟨2621732264289894803018845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495643019053193070691793 2621732264289894803018845)
                    ·
                      refine ⟨983149599108710551132067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621732264289894803018845 983149599108710551132067)
                      ·
                        rfl

theorem cell23_1914677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1914677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914677 prefixEnd_1914677 := by exact prefixLift 1914677
  have htrace : WordTrace (prefixWord ++ tailWord_1914677) baseStart_1914677 baseEnd_1914677 := by
    simpa [prefixWord, tailWord_1914677, baseEnd_1914677] using wordTrace_append hprefix tailTrace_1914677
  have hstable : (prefixWord ++ tailWord_1914677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914677).length < 2 ^ (prefixWord ++ tailWord_1914677).sum := by decide
  have hdescent : baseEnd_1914677 < baseStart_1914677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914733 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1914733 : Nat := 118140960795 + 1914733 * 2 ^ 59
def prefixEnd_1914733 : Nat := 4983230072969 + 3 ^ 40 * 1914733 * 2
def baseEnd_1914733 : Nat := 983178354025362332031809

theorem tailTrace_1914733 : CollatzResearch.WordTrace tailWord_1914733 prefixEnd_1914733 983178354025362332031809 := by
  unfold tailWord_1914733
  simp only [CollatzResearch.WordTrace]
  refine ⟨69836049772256826206884853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46557366514837884137923235 69836049772256826206884853)
  ·
    refine ⟨6547129666149077456895455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69836049772256826206884853 6547129666149077456895455)
    ·
      refine ⟨9820694499223616185343183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547129666149077456895455 9820694499223616185343183)
      ·
        refine ⟨14731041748835424278014775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9820694499223616185343183 14731041748835424278014775)
        ·
          refine ⟨22096562623253136417022163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14731041748835424278014775 22096562623253136417022163)
          ·
            refine ⟨33144843934879704625533245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22096562623253136417022163 33144843934879704625533245)
            ·
              refine ⟨12429316475579889234574967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33144843934879704625533245 12429316475579889234574967)
              ·
                refine ⟨18643974713369833851862451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429316475579889234574967 18643974713369833851862451)
                ·
                  refine ⟨27965962070054750777793677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18643974713369833851862451 27965962070054750777793677)
                  ·
                    refine ⟨10487235776270531541672629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27965962070054750777793677 10487235776270531541672629)
                    ·
                      refine ⟨983178354025362332031809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10487235776270531541672629 983178354025362332031809)
                      ·
                        rfl

theorem cell23_1914733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1914733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914733 prefixEnd_1914733 := by exact prefixLift 1914733
  have htrace : WordTrace (prefixWord ++ tailWord_1914733) baseStart_1914733 baseEnd_1914733 := by
    simpa [prefixWord, tailWord_1914733, baseEnd_1914733] using wordTrace_append hprefix tailTrace_1914733
  have hstable : (prefixWord ++ tailWord_1914733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914733).length < 2 ^ (prefixWord ++ tailWord_1914733).sum := by decide
  have hdescent : baseEnd_1914733 < baseStart_1914733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914734 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1914734 : Nat := 118140960795 + 1914734 * 2 ^ 59
def prefixEnd_1914734 : Nat := 4983230072969 + 3 ^ 40 * 1914734 * 2
def baseEnd_1914734 : Nat := 983178867506016828119305

theorem tailTrace_1914734 : CollatzResearch.WordTrace tailWord_1914734 prefixEnd_1914734 983178867506016828119305 := by
  unfold tailWord_1914734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729510780656650422208907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46557390830168802251780837 8729510780656650422208907)
  ·
    refine ⟨13094266170984975633313361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729510780656650422208907 13094266170984975633313361)
    ·
      refine ⟨9820699628238731724985021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13094266170984975633313361 9820699628238731724985021)
      ·
        refine ⟨3682762360589524396869383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9820699628238731724985021 3682762360589524396869383)
        ·
          refine ⟨5524143540884286595304075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682762360589524396869383 5524143540884286595304075)
          ·
            refine ⟨8286215311326429892956113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524143540884286595304075 8286215311326429892956113)
            ·
              refine ⟨6214661483494822419717085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286215311326429892956113 6214661483494822419717085)
              ·
                refine ⟨2330498056310558407393907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6214661483494822419717085 2330498056310558407393907)
                ·
                  refine ⟨3495747084465837611090861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330498056310558407393907 3495747084465837611090861)
                  ·
                    refine ⟨1310905156674689104159073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495747084465837611090861 1310905156674689104159073)
                    ·
                      refine ⟨983178867506016828119305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310905156674689104159073 983178867506016828119305)
                      ·
                        rfl

theorem cell23_1914734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1914734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914734 prefixEnd_1914734 := by exact prefixLift 1914734
  have htrace : WordTrace (prefixWord ++ tailWord_1914734) baseStart_1914734 baseEnd_1914734 := by
    simpa [prefixWord, tailWord_1914734, baseEnd_1914734] using wordTrace_append hprefix tailTrace_1914734
  have hstable : (prefixWord ++ tailWord_1914734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914734).length < 2 ^ (prefixWord ++ tailWord_1914734).sum := by decide
  have hdescent : baseEnd_1914734 < baseStart_1914734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914747 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 2, 2, 2]
def baseStart_1914747 : Nat := 118140960795 + 1914747 * 2 ^ 59
def prefixEnd_1914747 : Nat := 4983230072969 + 3 ^ 40 * 1914747 * 2
def baseEnd_1914747 : Nat := 983185542754525277256745

theorem tailTrace_1914747 : CollatzResearch.WordTrace tailWord_1914747 prefixEnd_1914747 983185542754525277256745 := by
  unfold tailWord_1914747
  simp only [CollatzResearch.WordTrace]
  refine ⟨69836560394206106597894495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46557706929470737731929663 69836560394206106597894495)
  ·
    refine ⟨104754840591309159896841743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69836560394206106597894495 104754840591309159896841743)
    ·
      refine ⟨157132260886963739845262615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104754840591309159896841743 157132260886963739845262615)
      ·
        refine ⟨235698391330445609767893923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157132260886963739845262615 235698391330445609767893923)
        ·
          refine ⟨353547586995668414651840885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235698391330445609767893923 353547586995668414651840885)
          ·
            refine ⟨33145086280843913873610083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353547586995668414651840885 33145086280843913873610083)
            ·
              refine ⟨49717629421265870810415125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33145086280843913873610083 49717629421265870810415125)
              ·
                refine ⟨2330513879121837694238209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49717629421265870810415125 2330513879121837694238209)
                ·
                  refine ⟨1747885409341378270678657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330513879121837694238209 1747885409341378270678657)
                  ·
                    refine ⟨1310914057006033703008993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747885409341378270678657 1310914057006033703008993)
                    ·
                      refine ⟨983185542754525277256745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1310914057006033703008993 983185542754525277256745)
                      ·
                        rfl

theorem cell23_1914747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2, 2].length) (baseStart_1914747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914747 prefixEnd_1914747 := by exact prefixLift 1914747
  have htrace : WordTrace (prefixWord ++ tailWord_1914747) baseStart_1914747 baseEnd_1914747 := by
    simpa [prefixWord, tailWord_1914747, baseEnd_1914747] using wordTrace_append hprefix tailTrace_1914747
  have hstable : (prefixWord ++ tailWord_1914747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914747).length < 2 ^ (prefixWord ++ tailWord_1914747).sum := by decide
  have hdescent : baseEnd_1914747 < baseStart_1914747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914763 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3]
def baseStart_1914763 : Nat := 118140960795 + 1914763 * 2 ^ 59
def prefixEnd_1914763 : Nat := 4983230072969 + 3 ^ 40 * 1914763 * 2
def baseEnd_1914763 : Nat := 983193758444997214656671

theorem tailTrace_1914763 : CollatzResearch.WordTrace tailWord_1914763 prefixEnd_1914763 983193758444997214656671 := by
  unfold tailWord_1914763
  simp only [CollatzResearch.WordTrace]
  refine ⟨69837143962148141330476943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46558095974765427553651295 69837143962148141330476943)
  ·
    refine ⟨104755715943222211995715415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69837143962148141330476943 104755715943222211995715415)
    ·
      refine ⟨157133573914833317993573123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104755715943222211995715415 157133573914833317993573123)
      ·
        refine ⟨235700360872249976990359685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157133573914833317993573123 235700360872249976990359685)
        ·
          refine ⟨44193817663546870685692441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235700360872249976990359685 44193817663546870685692441)
          ·
            refine ⟨33145363247660153014269331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44193817663546870685692441 33145363247660153014269331)
            ·
              refine ⟨49718044871490229521403997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33145363247660153014269331 49718044871490229521403997)
              ·
                refine ⟨18644266826808836070526499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49718044871490229521403997 18644266826808836070526499)
                ·
                  refine ⟨27966400240213254105789749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18644266826808836070526499 27966400240213254105789749)
                  ·
                    refine ⟨2621850022519992572417789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27966400240213254105789749 2621850022519992572417789)
                    ·
                      refine ⟨983193758444997214656671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621850022519992572417789 983193758444997214656671)
                      ·
                        rfl

theorem cell23_1914763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].length) (baseStart_1914763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914763 prefixEnd_1914763 := by exact prefixLift 1914763
  have htrace : WordTrace (prefixWord ++ tailWord_1914763) baseStart_1914763 baseEnd_1914763 := by
    simpa [prefixWord, tailWord_1914763, baseEnd_1914763] using wordTrace_append hprefix tailTrace_1914763
  have hstable : (prefixWord ++ tailWord_1914763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914763).length < 2 ^ (prefixWord ++ tailWord_1914763).sum := by decide
  have hdescent : baseEnd_1914763 < baseStart_1914763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914833 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1914833 : Nat := 118140960795 + 1914833 * 2 ^ 59
def prefixEnd_1914833 : Nat := 4983230072969 + 3 ^ 40 * 1914833 * 2
def baseEnd_1914833 : Nat := 983229702090811940781349

theorem tailTrace_1914833 : CollatzResearch.WordTrace tailWord_1914833 prefixEnd_1914833 983229702090811940781349 := by
  unfold tailWord_1914833
  simp only [CollatzResearch.WordTrace]
  refine ⟨69839697071894543285525153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46559798047929695523683435 69839697071894543285525153)
  ·
    refine ⟨52379772803920907464143865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69839697071894543285525153 52379772803920907464143865)
    ·
      refine ⟨39284829602940680598107899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52379772803920907464143865 39284829602940680598107899)
      ·
        refine ⟨58927244404411020897161849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39284829602940680598107899 58927244404411020897161849)
        ·
          refine ⟨44195433303308265672871387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58927244404411020897161849 44195433303308265672871387)
          ·
            refine ⟨66293149954962398509307081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44195433303308265672871387 66293149954962398509307081)
            ·
              refine ⟨49719862466221798881980311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66293149954962398509307081 49719862466221798881980311)
              ·
                refine ⟨74579793699332698322970467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49719862466221798881980311 74579793699332698322970467)
                ·
                  refine ⟨111869690548999047484455701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74579793699332698322970467 111869690548999047484455701)
                  ·
                    refine ⟨5243891744484330350833861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111869690548999047484455701 5243891744484330350833861)
                    ·
                      refine ⟨983229702090811940781349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5243891744484330350833861 983229702090811940781349)
                      ·
                        rfl

theorem cell23_1914833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1914833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914833 prefixEnd_1914833 := by exact prefixLift 1914833
  have htrace : WordTrace (prefixWord ++ tailWord_1914833) baseStart_1914833 baseEnd_1914833 := by
    simpa [prefixWord, tailWord_1914833, baseEnd_1914833] using wordTrace_append hprefix tailTrace_1914833
  have hstable : (prefixWord ++ tailWord_1914833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914833).length < 2 ^ (prefixWord ++ tailWord_1914833).sum := by decide
  have hdescent : baseEnd_1914833 < baseStart_1914833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914834 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1914834 : Nat := 118140960795 + 1914834 * 2 ^ 59
def prefixEnd_1914834 : Nat := 4983230072969 + 3 ^ 40 * 1914834 * 2
def baseEnd_1914834 : Nat := 327743405190488812289615

theorem tailTrace_1914834 : CollatzResearch.WordTrace tailWord_1914834 prefixEnd_1914834 327743405190488812289615 := by
  unfold tailWord_1914834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459933386222730114077889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46559822363260613637541037 17459933386222730114077889)
  ·
    refine ⟨13094950039667047585558417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17459933386222730114077889 13094950039667047585558417)
    ·
      refine ⟨9821212529750285689168813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13094950039667047585558417 9821212529750285689168813)
      ·
        refine ⟨3682954698656357133438305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9821212529750285689168813 3682954698656357133438305)
        ·
          refine ⟨2762216023992267850078729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682954698656357133438305 2762216023992267850078729)
          ·
            refine ⟨2071662017994200887559047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762216023992267850078729 2071662017994200887559047)
            ·
              refine ⟨3107493026991301331338571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071662017994200887559047 3107493026991301331338571)
              ·
                refine ⟨4661239540486951997007857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107493026991301331338571 4661239540486951997007857)
                ·
                  refine ⟨3495929655365213997755893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661239540486951997007857 3495929655365213997755893)
                  ·
                    refine ⟨327743405190488812289615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3495929655365213997755893 327743405190488812289615)
                    ·
                      rfl

theorem cell23_1914834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1914834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914834 prefixEnd_1914834 := by exact prefixLift 1914834
  have htrace : WordTrace (prefixWord ++ tailWord_1914834) baseStart_1914834 baseEnd_1914834 := by
    simpa [prefixWord, tailWord_1914834, baseEnd_1914834] using wordTrace_append hprefix tailTrace_1914834
  have hstable : (prefixWord ++ tailWord_1914834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914834).length < 2 ^ (prefixWord ++ tailWord_1914834).sum := by decide
  have hdescent : baseEnd_1914834 < baseStart_1914834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914837 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1914837 : Nat := 118140960795 + 1914837 * 2 ^ 59
def prefixEnd_1914837 : Nat := 4983230072969 + 3 ^ 40 * 1914837 * 2
def baseEnd_1914837 : Nat := 983231756013429925131331

theorem tailTrace_1914837 : CollatzResearch.WordTrace tailWord_1914837 prefixEnd_1914837 983231756013429925131331 := by
  unfold tailWord_1914837
  simp only [CollatzResearch.WordTrace]
  refine ⟨69839842963880051968670765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46559895309253367979113843 69839842963880051968670765)
  ·
    refine ⟨26189941111455019488251537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69839842963880051968670765 26189941111455019488251537)
    ·
      refine ⟨19642455833591264616188653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26189941111455019488251537 19642455833591264616188653)
      ·
        refine ⟨7365920937596724231070745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19642455833591264616188653 7365920937596724231070745)
        ·
          refine ⟨5524440703197543173303059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365920937596724231070745 5524440703197543173303059)
          ·
            refine ⟨8286661054796314759954589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524440703197543173303059 8286661054796314759954589)
            ·
              refine ⟨3107497895548618034982971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8286661054796314759954589 3107497895548618034982971)
              ·
                refine ⟨4661246843322927052474457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107497895548618034982971 4661246843322927052474457)
                ·
                  refine ⟨3495935132492195289355843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661246843322927052474457 3495935132492195289355843)
                  ·
                    refine ⟨5243902698738292934033765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3495935132492195289355843 5243902698738292934033765)
                    ·
                      refine ⟨983231756013429925131331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5243902698738292934033765 983231756013429925131331)
                      ·
                        rfl

theorem cell23_1914837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1914837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914837 prefixEnd_1914837 := by exact prefixLift 1914837
  have htrace : WordTrace (prefixWord ++ tailWord_1914837) baseStart_1914837 baseEnd_1914837 := by
    simpa [prefixWord, tailWord_1914837, baseEnd_1914837] using wordTrace_append hprefix tailTrace_1914837
  have hstable : (prefixWord ++ tailWord_1914837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914837).length < 2 ^ (prefixWord ++ tailWord_1914837).sum := by decide
  have hdescent : baseEnd_1914837 < baseStart_1914837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914840 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1914840 : Nat := 118140960795 + 1914840 * 2 ^ 59
def prefixEnd_1914840 : Nat := 4983230072969 + 3 ^ 40 * 1914840 * 2
def baseEnd_1914840 : Nat := 983233296455393413393817

theorem tailTrace_1914840 : CollatzResearch.WordTrace tailWord_1914840 prefixEnd_1914840 983233296455393413393817 := by
  unfold tailWord_1914840
  simp only [CollatzResearch.WordTrace]
  refine ⟨34919976191434591740514987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46559968255246122320686649 34919976191434591740514987)
  ·
    refine ⟨52379964287151887610772481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34919976191434591740514987 52379964287151887610772481)
    ·
      refine ⟨39284973215363915708079361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52379964287151887610772481 39284973215363915708079361)
      ·
        refine ⟨29463729911522936781059521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39284973215363915708079361 29463729911522936781059521)
        ·
          refine ⟨22097797433642202585794641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29463729911522936781059521 22097797433642202585794641)
          ·
            refine ⟨16573348075231651939345981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22097797433642202585794641 16573348075231651939345981)
            ·
              refine ⟨6215005528211869477254743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16573348075231651939345981 6215005528211869477254743)
              ·
                refine ⟨9322508292317804215882115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215005528211869477254743 9322508292317804215882115)
                ·
                  refine ⟨13983762438476706323823173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322508292317804215882115 13983762438476706323823173)
                  ·
                    refine ⟨2621955457214382435716845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13983762438476706323823173 2621955457214382435716845)
                    ·
                      refine ⟨983233296455393413393817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2621955457214382435716845 983233296455393413393817)
                      ·
                        rfl

theorem cell23_1914840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1914840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914840 prefixEnd_1914840 := by exact prefixLift 1914840
  have htrace : WordTrace (prefixWord ++ tailWord_1914840) baseStart_1914840 baseEnd_1914840 := by
    simpa [prefixWord, tailWord_1914840, baseEnd_1914840] using wordTrace_append hprefix tailTrace_1914840
  have hstable : (prefixWord ++ tailWord_1914840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914840).length < 2 ^ (prefixWord ++ tailWord_1914840).sum := by decide
  have hdescent : baseEnd_1914840 < baseStart_1914840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914863 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1914863 : Nat := 118140960795 + 1914863 * 2 ^ 59
def prefixEnd_1914863 : Nat := 4983230072969 + 3 ^ 40 * 1914863 * 2
def baseEnd_1914863 : Nat := 983245106510446823406211

theorem tailTrace_1914863 : CollatzResearch.WordTrace tailWord_1914863 prefixEnd_1914863 983245106510446823406211 := by
  unfold tailWord_1914863
  simp only [CollatzResearch.WordTrace]
  refine ⟨69840791261785858409117243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46560527507857238939411495 69840791261785858409117243)
  ·
    refine ⟨104761186892678787613675865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69840791261785858409117243 104761186892678787613675865)
    ·
      refine ⟨78570890169509090710256899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104761186892678787613675865 78570890169509090710256899)
      ·
        refine ⟨117856335254263636065385349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78570890169509090710256899 117856335254263636065385349)
        ·
          refine ⟨22098062860174431762259753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117856335254263636065385349 22098062860174431762259753)
          ·
            refine ⟨16573547145130823821694815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22098062860174431762259753 16573547145130823821694815)
            ·
              refine ⟨24860320717696235732542223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16573547145130823821694815 24860320717696235732542223)
              ·
                refine ⟨37290481076544353598813335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24860320717696235732542223 37290481076544353598813335)
                ·
                  refine ⟨55935721614816530398220003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37290481076544353598813335 55935721614816530398220003)
                  ·
                    refine ⟨83903582422224795597330005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55935721614816530398220003 83903582422224795597330005)
                    ·
                      refine ⟨983245106510446823406211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 83903582422224795597330005 983245106510446823406211)
                      ·
                        rfl

theorem cell23_1914863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1914863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914863 prefixEnd_1914863 := by exact prefixLift 1914863
  have htrace : WordTrace (prefixWord ++ tailWord_1914863) baseStart_1914863 baseEnd_1914863 := by
    simpa [prefixWord, tailWord_1914863, baseEnd_1914863] using wordTrace_append hprefix tailTrace_1914863
  have hstable : (prefixWord ++ tailWord_1914863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914863).length < 2 ^ (prefixWord ++ tailWord_1914863).sum := by decide
  have hdescent : baseEnd_1914863 < baseStart_1914863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914883 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1914883 : Nat := 118140960795 + 1914883 * 2 ^ 59
def prefixEnd_1914883 : Nat := 4983230072969 + 3 ^ 40 * 1914883 * 2
def baseEnd_1914883 : Nat := 983255376123536745156119

theorem tailTrace_1914883 : CollatzResearch.WordTrace tailWord_1914883 prefixEnd_1914883 983255376123536745156119 := by
  unfold tailWord_1914883
  simp only [CollatzResearch.WordTrace]
  refine ⟨69841520721713401824845303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46561013814475601216563535 69841520721713401824845303)
  ·
    refine ⟨104762281082570102737267955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69841520721713401824845303 104762281082570102737267955)
    ·
      refine ⟨157143421623855154105901933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104762281082570102737267955 157143421623855154105901933)
      ·
        refine ⟨58928783108945682789713225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157143421623855154105901933 58928783108945682789713225)
        ·
          refine ⟨44196587331709262092284919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58928783108945682789713225 44196587331709262092284919)
          ·
            refine ⟨66294880997563893138427379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44196587331709262092284919 66294880997563893138427379)
            ·
              refine ⟨99442321496345839707641069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66294880997563893138427379 99442321496345839707641069)
              ·
                refine ⟨37290870561129689890365401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99442321496345839707641069 37290870561129689890365401)
                ·
                  refine ⟨27968152920847267417774051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37290870561129689890365401 27968152920847267417774051)
                  ·
                    refine ⟨41952229381270901126661077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27968152920847267417774051 41952229381270901126661077)
                    ·
                      refine ⟨983255376123536745156119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41952229381270901126661077 983255376123536745156119)
                      ·
                        rfl

theorem cell23_1914883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1914883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914883 prefixEnd_1914883 := by exact prefixLift 1914883
  have htrace : WordTrace (prefixWord ++ tailWord_1914883) baseStart_1914883 baseEnd_1914883 := by
    simpa [prefixWord, tailWord_1914883, baseEnd_1914883] using wordTrace_append hprefix tailTrace_1914883
  have hstable : (prefixWord ++ tailWord_1914883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914883).length < 2 ^ (prefixWord ++ tailWord_1914883).sum := by decide
  have hdescent : baseEnd_1914883 < baseStart_1914883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914914 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_1914914 : Nat := 118140960795 + 1914914 * 2 ^ 59
def prefixEnd_1914914 : Nat := 4983230072969 + 3 ^ 40 * 1914914 * 2
def baseEnd_1914914 : Nat := 983271294023826123868477

theorem tailTrace_1914914 : CollatzResearch.WordTrace tailWord_1914914 prefixEnd_1914914 983271294023826123868477 := by
  unfold tailWord_1914914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17460662846150273529805949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46561767589734062746149197 17460662846150273529805949)
  ·
    refine ⟨6547748567306352573677231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17460662846150273529805949 6547748567306352573677231)
    ·
      refine ⟨9821622850959528860515847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547748567306352573677231 9821622850959528860515847)
      ·
        refine ⟨14732434276439293290773771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821622850959528860515847 14732434276439293290773771)
        ·
          refine ⟨22098651414658939936160657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732434276439293290773771 22098651414658939936160657)
          ·
            refine ⟨16573988560994204952120493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22098651414658939936160657 16573988560994204952120493)
            ·
              refine ⟨6215245710372826857045185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16573988560994204952120493 6215245710372826857045185)
              ·
                refine ⟨4661434282779620142783889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215245710372826857045185 4661434282779620142783889)
                ·
                  refine ⟨3496075712084715107087917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661434282779620142783889 3496075712084715107087917)
                  ·
                    refine ⟨1311028392031768165157969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496075712084715107087917 1311028392031768165157969)
                    ·
                      refine ⟨983271294023826123868477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311028392031768165157969 983271294023826123868477)
                      ·
                        rfl

theorem cell23_1914914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_1914914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914914 prefixEnd_1914914 := by exact prefixLift 1914914
  have htrace : WordTrace (prefixWord ++ tailWord_1914914) baseStart_1914914 baseEnd_1914914 := by
    simpa [prefixWord, tailWord_1914914, baseEnd_1914914] using wordTrace_append hprefix tailTrace_1914914
  have hstable : (prefixWord ++ tailWord_1914914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914914).length < 2 ^ (prefixWord ++ tailWord_1914914).sum := by decide
  have hdescent : baseEnd_1914914 < baseStart_1914914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914940 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1914940 : Nat := 118140960795 + 1914940 * 2 ^ 59
def prefixEnd_1914940 : Nat := 4983230072969 + 3 ^ 40 * 1914940 * 2
def baseEnd_1914940 : Nat := 983284644520843022143357

theorem tailTrace_1914940 : CollatzResearch.WordTrace tailWord_1914940 prefixEnd_1914940 983284644520843022143357 := by
  unfold tailWord_1914940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921799841253450279835137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46562399788337933706446849 34921799841253450279835137)
  ·
    refine ⟨26191349880940087709876353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34921799841253450279835137 26191349880940087709876353)
    ·
      refine ⟨19643512410705065782407265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26191349880940087709876353 19643512410705065782407265)
      ·
        refine ⟨14732634308028799336805449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19643512410705065782407265 14732634308028799336805449)
        ·
          refine ⟨11049475731021599502604087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732634308028799336805449 11049475731021599502604087)
          ·
            refine ⟨16574213596532399253906131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049475731021599502604087 16574213596532399253906131)
            ·
              refine ⟨24861320394798598880859197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16574213596532399253906131 24861320394798598880859197)
              ·
                refine ⟨9322995148049474580322199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24861320394798598880859197 9322995148049474580322199)
                ·
                  refine ⟨13984492722074211870483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322995148049474580322199 13984492722074211870483299)
                  ·
                    refine ⟨20976739083111317805724949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13984492722074211870483299 20976739083111317805724949)
                    ·
                      refine ⟨983284644520843022143357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20976739083111317805724949 983284644520843022143357)
                      ·
                        rfl

theorem cell23_1914940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1914940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914940 prefixEnd_1914940 := by exact prefixLift 1914940
  have htrace : WordTrace (prefixWord ++ tailWord_1914940) baseStart_1914940 baseEnd_1914940 := by
    simpa [prefixWord, tailWord_1914940, baseEnd_1914940] using wordTrace_append hprefix tailTrace_1914940
  have hstable : (prefixWord ++ tailWord_1914940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914940).length < 2 ^ (prefixWord ++ tailWord_1914940).sum := by decide
  have hdescent : baseEnd_1914940 < baseStart_1914940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914944 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_1914944 : Nat := 118140960795 + 1914944 * 2 ^ 59
def prefixEnd_1914944 : Nat := 4983230072969 + 3 ^ 40 * 1914944 * 2
def baseEnd_1914944 : Nat := 983286698443461006493339

theorem tailTrace_1914944 : CollatzResearch.WordTrace tailWord_1914944 prefixEnd_1914944 983286698443461006493339 := by
  unfold tailWord_1914944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921872787246204621407943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46562497049661606161877257 34921872787246204621407943)
  ·
    refine ⟨52382809180869306932111915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34921872787246204621407943 52382809180869306932111915)
    ·
      refine ⟨78574213771303960398167873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52382809180869306932111915 78574213771303960398167873)
      ·
        refine ⟨58930660328477970298625905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78574213771303960398167873 58930660328477970298625905)
        ·
          refine ⟨44197995246358477723969429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58930660328477970298625905 44197995246358477723969429)
          ·
            refine ⟨2071781027173053643311067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44197995246358477723969429 2071781027173053643311067)
            ·
              refine ⟨3107671540759580464966601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071781027173053643311067 3107671540759580464966601)
              ·
                refine ⟨2330753655569685348724951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107671540759580464966601 2330753655569685348724951)
                ·
                  refine ⟨3496130483354528023087427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330753655569685348724951 3496130483354528023087427)
                  ·
                    refine ⟨5244195725031792034631141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496130483354528023087427 5244195725031792034631141)
                    ·
                      refine ⟨983286698443461006493339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5244195725031792034631141 983286698443461006493339)
                      ·
                        rfl

theorem cell23_1914944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_1914944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914944 prefixEnd_1914944 := by exact prefixLift 1914944
  have htrace : WordTrace (prefixWord ++ tailWord_1914944) baseStart_1914944 baseEnd_1914944 := by
    simpa [prefixWord, tailWord_1914944, baseEnd_1914944] using wordTrace_append hprefix tailTrace_1914944
  have hstable : (prefixWord ++ tailWord_1914944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914944).length < 2 ^ (prefixWord ++ tailWord_1914944).sum := by decide
  have hdescent : baseEnd_1914944 < baseStart_1914944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914947 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 3]
def baseStart_1914947 : Nat := 118140960795 + 1914947 * 2 ^ 59
def prefixEnd_1914947 : Nat := 4983230072969 + 3 ^ 40 * 1914947 * 2
def baseEnd_1914947 : Nat := 983288238885424494755825

theorem tailTrace_1914947 : CollatzResearch.WordTrace tailWord_1914947 prefixEnd_1914947 983288238885424494755825 := by
  unfold tailWord_1914947
  simp only [CollatzResearch.WordTrace]
  refine ⟨69843854993481540755175095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46562569995654360503450063 69843854993481540755175095)
  ·
    refine ⟨104765782490222311132762643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69843854993481540755175095 104765782490222311132762643)
    ·
      refine ⟨157148673735333466699143965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104765782490222311132762643 157148673735333466699143965)
      ·
        refine ⟨58930752650750050012178987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157148673735333466699143965 58930752650750050012178987)
        ·
          refine ⟨88396128976125075018268481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58930752650750050012178987 88396128976125075018268481)
          ·
            refine ⟨66297096732093806263701361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88396128976125075018268481 66297096732093806263701361)
            ·
              refine ⟨49722822549070354697776021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66297096732093806263701361 49722822549070354697776021)
              ·
                refine ⟨2330757306987672876458251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49722822549070354697776021 2330757306987672876458251)
                ·
                  refine ⟨3496135960481509314687377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330757306987672876458251 3496135960481509314687377)
                  ·
                    refine ⟨2622101970361131986015533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496135960481509314687377 2622101970361131986015533)
                    ·
                      refine ⟨983288238885424494755825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2622101970361131986015533 983288238885424494755825)
                      ·
                        rfl

theorem cell23_1914947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_1914947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914947 prefixEnd_1914947 := by exact prefixLift 1914947
  have htrace : WordTrace (prefixWord ++ tailWord_1914947) baseStart_1914947 baseEnd_1914947 := by
    simpa [prefixWord, tailWord_1914947, baseEnd_1914947] using wordTrace_append hprefix tailTrace_1914947
  have hstable : (prefixWord ++ tailWord_1914947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914947).length < 2 ^ (prefixWord ++ tailWord_1914947).sum := by decide
  have hdescent : baseEnd_1914947 < baseStart_1914947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914961 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_1914961 : Nat := 118140960795 + 1914961 * 2 ^ 59
def prefixEnd_1914961 : Nat := 4983230072969 + 3 ^ 40 * 1914961 * 2
def baseEnd_1914961 : Nat := 983295427614587439980761

theorem tailTrace_1914961 : CollatzResearch.WordTrace tailWord_1914961 prefixEnd_1914961 983295427614587439980761 := by
  unfold tailWord_1914961
  simp only [CollatzResearch.WordTrace]
  refine ⟨69844365615430821146184737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46562910410287214097456491 69844365615430821146184737)
  ·
    refine ⟨52383274211573115859638553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69844365615430821146184737 52383274211573115859638553)
    ·
      refine ⟨39287455658679836894728915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52383274211573115859638553 39287455658679836894728915)
      ·
        refine ⟨58931183488019755342093373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39287455658679836894728915 58931183488019755342093373)
        ·
          refine ⟨22099193808007408253285015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58931183488019755342093373 22099193808007408253285015)
          ·
            refine ⟨33148790712011112379927523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22099193808007408253285015 33148790712011112379927523)
            ·
              refine ⟨49723186068016668569891285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33148790712011112379927523 49723186068016668569891285)
              ·
                refine ⟨1165387173469140669606827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49723186068016668569891285 1165387173469140669606827)
                ·
                  refine ⟨1748080760203711004410241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165387173469140669606827 1748080760203711004410241)
                  ·
                    refine ⟨1311060570152783253307681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1748080760203711004410241 1311060570152783253307681)
                    ·
                      refine ⟨983295427614587439980761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311060570152783253307681 983295427614587439980761)
                      ·
                        rfl

theorem cell23_1914961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_1914961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914961 prefixEnd_1914961 := by exact prefixLift 1914961
  have htrace : WordTrace (prefixWord ++ tailWord_1914961) baseStart_1914961 baseEnd_1914961 := by
    simpa [prefixWord, tailWord_1914961, baseEnd_1914961] using wordTrace_append hprefix tailTrace_1914961
  have hstable : (prefixWord ++ tailWord_1914961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914961).length < 2 ^ (prefixWord ++ tailWord_1914961).sum := by decide
  have hdescent : baseEnd_1914961 < baseStart_1914961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914980 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1914980 : Nat := 118140960795 + 1914980 * 2 ^ 59
def prefixEnd_1914980 : Nat := 4983230072969 + 3 ^ 40 * 1914980 * 2
def baseEnd_1914980 : Nat := 327768394582340955214391

theorem tailTrace_1914980 : CollatzResearch.WordTrace tailWord_1914980 prefixEnd_1914980 327768394582340955214391 := by
  unfold tailWord_1914980
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922529301180993695563197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46563372401574658260750929 34922529301180993695563197)
  ·
    refine ⟨13095948487942872635836199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34922529301180993695563197 13095948487942872635836199)
    ·
      refine ⟨19643922731914308953754299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095948487942872635836199 19643922731914308953754299)
      ·
        refine ⟨29465884097871463430631449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19643922731914308953754299 29465884097871463430631449)
        ·
          refine ⟨22099413073403597572973587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29465884097871463430631449 22099413073403597572973587)
          ·
            refine ⟨33149119610105396359460381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22099413073403597572973587 33149119610105396359460381)
            ·
              refine ⟨12430919853789523634797643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33149119610105396359460381 12430919853789523634797643)
              ·
                refine ⟨18646379780684285452196465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430919853789523634797643 18646379780684285452196465)
                ·
                  refine ⟨13984784835513214089147349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18646379780684285452196465 13984784835513214089147349)
                  ·
                    refine ⟨327768394582340955214391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13984784835513214089147349 327768394582340955214391)
                    ·
                      rfl

theorem cell23_1914980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1914980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914980 prefixEnd_1914980 := by exact prefixLift 1914980
  have htrace : WordTrace (prefixWord ++ tailWord_1914980) baseStart_1914980 baseEnd_1914980 := by
    simpa [prefixWord, tailWord_1914980, baseEnd_1914980] using wordTrace_append hprefix tailTrace_1914980
  have hstable : (prefixWord ++ tailWord_1914980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914980).length < 2 ^ (prefixWord ++ tailWord_1914980).sum := by decide
  have hdescent : baseEnd_1914980 < baseStart_1914980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914994 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1914994 : Nat := 118140960795 + 1914994 * 2 ^ 59
def prefixEnd_1914994 : Nat := 4983230072969 + 3 ^ 40 * 1914994 * 2
def baseEnd_1914994 : Nat := 983312372476185810868109

theorem tailTrace_1914994 : CollatzResearch.WordTrace tailWord_1914994 prefixEnd_1914994 983312372476185810868109 := by
  unfold tailWord_1914994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461392306077816945534009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46563712816207511854757357 17461392306077816945534009)
  ·
    refine ⟨13096044229558362709150507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461392306077816945534009 13096044229558362709150507)
    ·
      refine ⟨19644066344337544063725761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096044229558362709150507 19644066344337544063725761)
      ·
        refine ⟨14733049758253158047794321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19644066344337544063725761 14733049758253158047794321)
        ·
          refine ⟨11049787318689868535845741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14733049758253158047794321 11049787318689868535845741)
          ·
            refine ⟨4143670244508700700942153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11049787318689868535845741 4143670244508700700942153)
            ·
              refine ⟨3107752683381525525706615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143670244508700700942153 3107752683381525525706615)
              ·
                refine ⟨4661629025072288288559923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107752683381525525706615 4661629025072288288559923)
                ·
                  refine ⟨6992443537608432432839885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661629025072288288559923 6992443537608432432839885)
                  ·
                    refine ⟨2622166326603162162314957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6992443537608432432839885 2622166326603162162314957)
                    ·
                      refine ⟨983312372476185810868109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2622166326603162162314957 983312372476185810868109)
                      ·
                        rfl

theorem cell23_1914994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1914994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1914994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1914994 prefixEnd_1914994 := by exact prefixLift 1914994
  have htrace : WordTrace (prefixWord ++ tailWord_1914994) baseStart_1914994 baseEnd_1914994 := by
    simpa [prefixWord, tailWord_1914994, baseEnd_1914994] using wordTrace_append hprefix tailTrace_1914994
  have hstable : (prefixWord ++ tailWord_1914994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914994).length < 2 ^ (prefixWord ++ tailWord_1914994).sum := by decide
  have hdescent : baseEnd_1914994 < baseStart_1914994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915000 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1915000 : Nat := 118140960795 + 1915000 * 2 ^ 59
def prefixEnd_1915000 : Nat := 4983230072969 + 3 ^ 40 * 1915000 * 2
def baseEnd_1915000 : Nat := 983315453360112787393081

theorem tailTrace_1915000 : CollatzResearch.WordTrace tailWord_1915000 prefixEnd_1915000 983315453360112787393081 := by
  unfold tailWord_1915000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922894031144765403427227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46563858708193020537902969 34922894031144765403427227)
  ·
    refine ⟨52384341046717148105140841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34922894031144765403427227 52384341046717148105140841)
    ·
      refine ⟨39288255785037861078855631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52384341046717148105140841 39288255785037861078855631)
      ·
        refine ⟨58932383677556791618283447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39288255785037861078855631 58932383677556791618283447)
        ·
          refine ⟨88398575516335187427425171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58932383677556791618283447 88398575516335187427425171)
          ·
            refine ⟨132597863274502781141137757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88398575516335187427425171 132597863274502781141137757)
            ·
              refine ⟨49724198727938542927926659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132597863274502781141137757 49724198727938542927926659)
              ·
                refine ⟨74586298091907814391889989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49724198727938542927926659 74586298091907814391889989)
                ·
                  refine ⟨13984930892232715198479373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74586298091907814391889989 13984930892232715198479373)
                  ·
                    refine ⟨5244349084587268199429765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13984930892232715198479373 5244349084587268199429765)
                    ·
                      refine ⟨983315453360112787393081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5244349084587268199429765 983315453360112787393081)
                      ·
                        rfl

theorem cell23_1915000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1915000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915000 prefixEnd_1915000 := by exact prefixLift 1915000
  have htrace : WordTrace (prefixWord ++ tailWord_1915000) baseStart_1915000 baseEnd_1915000 := by
    simpa [prefixWord, tailWord_1915000, baseEnd_1915000] using wordTrace_append hprefix tailTrace_1915000
  have hstable : (prefixWord ++ tailWord_1915000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915000).length < 2 ^ (prefixWord ++ tailWord_1915000).sum := by decide
  have hdescent : baseEnd_1915000 < baseStart_1915000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915004 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_1915004 : Nat := 118140960795 + 1915004 * 2 ^ 59
def prefixEnd_1915004 : Nat := 4983230072969 + 3 ^ 40 * 1915004 * 2
def baseEnd_1915004 : Nat := 983317507282730771743063

theorem tailTrace_1915004 : CollatzResearch.WordTrace tailWord_1915004 prefixEnd_1915004 983317507282730771743063 := by
  unfold tailWord_1915004
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922966977137519745000033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46563955969516692993333377 34922966977137519745000033)
  ·
    refine ⟨26192225232853139808750025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34922966977137519745000033 26192225232853139808750025)
    ·
      refine ⟨19644168924639854856562519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26192225232853139808750025 19644168924639854856562519)
      ·
        refine ⟨29466253386959782284843779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644168924639854856562519 29466253386959782284843779)
        ·
          refine ⟨44199380080439673427265669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29466253386959782284843779 44199380080439673427265669)
          ·
            refine ⟨8287383765082438767612313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44199380080439673427265669 8287383765082438767612313)
            ·
              refine ⟨6215537823811829075709235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287383765082438767612313 6215537823811829075709235)
              ·
                refine ⟨9323306735717743613563853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215537823811829075709235 9323306735717743613563853)
                ·
                  refine ⟨3496240025894153855086445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9323306735717743613563853 3496240025894153855086445)
                  ·
                    refine ⟨1311090009710307695657417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496240025894153855086445 1311090009710307695657417)
                    ·
                      refine ⟨983317507282730771743063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311090009710307695657417 983317507282730771743063)
                      ·
                        rfl

theorem cell23_1915004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_1915004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915004 prefixEnd_1915004 := by exact prefixLift 1915004
  have htrace : WordTrace (prefixWord ++ tailWord_1915004) baseStart_1915004 baseEnd_1915004 := by
    simpa [prefixWord, tailWord_1915004, baseEnd_1915004] using wordTrace_append hprefix tailTrace_1915004
  have hstable : (prefixWord ++ tailWord_1915004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915004).length < 2 ^ (prefixWord ++ tailWord_1915004).sum := by decide
  have hdescent : baseEnd_1915004 < baseStart_1915004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915028 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1915028 : Nat := 118140960795 + 1915028 * 2 ^ 59
def prefixEnd_1915028 : Nat := 4983230072969 + 3 ^ 40 * 1915028 * 2
def baseEnd_1915028 : Nat := 983329830818438677842953

theorem tailTrace_1915028 : CollatzResearch.WordTrace tailWord_1915028 prefixEnd_1915028 983329830818438677842953 := by
  unfold tailWord_1915028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923404653094045794436869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46564539537458727725915825 34923404653094045794436869)
  ·
    refine ⟨6548138372455133586456913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34923404653094045794436869 6548138372455133586456913)
    ·
      refine ⟨4911103779341350189842685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6548138372455133586456913 4911103779341350189842685)
      ·
        refine ⟨1841663917253006321191007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4911103779341350189842685 1841663917253006321191007)
        ·
          refine ⟨2762495875879509481786511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841663917253006321191007 2762495875879509481786511)
          ·
            refine ⟨4143743813819264222679767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762495875879509481786511 4143743813819264222679767)
            ·
              refine ⟨6215615720728896334019651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143743813819264222679767 6215615720728896334019651)
              ·
                refine ⟨9323423581093344501029477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215615720728896334019651 9323423581093344501029477)
                ·
                  refine ⟨1748141921455002093943027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9323423581093344501029477 1748141921455002093943027)
                  ·
                    refine ⟨2622212882182503140914541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748141921455002093943027 2622212882182503140914541)
                    ·
                      refine ⟨983329830818438677842953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2622212882182503140914541 983329830818438677842953)
                      ·
                        rfl

theorem cell23_1915028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1915028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915028 prefixEnd_1915028 := by exact prefixLift 1915028
  have htrace : WordTrace (prefixWord ++ tailWord_1915028) baseStart_1915028 baseEnd_1915028 := by
    simpa [prefixWord, tailWord_1915028, baseEnd_1915028] using wordTrace_append hprefix tailTrace_1915028
  have hstable : (prefixWord ++ tailWord_1915028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915028).length < 2 ^ (prefixWord ++ tailWord_1915028).sum := by decide
  have hdescent : baseEnd_1915028 < baseStart_1915028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915087 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 2, 5]
def baseStart_1915087 : Nat := 118140960795 + 1915087 * 2 ^ 59
def prefixEnd_1915087 : Nat := 4983230072969 + 3 ^ 40 * 1915087 * 2
def baseEnd_1915087 : Nat := 327786708725684649001727

theorem tailTrace_1915087 : CollatzResearch.WordTrace tailWord_1915087 prefixEnd_1915087 327786708725684649001727 := by
  unfold tailWord_1915087
  simp only [CollatzResearch.WordTrace]
  refine ⟨69848961212974344665271515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46565974141982896443514343 69848961212974344665271515)
  ·
    refine ⟨104773441819461516997907273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69848961212974344665271515 104773441819461516997907273)
    ·
      refine ⟨78580081364596137748430455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104773441819461516997907273 78580081364596137748430455)
      ·
        refine ⟨117870122046894206622645683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78580081364596137748430455 117870122046894206622645683)
        ·
          refine ⟨176805183070341309933968525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117870122046894206622645683 176805183070341309933968525)
          ·
            refine ⟨66301943651377991225238197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176805183070341309933968525 66301943651377991225238197)
            ·
              refine ⟨6215807217316686677366081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66301943651377991225238197 6215807217316686677366081)
              ·
                refine ⟨4661855412987515008024561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215807217316686677366081 4661855412987515008024561)
                ·
                  refine ⟨3496391559740636256018421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661855412987515008024561 3496391559740636256018421)
                  ·
                    refine ⟨327786708725684649001727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3496391559740636256018421 327786708725684649001727)
                    ·
                      rfl

theorem cell23_1915087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_1915087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915087 prefixEnd_1915087 := by exact prefixLift 1915087
  have htrace : WordTrace (prefixWord ++ tailWord_1915087) baseStart_1915087 baseEnd_1915087 := by
    simpa [prefixWord, tailWord_1915087, baseEnd_1915087] using wordTrace_append hprefix tailTrace_1915087
  have hstable : (prefixWord ++ tailWord_1915087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915087).length < 2 ^ (prefixWord ++ tailWord_1915087).sum := by decide
  have hdescent : baseEnd_1915087 < baseStart_1915087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915137 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1915137 : Nat := 118140960795 + 1915137 * 2 ^ 59
def prefixEnd_1915137 : Nat := 4983230072969 + 3 ^ 40 * 1915137 * 2
def baseEnd_1915137 : Nat := 983385800209778751379951

theorem tailTrace_1915137 : CollatzResearch.WordTrace tailWord_1915137 prefixEnd_1915137 983385800209778751379951 := by
  unfold tailWord_1915137
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850784862793203204591665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46567189908528802136394443 69850784862793203204591665)
  ·
    refine ⟨52388088647094902403443749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69850784862793203204591665 52388088647094902403443749)
    ·
      refine ⟨9822766621330294200645703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52388088647094902403443749 9822766621330294200645703)
      ·
        refine ⟨14734149931995441300968555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822766621330294200645703 14734149931995441300968555)
        ·
          refine ⟨22101224897993161951452833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734149931995441300968555 22101224897993161951452833)
          ·
            refine ⟨16575918673494871463589625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22101224897993161951452833 16575918673494871463589625)
            ·
              refine ⟨12431939005121153597692219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16575918673494871463589625 12431939005121153597692219)
              ·
                refine ⟨18647908507681730396538329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431939005121153597692219 18647908507681730396538329)
                ·
                  refine ⟨13985931380761297797403747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18647908507681730396538329 13985931380761297797403747)
                  ·
                    refine ⟨20978897071141946696105621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13985931380761297797403747 20978897071141946696105621)
                    ·
                      refine ⟨983385800209778751379951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20978897071141946696105621 983385800209778751379951)
                      ·
                        rfl

theorem cell23_1915137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1915137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915137 prefixEnd_1915137 := by exact prefixLift 1915137
  have htrace : WordTrace (prefixWord ++ tailWord_1915137) baseStart_1915137 baseEnd_1915137 := by
    simpa [prefixWord, tailWord_1915137, baseEnd_1915137] using wordTrace_append hprefix tailTrace_1915137
  have hstable : (prefixWord ++ tailWord_1915137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915137).length < 2 ^ (prefixWord ++ tailWord_1915137).sum := by decide
  have hdescent : baseEnd_1915137 < baseStart_1915137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915208 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_1915208 : Nat := 118140960795 + 1915208 * 2 ^ 59
def prefixEnd_1915208 : Nat := 4983230072969 + 3 ^ 40 * 1915208 * 2
def baseEnd_1915208 : Nat := 983422257336247973592125

theorem tailTrace_1915208 : CollatzResearch.WordTrace tailWord_1915208 prefixEnd_1915208 983422257336247973592125 := by
  unfold tailWord_1915208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34926687222767991165213139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46568916297023988220284185 34926687222767991165213139)
  ·
    refine ⟨52390030834151986747819709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34926687222767991165213139 52390030834151986747819709)
    ·
      refine ⟨19646261562806995030432391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52390030834151986747819709 19646261562806995030432391)
      ·
        refine ⟨29469392344210492545648587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19646261562806995030432391 29469392344210492545648587)
        ·
          refine ⟨44204088516315738818472881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29469392344210492545648587 44204088516315738818472881)
          ·
            refine ⟨33153066387236804113854661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44204088516315738818472881 33153066387236804113854661)
            ·
              refine ⟨6216199947606900771347749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33153066387236804113854661 6216199947606900771347749)
              ·
                refine ⟨1165537490176293894627703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6216199947606900771347749 1165537490176293894627703)
                ·
                  refine ⟨1748306235264440841941555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165537490176293894627703 1748306235264440841941555)
                  ·
                    refine ⟨2622459352896661262912333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748306235264440841941555 2622459352896661262912333)
                    ·
                      refine ⟨983422257336247973592125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2622459352896661262912333 983422257336247973592125)
                      ·
                        rfl

theorem cell23_1915208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_1915208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915208 prefixEnd_1915208 := by exact prefixLift 1915208
  have htrace : WordTrace (prefixWord ++ tailWord_1915208) baseStart_1915208 baseEnd_1915208 := by
    simpa [prefixWord, tailWord_1915208, baseEnd_1915208] using wordTrace_append hprefix tailTrace_1915208
  have hstable : (prefixWord ++ tailWord_1915208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915208).length < 2 ^ (prefixWord ++ tailWord_1915208).sum := by decide
  have hdescent : baseEnd_1915208 < baseStart_1915208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915214 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1915214 : Nat := 118140960795 + 1915214 * 2 ^ 59
def prefixEnd_1915214 : Nat := 4983230072969 + 3 ^ 40 * 1915214 * 2
def baseEnd_1915214 : Nat := 983425338220174950117097

theorem tailTrace_1915214 : CollatzResearch.WordTrace tailWord_1915214 prefixEnd_1915214 983425338220174950117097 := by
  unfold tailWord_1915214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731699160439280669393087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46569062189009496903429797 8731699160439280669393087)
  ·
    refine ⟨13097548740658921004089631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731699160439280669393087 13097548740658921004089631)
    ·
      refine ⟨19646323110988381506134447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097548740658921004089631 19646323110988381506134447)
      ·
        refine ⟨29469484666482572259201671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19646323110988381506134447 29469484666482572259201671)
        ·
          refine ⟨44204226999723858388802507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29469484666482572259201671 44204226999723858388802507)
          ·
            refine ⟨66306340499585787583203761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44204226999723858388802507 66306340499585787583203761)
            ·
              refine ⟨49729755374689340687402821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66306340499585787583203761 49729755374689340687402821)
              ·
                refine ⟨9324329132754251378888029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49729755374689340687402821 9324329132754251378888029)
                ·
                  refine ⟨3496623424782844267083011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9324329132754251378888029 3496623424782844267083011)
                  ·
                    refine ⟨5244935137174266400624517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496623424782844267083011 5244935137174266400624517)
                    ·
                      refine ⟨983425338220174950117097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5244935137174266400624517 983425338220174950117097)
                      ·
                        rfl

theorem cell23_1915214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1915214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915214 prefixEnd_1915214 := by exact prefixLift 1915214
  have htrace : WordTrace (prefixWord ++ tailWord_1915214) baseStart_1915214 baseEnd_1915214 := by
    simpa [prefixWord, tailWord_1915214, baseEnd_1915214] using wordTrace_append hprefix tailTrace_1915214
  have hstable : (prefixWord ++ tailWord_1915214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915214).length < 2 ^ (prefixWord ++ tailWord_1915214).sum := by decide
  have hdescent : baseEnd_1915214 < baseStart_1915214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915242 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1915242 : Nat := 118140960795 + 1915242 * 2 ^ 59
def prefixEnd_1915242 : Nat := 4983230072969 + 3 ^ 40 * 1915242 * 2
def baseEnd_1915242 : Nat := 983439715678500840566969

theorem tailTrace_1915242 : CollatzResearch.WordTrace tailWord_1915242 prefixEnd_1915242 983439715678500840566969 := by
  unfold tailWord_1915242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463653631853201534290995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46569743018275204091442653 17463653631853201534290995)
  ·
    refine ⟨26195480447779802301436493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463653631853201534290995 26195480447779802301436493)
    ·
      refine ⟨9823305167917425863038685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26195480447779802301436493 9823305167917425863038685)
      ·
        refine ⟨3683739437969034698639507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9823305167917425863038685 3683739437969034698639507)
        ·
          refine ⟨5525609156953552047959261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683739437969034698639507 5525609156953552047959261)
          ·
            refine ⟨2072103433857582017984723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5525609156953552047959261 2072103433857582017984723)
            ·
              refine ⟨3108155150786373026977085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072103433857582017984723 3108155150786373026977085)
              ·
                refine ⟨1165558181544889885116407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108155150786373026977085 1165558181544889885116407)
                ·
                  refine ⟨1748337272317334827674611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165558181544889885116407 1748337272317334827674611)
                  ·
                    refine ⟨2622505908476002241511917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748337272317334827674611 2622505908476002241511917)
                    ·
                      refine ⟨983439715678500840566969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2622505908476002241511917 983439715678500840566969)
                      ·
                        rfl

theorem cell23_1915242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1915242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915242 prefixEnd_1915242 := by exact prefixLift 1915242
  have htrace : WordTrace (prefixWord ++ tailWord_1915242) baseStart_1915242 baseEnd_1915242 := by
    simpa [prefixWord, tailWord_1915242, baseEnd_1915242] using wordTrace_append hprefix tailTrace_1915242
  have hstable : (prefixWord ++ tailWord_1915242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915242).length < 2 ^ (prefixWord ++ tailWord_1915242).sum := by decide
  have hdescent : baseEnd_1915242 < baseStart_1915242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915265 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1915265 : Nat := 118140960795 + 1915265 * 2 ^ 59
def prefixEnd_1915265 : Nat := 4983230072969 + 3 ^ 40 * 1915265 * 2
def baseEnd_1915265 : Nat := 983451525733554250579363

theorem tailTrace_1915265 : CollatzResearch.WordTrace tailWord_1915265 prefixEnd_1915265 983451525733554250579363 := by
  unfold tailWord_1915265
  simp only [CollatzResearch.WordTrace]
  refine ⟨69855453406329481065251249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46570302270886320710167499 69855453406329481065251249)
  ·
    refine ⟨52391590054747110798938437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69855453406329481065251249 52391590054747110798938437)
    ·
      refine ⟨9823423135265083274800957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52391590054747110798938437 9823423135265083274800957)
      ·
        refine ⟨3683783675724406228050359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9823423135265083274800957 3683783675724406228050359)
        ·
          refine ⟨5525675513586609342075539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683783675724406228050359 5525675513586609342075539)
          ·
            refine ⟨8288513270379914013113309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525675513586609342075539 8288513270379914013113309)
            ·
              refine ⟨3108192476392467754917491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8288513270379914013113309 3108192476392467754917491)
              ·
                refine ⟨4662288714588701632376237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108192476392467754917491 4662288714588701632376237)
                ·
                  refine ⟨1748358267970763112141089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4662288714588701632376237 1748358267970763112141089)
                  ·
                    refine ⟨1311268700978072334105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1748358267970763112141089 1311268700978072334105817)
                    ·
                      refine ⟨983451525733554250579363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311268700978072334105817 983451525733554250579363)
                      ·
                        rfl

theorem cell23_1915265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1915265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915265 prefixEnd_1915265 := by exact prefixLift 1915265
  have htrace : WordTrace (prefixWord ++ tailWord_1915265) baseStart_1915265 baseEnd_1915265 := by
    simpa [prefixWord, tailWord_1915265, baseEnd_1915265] using wordTrace_append hprefix tailTrace_1915265
  have hstable : (prefixWord ++ tailWord_1915265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915265).length < 2 ^ (prefixWord ++ tailWord_1915265).sum := by decide
  have hdescent : baseEnd_1915265 < baseStart_1915265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915314 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1915314 : Nat := 118140960795 + 1915314 * 2 ^ 59
def prefixEnd_1915314 : Nat := 4983230072969 + 3 ^ 40 * 1915314 * 2
def baseEnd_1915314 : Nat := 327825562095208186288879

theorem tailTrace_1915314 : CollatzResearch.WordTrace tailWord_1915314 prefixEnd_1915314 327825562095208186288879 := by
  unfold tailWord_1915314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464310145787990608446249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46571493722101308289189997 17464310145787990608446249)
  ·
    refine ⟨13098232609340992956334687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17464310145787990608446249 13098232609340992956334687)
    ·
      refine ⟨19647348914011489434502031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098232609340992956334687 19647348914011489434502031)
      ·
        refine ⟨29471023371017234151753047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19647348914011489434502031 29471023371017234151753047)
        ·
          refine ⟨44206535056525851227629571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29471023371017234151753047 44206535056525851227629571)
          ·
            refine ⟨66309802584788776841444357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44206535056525851227629571 66309802584788776841444357)
            ·
              refine ⟨12433087984647895657770817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66309802584788776841444357 12433087984647895657770817)
              ·
                refine ⟨9324815988485921743328113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12433087984647895657770817 9324815988485921743328113)
                ·
                  refine ⟨6993611991364441307496085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9324815988485921743328113 6993611991364441307496085)
                  ·
                    refine ⟨327825562095208186288879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6993611991364441307496085 327825562095208186288879)
                    ·
                      rfl

theorem cell23_1915314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1915314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915314 prefixEnd_1915314 := by exact prefixLift 1915314
  have htrace : WordTrace (prefixWord ++ tailWord_1915314) baseStart_1915314 baseEnd_1915314 := by
    simpa [prefixWord, tailWord_1915314, baseEnd_1915314] using wordTrace_append hprefix tailTrace_1915314
  have hstable : (prefixWord ++ tailWord_1915314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915314).length < 2 ^ (prefixWord ++ tailWord_1915314).sum := by decide
  have hdescent : baseEnd_1915314 < baseStart_1915314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915316 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1915316 : Nat := 118140960795 + 1915316 * 2 ^ 59
def prefixEnd_1915316 : Nat := 4983230072969 + 3 ^ 40 * 1915316 * 2
def baseEnd_1915316 : Nat := 983477713246933551041629

theorem tailTrace_1915316 : CollatzResearch.WordTrace tailWord_1915316 prefixEnd_1915316 983477713246933551041629 := by
  unfold tailWord_1915316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928656764572358387678901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46571542352763144516905201 34928656764572358387678901)
  ·
    refine ⟨3274561571678658598844897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34928656764572358387678901 3274561571678658598844897)
    ·
      refine ⟨2455921178758993949133673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3274561571678658598844897 2455921178758993949133673)
      ·
        refine ⟨1841940884069245461850255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455921178758993949133673 1841940884069245461850255)
        ·
          refine ⟨2762911326103868192775383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841940884069245461850255 2762911326103868192775383)
          ·
            refine ⟨4144366989155802289163075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762911326103868192775383 4144366989155802289163075)
            ·
              refine ⟨6216550483733703433744613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144366989155802289163075 6216550483733703433744613)
              ·
                refine ⟨1165603215700069393827115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6216550483733703433744613 1165603215700069393827115)
                ·
                  refine ⟨1748404823550104090740673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165603215700069393827115 1748404823550104090740673)
                  ·
                    refine ⟨1311303617662578068055505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1748404823550104090740673 1311303617662578068055505)
                    ·
                      refine ⟨983477713246933551041629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311303617662578068055505 983477713246933551041629)
                      ·
                        rfl

theorem cell23_1915316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1915316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915316 prefixEnd_1915316 := by exact prefixLift 1915316
  have htrace : WordTrace (prefixWord ++ tailWord_1915316) baseStart_1915316 baseEnd_1915316 := by
    simpa [prefixWord, tailWord_1915316, baseEnd_1915316] using wordTrace_append hprefix tailTrace_1915316
  have hstable : (prefixWord ++ tailWord_1915316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915316).length < 2 ^ (prefixWord ++ tailWord_1915316).sum := by decide
  have hdescent : baseEnd_1915316 < baseStart_1915316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915338 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_1915338 : Nat := 118140960795 + 1915338 * 2 ^ 59
def prefixEnd_1915338 : Nat := 4983230072969 + 3 ^ 40 * 1915338 * 2
def baseEnd_1915338 : Nat := 983489009821332464966527

theorem tailTrace_1915338 : CollatzResearch.WordTrace tailWord_1915338 prefixEnd_1915338 983489009821332464966527 := by
  unfold tailWord_1915338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464528983766253633164667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46572077290043343021772445 17464528983766253633164667)
  ·
    refine ⟨26196793475649380449747001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17464528983766253633164667 26196793475649380449747001)
    ·
      refine ⟨19647595106737035337310251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26196793475649380449747001 19647595106737035337310251)
      ·
        refine ⟨29471392660105553005965377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19647595106737035337310251 29471392660105553005965377)
        ·
          refine ⟨22103544495079164754474033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29471392660105553005965377 22103544495079164754474033)
          ·
            refine ⟨16577658371309373565855525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22103544495079164754474033 16577658371309373565855525)
            ·
              refine ⟨3108310944620507543597911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16577658371309373565855525 3108310944620507543597911)
              ·
                refine ⟨4662466416930761315396867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108310944620507543597911 4662466416930761315396867)
                ·
                  refine ⟨6993699625396141973095301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662466416930761315396867 6993699625396141973095301)
                  ·
                    refine ⟨1311318679761776619955369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993699625396141973095301 1311318679761776619955369)
                    ·
                      refine ⟨983489009821332464966527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311318679761776619955369 983489009821332464966527)
                      ·
                        rfl

theorem cell23_1915338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_1915338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915338 prefixEnd_1915338 := by exact prefixLift 1915338
  have htrace : WordTrace (prefixWord ++ tailWord_1915338) baseStart_1915338 baseEnd_1915338 := by
    simpa [prefixWord, tailWord_1915338, baseEnd_1915338] using wordTrace_append hprefix tailTrace_1915338
  have hstable : (prefixWord ++ tailWord_1915338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915338).length < 2 ^ (prefixWord ++ tailWord_1915338).sum := by decide
  have hdescent : baseEnd_1915338 < baseStart_1915338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915378 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1915378 : Nat := 118140960795 + 1915378 * 2 ^ 59
def prefixEnd_1915378 : Nat := 4983230072969 + 3 ^ 40 * 1915378 * 2
def baseEnd_1915378 : Nat := 109278838783056923162927

theorem tailTrace_1915378 : CollatzResearch.WordTrace tailWord_1915378 prefixEnd_1915378 109278838783056923162927 := by
  unfold tailWord_1915378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464893713730025341028697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46573049903280067576076525 17464893713730025341028697)
  ·
    refine ⟨13098670285297519005771523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17464893713730025341028697 13098670285297519005771523)
    ·
      refine ⟨19648005427946278508657285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098670285297519005771523 19648005427946278508657285)
      ·
        refine ⟨3684001017739927220373241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19648005427946278508657285 3684001017739927220373241)
        ·
          refine ⟨2763000763304945415279931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684001017739927220373241 2763000763304945415279931)
          ·
            refine ⟨4144501144957418122919897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763000763304945415279931 4144501144957418122919897)
            ·
              refine ⟨3108375858718063592189923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4144501144957418122919897 3108375858718063592189923)
              ·
                refine ⟨4662563788077095388284885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108375858718063592189923 4662563788077095388284885)
                ·
                  refine ⟨109278838783056923162927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4662563788077095388284885 109278838783056923162927)
                  ·
                    rfl

theorem cell23_1915378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1915378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915378 prefixEnd_1915378 := by exact prefixLift 1915378
  have htrace : WordTrace (prefixWord ++ tailWord_1915378) baseStart_1915378 baseEnd_1915378 := by
    simpa [prefixWord, tailWord_1915378, baseEnd_1915378] using wordTrace_append hprefix tailTrace_1915378
  have hstable : (prefixWord ++ tailWord_1915378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915378).length < 2 ^ (prefixWord ++ tailWord_1915378).sum := by decide
  have hdescent : baseEnd_1915378 < baseStart_1915378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915384 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1915384 : Nat := 118140960795 + 1915384 * 2 ^ 59
def prefixEnd_1915384 : Nat := 4983230072969 + 3 ^ 40 * 1915384 * 2
def baseEnd_1915384 : Nat := 983512629931439284991315

theorem tailTrace_1915384 : CollatzResearch.WordTrace tailWord_1915384 prefixEnd_1915384 983512629931439284991315 := by
  unfold tailWord_1915384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34929896846449182194416603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46573195795265576259222137 34929896846449182194416603)
  ·
    refine ⟨52394845269673773291624905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34929896846449182194416603 52394845269673773291624905)
    ·
      refine ⟨39296133952255329968718679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52394845269673773291624905 39296133952255329968718679)
      ·
        refine ⟨58944200928382994953078019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39296133952255329968718679 58944200928382994953078019)
        ·
          refine ⟨88416301392574492429617029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58944200928382994953078019 88416301392574492429617029)
          ·
            refine ⟨16578056511107717330553193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88416301392574492429617029 16578056511107717330553193)
            ·
              refine ⟨12433542383330787997914895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16578056511107717330553193 12433542383330787997914895)
              ·
                refine ⟨18650313574996181996872343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12433542383330787997914895 18650313574996181996872343)
                ·
                  refine ⟨27975470362494272995308515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18650313574996181996872343 27975470362494272995308515)
                  ·
                    refine ⟨41963205543741409492962773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27975470362494272995308515 41963205543741409492962773)
                    ·
                      refine ⟨983512629931439284991315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41963205543741409492962773 983512629931439284991315)
                      ·
                        rfl

theorem cell23_1915384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1915384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915384 prefixEnd_1915384 := by exact prefixLift 1915384
  have htrace : WordTrace (prefixWord ++ tailWord_1915384) baseStart_1915384 baseEnd_1915384 := by
    simpa [prefixWord, tailWord_1915384, baseEnd_1915384] using wordTrace_append hprefix tailTrace_1915384
  have hstable : (prefixWord ++ tailWord_1915384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915384).length < 2 ^ (prefixWord ++ tailWord_1915384).sum := by decide
  have hdescent : baseEnd_1915384 < baseStart_1915384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915411 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4]
def baseStart_1915411 : Nat := 118140960795 + 1915411 * 2 ^ 59
def prefixEnd_1915411 : Nat := 4983230072969 + 3 ^ 40 * 1915411 * 2
def baseEnd_1915411 : Nat := 983526493909110679353691

theorem tailTrace_1915411 : CollatzResearch.WordTrace tailWord_1915411 prefixEnd_1915411 983526493909110679353691 := by
  unfold tailWord_1915411
  simp only [CollatzResearch.WordTrace]
  refine ⟨69860778463800548000066087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46573852309200365333377391 69860778463800548000066087)
  ·
    refine ⟨104791167695700822000099131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69860778463800548000066087 104791167695700822000099131)
    ·
      refine ⟨157186751543551233000148697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104791167695700822000099131 157186751543551233000148697)
      ·
        refine ⟨117890063657663424750111523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157186751543551233000148697 117890063657663424750111523)
        ·
          refine ⟨176835095486495137125167285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117890063657663424750111523 176835095486495137125167285)
          ·
            refine ⟨16578290201858919105484433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176835095486495137125167285 16578290201858919105484433)
            ·
              refine ⟨12433717651394189329113325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16578290201858919105484433 12433717651394189329113325)
              ·
                refine ⟨4662644119272820998417497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12433717651394189329113325 4662644119272820998417497)
                ·
                  refine ⟨3496983089454615748813123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662644119272820998417497 3496983089454615748813123)
                  ·
                    refine ⟨5245474634181923623219685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496983089454615748813123 5245474634181923623219685)
                    ·
                      refine ⟨983526493909110679353691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5245474634181923623219685 983526493909110679353691)
                      ·
                        rfl

theorem cell23_1915411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_1915411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915411 prefixEnd_1915411 := by exact prefixLift 1915411
  have htrace : WordTrace (prefixWord ++ tailWord_1915411) baseStart_1915411 baseEnd_1915411 := by
    simpa [prefixWord, tailWord_1915411, baseEnd_1915411] using wordTrace_append hprefix tailTrace_1915411
  have hstable : (prefixWord ++ tailWord_1915411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915411).length < 2 ^ (prefixWord ++ tailWord_1915411).sum := by decide
  have hdescent : baseEnd_1915411 < baseStart_1915411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915412 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1915412 : Nat := 118140960795 + 1915412 * 2 ^ 59
def prefixEnd_1915412 : Nat := 4983230072969 + 3 ^ 40 * 1915412 * 2
def baseEnd_1915412 : Nat := 109280778598862797271243

theorem tailTrace_1915412 : CollatzResearch.WordTrace tailWord_1915412 prefixEnd_1915412 109280778598862797271243 := by
  unfold tailWord_1915412
  simp only [CollatzResearch.WordTrace]
  refine ⟨34930407468398462585426245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46573876624531283447234993 34930407468398462585426245)
  ·
    refine ⟨6549451400324711734767421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34930407468398462585426245 6549451400324711734767421)
    ·
      refine ⟨2456044275121766900537783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6549451400324711734767421 2456044275121766900537783)
      ·
        refine ⟨3684066412682650350806675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456044275121766900537783 3684066412682650350806675)
        ·
          refine ⟨5526099619023975526210013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684066412682650350806675 5526099619023975526210013)
          ·
            refine ⟨2072287357133990822328755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5526099619023975526210013 2072287357133990822328755)
            ·
              refine ⟨3108431035700986233493133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072287357133990822328755 3108431035700986233493133)
              ·
                refine ⟨1165661638387869837559925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108431035700986233493133 1165661638387869837559925)
                ·
                  refine ⟨109280778598862797271243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165661638387869837559925 109280778598862797271243)
                  ·
                    rfl

theorem cell23_1915412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1915412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915412 prefixEnd_1915412 := by exact prefixLift 1915412
  have htrace : WordTrace (prefixWord ++ tailWord_1915412) baseStart_1915412 baseEnd_1915412 := by
    simpa [prefixWord, tailWord_1915412, baseEnd_1915412] using wordTrace_append hprefix tailTrace_1915412
  have hstable : (prefixWord ++ tailWord_1915412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915412).length < 2 ^ (prefixWord ++ tailWord_1915412).sum := by decide
  have hdescent : baseEnd_1915412 < baseStart_1915412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915462 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1915462 : Nat := 118140960795 + 1915462 * 2 ^ 59
def prefixEnd_1915462 : Nat := 4983230072969 + 3 ^ 40 * 1915462 * 2
def baseEnd_1915462 : Nat := 983552681422489979815957

theorem tailTrace_1915462 : CollatzResearch.WordTrace tailWord_1915462 prefixEnd_1915462 983552681422489979815957 := by
  unfold tailWord_1915462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183207455831743240942895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46575092391077189140115093 2183207455831743240942895)
  ·
    refine ⟨3274811183747614861414343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183207455831743240942895 3274811183747614861414343)
    ·
      refine ⟨4912216775621422292121515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274811183747614861414343 4912216775621422292121515)
      ·
        refine ⟨7368325163432133438182273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912216775621422292121515 7368325163432133438182273)
        ·
          refine ⟨5526243872574100078636705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7368325163432133438182273 5526243872574100078636705)
          ·
            refine ⟨4144682904430575058977529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5526243872574100078636705 4144682904430575058977529)
            ·
              refine ⟨3108512178322931294233147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4144682904430575058977529 3108512178322931294233147)
              ·
                refine ⟨4662768267484396941349721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108512178322931294233147 4662768267484396941349721)
                ·
                  refine ⟨3497076200613297706012291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662768267484396941349721 3497076200613297706012291)
                  ·
                    refine ⟨5245614300919946559018437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497076200613297706012291 5245614300919946559018437)
                    ·
                      refine ⟨983552681422489979815957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5245614300919946559018437 983552681422489979815957)
                      ·
                        rfl

theorem cell23_1915462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1915462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915462 prefixEnd_1915462 := by exact prefixLift 1915462
  have htrace : WordTrace (prefixWord ++ tailWord_1915462) baseStart_1915462 baseEnd_1915462 := by
    simpa [prefixWord, tailWord_1915462, baseEnd_1915462] using wordTrace_append hprefix tailTrace_1915462
  have hstable : (prefixWord ++ tailWord_1915462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915462).length < 2 ^ (prefixWord ++ tailWord_1915462).sum := by decide
  have hdescent : baseEnd_1915462 < baseStart_1915462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915511 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1915511 : Nat := 118140960795 + 1915511 * 2 ^ 59
def prefixEnd_1915511 : Nat := 4983230072969 + 3 ^ 40 * 1915511 * 2
def baseEnd_1915511 : Nat := 327859280658186762701077

theorem tailTrace_1915511 : CollatzResearch.WordTrace tailWord_1915511 prefixEnd_1915511 327859280658186762701077 := by
  unfold tailWord_1915511
  simp only [CollatzResearch.WordTrace]
  refine ⟨69864425763438265078706387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46576283842292176719137591 69864425763438265078706387)
  ·
    refine ⟨104796638645157397618059581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69864425763438265078706387 104796638645157397618059581)
    ·
      refine ⟨39298739491934024106772343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104796638645157397618059581 39298739491934024106772343)
      ·
        refine ⟨58948109237901036160158515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39298739491934024106772343 58948109237901036160158515)
        ·
          refine ⟨88422163856851554240237773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58948109237901036160158515 88422163856851554240237773)
          ·
            refine ⟨33158311446319332840089165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88422163856851554240237773 33158311446319332840089165)
            ·
              refine ⟨12434366792369749815033437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33158311446319332840089165 12434366792369749815033437)
              ·
                refine ⟨4662887547138656180637539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12434366792369749815033437 4662887547138656180637539)
                ·
                  refine ⟨6994331320707984270956309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662887547138656180637539 6994331320707984270956309)
                  ·
                    refine ⟨327859280658186762701077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6994331320707984270956309 327859280658186762701077)
                    ·
                      rfl

theorem cell23_1915511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1915511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915511 prefixEnd_1915511 := by exact prefixLift 1915511
  have htrace : WordTrace (prefixWord ++ tailWord_1915511) baseStart_1915511 baseEnd_1915511 := by
    simpa [prefixWord, tailWord_1915511, baseEnd_1915511] using wordTrace_append hprefix tailTrace_1915511
  have hstable : (prefixWord ++ tailWord_1915511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915511).length < 2 ^ (prefixWord ++ tailWord_1915511).sum := by decide
  have hdescent : baseEnd_1915511 < baseStart_1915511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915531 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_1915531 : Nat := 118140960795 + 1915531 * 2 ^ 59
def prefixEnd_1915531 : Nat := 4983230072969 + 3 ^ 40 * 1915531 * 2
def baseEnd_1915531 : Nat := 983588111587650209853139

theorem tailTrace_1915531 : CollatzResearch.WordTrace tailWord_1915531 prefixEnd_1915531 983588111587650209853139 := by
  unfold tailWord_1915531
  simp only [CollatzResearch.WordTrace]
  refine ⟨69865155223365808494434447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46576770148910538996289631 69865155223365808494434447)
  ·
    refine ⟨104797732835048712741651671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69865155223365808494434447 104797732835048712741651671)
    ·
      refine ⟨157196599252573069112477507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104797732835048712741651671 157196599252573069112477507)
      ·
        refine ⟨235794898878859603668716261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157196599252573069112477507 235794898878859603668716261)
        ·
          refine ⟨44211543539786175687884299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235794898878859603668716261 44211543539786175687884299)
          ·
            refine ⟨66317315309679263531826449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44211543539786175687884299 66317315309679263531826449)
            ·
              refine ⟨49737986482259447648869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66317315309679263531826449 49737986482259447648869837)
              ·
                refine ⟨18651744930847292868326189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49737986482259447648869837 18651744930847292868326189)
                ·
                  refine ⟨6994404349067734825622321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651744930847292868326189 6994404349067734825622321)
                  ·
                    refine ⟨5245803261800801119216741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994404349067734825622321 5245803261800801119216741)
                    ·
                      refine ⟨983588111587650209853139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5245803261800801119216741 983588111587650209853139)
                      ·
                        rfl

theorem cell23_1915531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_1915531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915531 prefixEnd_1915531 := by exact prefixLift 1915531
  have htrace : WordTrace (prefixWord ++ tailWord_1915531) baseStart_1915531 baseEnd_1915531 := by
    simpa [prefixWord, tailWord_1915531, baseEnd_1915531] using wordTrace_append hprefix tailTrace_1915531
  have hstable : (prefixWord ++ tailWord_1915531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915531).length < 2 ^ (prefixWord ++ tailWord_1915531).sum := by decide
  have hdescent : baseEnd_1915531 < baseStart_1915531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915565 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1915565 : Nat := 118140960795 + 1915565 * 2 ^ 59
def prefixEnd_1915565 : Nat := 4983230072969 + 3 ^ 40 * 1915565 * 2
def baseEnd_1915565 : Nat := 983605569929903076827983

theorem tailTrace_1915565 : CollatzResearch.WordTrace tailWord_1915565 prefixEnd_1915565 983605569929903076827983 := by
  unfold tailWord_1915565
  simp only [CollatzResearch.WordTrace]
  refine ⟨69866395305242632301172149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46577596870161754867448099 69866395305242632301172149)
  ·
    refine ⟨6549974559866496778234889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69866395305242632301172149 6549974559866496778234889)
    ·
      refine ⟨4912480919899872583676167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6549974559866496778234889 4912480919899872583676167)
      ·
        refine ⟨7368721379849808875514251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912480919899872583676167 7368721379849808875514251)
        ·
          refine ⟨11053082069774713313271377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368721379849808875514251 11053082069774713313271377)
          ·
            refine ⟨8289811552331034984953533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11053082069774713313271377 8289811552331034984953533)
            ·
              refine ⟨3108679332124138119357575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8289811552331034984953533 3108679332124138119357575)
              ·
                refine ⟨4663018998186207179036363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108679332124138119357575 4663018998186207179036363)
                ·
                  refine ⟨6994528497279310768554545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663018998186207179036363 6994528497279310768554545)
                  ·
                    refine ⟨5245896372959483076415909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994528497279310768554545 5245896372959483076415909)
                    ·
                      refine ⟨983605569929903076827983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5245896372959483076415909 983605569929903076827983)
                      ·
                        rfl

theorem cell23_1915565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1915565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915565 prefixEnd_1915565 := by exact prefixLift 1915565
  have htrace : WordTrace (prefixWord ++ tailWord_1915565) baseStart_1915565 baseEnd_1915565 := by
    simpa [prefixWord, tailWord_1915565, baseEnd_1915565] using wordTrace_append hprefix tailTrace_1915565
  have hstable : (prefixWord ++ tailWord_1915565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915565).length < 2 ^ (prefixWord ++ tailWord_1915565).sum := by decide
  have hdescent : baseEnd_1915565 < baseStart_1915565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915575 : List Nat := [1, 1, 3, 1, 6, 2, 2, 7]
def baseStart_1915575 : Nat := 118140960795 + 1915575 * 2 ^ 59
def prefixEnd_1915575 : Nat := 4983230072969 + 3 ^ 40 * 1915575 * 2
def baseEnd_1915575 : Nat := 36430026101349927322331

theorem tailTrace_1915575 : CollatzResearch.WordTrace tailWord_1915575 prefixEnd_1915575 36430026101349927322331 := by
  unfold tailWord_1915575
  simp only [CollatzResearch.WordTrace]
  refine ⟨69866760035206404009036179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46577840023470936006024119 69866760035206404009036179)
  ·
    refine ⟨104800140052809606013554269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69866760035206404009036179 104800140052809606013554269)
    ·
      refine ⟨39300052519803602255082851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104800140052809606013554269 39300052519803602255082851)
      ·
        refine ⟨58950078779705403382624277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39300052519803602255082851 58950078779705403382624277)
        ·
          refine ⟨2763284942798690783560513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58950078779705403382624277 2763284942798690783560513)
          ·
            refine ⟨2072463707099018087670385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2763284942798690783560513 2072463707099018087670385)
            ·
              refine ⟨1554347780324263565752789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072463707099018087670385 1554347780324263565752789)
              ·
                refine ⟨36430026101349927322331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1554347780324263565752789 36430026101349927322331)
                ·
                  rfl

theorem cell23_1915575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 7].length) (baseStart_1915575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915575 prefixEnd_1915575 := by exact prefixLift 1915575
  have htrace : WordTrace (prefixWord ++ tailWord_1915575) baseStart_1915575 baseEnd_1915575 := by
    simpa [prefixWord, tailWord_1915575, baseEnd_1915575] using wordTrace_append hprefix tailTrace_1915575
  have hstable : (prefixWord ++ tailWord_1915575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915575).length < 2 ^ (prefixWord ++ tailWord_1915575).sum := by decide
  have hdescent : baseEnd_1915575 < baseStart_1915575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915619 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1915619 : Nat := 118140960795 + 1915619 * 2 ^ 59
def prefixEnd_1915619 : Nat := 4983230072969 + 3 ^ 40 * 1915619 * 2
def baseEnd_1915619 : Nat := 983633297885245865552735

theorem tailTrace_1915619 : CollatzResearch.WordTrace tailWord_1915619 prefixEnd_1915619 983633297885245865552735 := by
  unfold tailWord_1915619
  simp only [CollatzResearch.WordTrace]
  refine ⟨69868364847046999523637911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46578909898031333015758607 69868364847046999523637911)
  ·
    refine ⟨104802547270570499285456867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69868364847046999523637911 104802547270570499285456867)
    ·
      refine ⟨157203820905855748928185301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104802547270570499285456867 157203820905855748928185301)
      ·
        refine ⟨3684464552480994115504343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157203820905855748928185301 3684464552480994115504343)
        ·
          refine ⟨5526696828721491173256515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684464552480994115504343 5526696828721491173256515)
          ·
            refine ⟨8290045243082236759884773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526696828721491173256515 8290045243082236759884773)
            ·
              refine ⟨1554383483077919392478395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8290045243082236759884773 1554383483077919392478395)
              ·
                refine ⟨2331575224616879088717593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554383483077919392478395 2331575224616879088717593)
                ·
                  refine ⟨1748681418462659316538195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2331575224616879088717593 1748681418462659316538195)
                  ·
                    refine ⟨2623022127693988974807293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748681418462659316538195 2623022127693988974807293)
                    ·
                      refine ⟨983633297885245865552735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623022127693988974807293 983633297885245865552735)
                      ·
                        rfl

theorem cell23_1915619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1915619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915619 prefixEnd_1915619 := by exact prefixLift 1915619
  have htrace : WordTrace (prefixWord ++ tailWord_1915619) baseStart_1915619 baseEnd_1915619 := by
    simpa [prefixWord, tailWord_1915619, baseEnd_1915619] using wordTrace_append hprefix tailTrace_1915619
  have hstable : (prefixWord ++ tailWord_1915619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915619).length < 2 ^ (prefixWord ++ tailWord_1915619).sum := by decide
  have hdescent : baseEnd_1915619 < baseStart_1915619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915646 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1915646 : Nat := 118140960795 + 1915646 * 2 ^ 59
def prefixEnd_1915646 : Nat := 4983230072969 + 3 ^ 40 * 1915646 * 2
def baseEnd_1915646 : Nat := 983647161862917259915111

theorem tailTrace_1915646 : CollatzResearch.WordTrace tailWord_1915646 prefixEnd_1915646 983647161862917259915111 := by
  unfold tailWord_1915646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733668702243647891858849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46579566411966122089913861 8733668702243647891858849)
  ·
    refine ⟨6550251526682735918894137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8733668702243647891858849 6550251526682735918894137)
    ·
      refine ⟨4912688645012051939170603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6550251526682735918894137 4912688645012051939170603)
      ·
        refine ⟨7369032967518077908755905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912688645012051939170603 7369032967518077908755905)
        ·
          refine ⟨5526774725638558431566929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369032967518077908755905 5526774725638558431566929)
          ·
            refine ⟨4145081044228918823675197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5526774725638558431566929 4145081044228918823675197)
            ·
              refine ⟨1554405391585844558878199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4145081044228918823675197 1554405391585844558878199)
              ·
                refine ⟨2331608087378766838317299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554405391585844558878199 2331608087378766838317299)
                ·
                  refine ⟨3497412131068150257475949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331608087378766838317299 3497412131068150257475949)
                  ·
                    refine ⟨1311529549150556346553481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497412131068150257475949 1311529549150556346553481)
                    ·
                      refine ⟨983647161862917259915111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311529549150556346553481 983647161862917259915111)
                      ·
                        rfl

theorem cell23_1915646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1915646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915646 prefixEnd_1915646 := by exact prefixLift 1915646
  have htrace : WordTrace (prefixWord ++ tailWord_1915646) baseStart_1915646 baseEnd_1915646 := by
    simpa [prefixWord, tailWord_1915646, baseEnd_1915646] using wordTrace_append hprefix tailTrace_1915646
  have hstable : (prefixWord ++ tailWord_1915646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915646).length < 2 ^ (prefixWord ++ tailWord_1915646).sum := by decide
  have hdescent : baseEnd_1915646 < baseStart_1915646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915685 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_1915685 : Nat := 118140960795 + 1915685 * 2 ^ 59
def prefixEnd_1915685 : Nat := 4983230072969 + 3 ^ 40 * 1915685 * 2
def baseEnd_1915685 : Nat := 983667187608442607327431

theorem tailTrace_1915685 : CollatzResearch.WordTrace tailWord_1915685 prefixEnd_1915685 983667187608442607327431 := by
  unfold tailWord_1915685
  simp only [CollatzResearch.WordTrace]
  refine ⟨69870772064807892795540509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46580514709871928530360339 69870772064807892795540509)
  ·
    refine ⟨26201539524302959798327691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69870772064807892795540509 26201539524302959798327691)
    ·
      refine ⟨39302309286454439697491537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26201539524302959798327691 39302309286454439697491537)
      ·
        refine ⟨29476731964840829773118653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39302309286454439697491537 29476731964840829773118653)
        ·
          refine ⟨11053774486815311164919495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29476731964840829773118653 11053774486815311164919495)
          ·
            refine ⟨16580661730222966747379243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11053774486815311164919495 16580661730222966747379243)
            ·
              refine ⟨24870992595334450121068865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580661730222966747379243 24870992595334450121068865)
              ·
                refine ⟨18653244446500837590801649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24870992595334450121068865 18653244446500837590801649)
                ·
                  refine ⟨13989933334875628193101237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18653244446500837590801649 13989933334875628193101237)
                  ·
                    refine ⟨1311556250144590143103241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13989933334875628193101237 1311556250144590143103241)
                    ·
                      refine ⟨983667187608442607327431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311556250144590143103241 983667187608442607327431)
                      ·
                        rfl

theorem cell23_1915685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_1915685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915685 prefixEnd_1915685 := by exact prefixLift 1915685
  have htrace : WordTrace (prefixWord ++ tailWord_1915685) baseStart_1915685 baseEnd_1915685 := by
    simpa [prefixWord, tailWord_1915685, baseEnd_1915685] using wordTrace_append hprefix tailTrace_1915685
  have hstable : (prefixWord ++ tailWord_1915685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915685).length < 2 ^ (prefixWord ++ tailWord_1915685).sum := by decide
  have hdescent : baseEnd_1915685 < baseStart_1915685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915715 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 4, 2]
def baseStart_1915715 : Nat := 118140960795 + 1915715 * 2 ^ 59
def prefixEnd_1915715 : Nat := 4983230072969 + 3 ^ 40 * 1915715 * 2
def baseEnd_1915715 : Nat := 983682592028077489952293

theorem tailTrace_1915715 : CollatzResearch.WordTrace tailWord_1915715 prefixEnd_1915715 983682592028077489952293 := by
  unfold tailWord_1915715
  simp only [CollatzResearch.WordTrace]
  refine ⟨69871866254699207919132599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46581244169799471946088399 69871866254699207919132599)
  ·
    refine ⟨104807799382048811878698899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69871866254699207919132599 104807799382048811878698899)
    ·
      refine ⟨157211699073073217818048349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104807799382048811878698899 157211699073073217818048349)
      ·
        refine ⟨58954387152402456681768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157211699073073217818048349 58954387152402456681768131)
        ·
          refine ⟨88431580728603685022652197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58954387152402456681768131 88431580728603685022652197)
          ·
            refine ⟨16580921386613190941747287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88431580728603685022652197 16580921386613190941747287)
            ·
              refine ⟨24871382079919786412620931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580921386613190941747287 24871382079919786412620931)
              ·
                refine ⟨37307073119879679618931397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871382079919786412620931 37307073119879679618931397)
                ·
                  refine ⟨6995076209977439928549637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37307073119879679618931397 6995076209977439928549637)
                  ·
                    refine ⟨1311576789370769986603057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995076209977439928549637 1311576789370769986603057)
                    ·
                      refine ⟨983682592028077489952293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311576789370769986603057 983682592028077489952293)
                      ·
                        rfl

theorem cell23_1915715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_1915715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915715 prefixEnd_1915715 := by exact prefixLift 1915715
  have htrace : WordTrace (prefixWord ++ tailWord_1915715) baseStart_1915715 baseEnd_1915715 := by
    simpa [prefixWord, tailWord_1915715, baseEnd_1915715] using wordTrace_append hprefix tailTrace_1915715
  have hstable : (prefixWord ++ tailWord_1915715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915715).length < 2 ^ (prefixWord ++ tailWord_1915715).sum := by decide
  have hdescent : baseEnd_1915715 < baseStart_1915715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915735 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1915735 : Nat := 118140960795 + 1915735 * 2 ^ 59
def prefixEnd_1915735 : Nat := 4983230072969 + 3 ^ 40 * 1915735 * 2
def baseEnd_1915735 : Nat := 983692861641167411702201

theorem tailTrace_1915735 : CollatzResearch.WordTrace tailWord_1915735 prefixEnd_1915735 983692861641167411702201 := by
  unfold tailWord_1915735
  simp only [CollatzResearch.WordTrace]
  refine ⟨69872595714626751334860659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46581730476417834223240439 69872595714626751334860659)
  ·
    refine ⟨104808893571940127002290989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69872595714626751334860659 104808893571940127002290989)
    ·
      refine ⟨39303335089477547625859121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104808893571940127002290989 39303335089477547625859121)
      ·
        refine ⟨29477501317108160719394341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39303335089477547625859121 29477501317108160719394341)
        ·
          refine ⟨5527031496957780134886439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29477501317108160719394341 5527031496957780134886439)
          ·
            refine ⟨8290547245436670202329659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527031496957780134886439 8290547245436670202329659)
            ·
              refine ⟨12435820868155005303494489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290547245436670202329659 12435820868155005303494489)
              ·
                refine ⟨9326865651116253977620867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12435820868155005303494489 9326865651116253977620867)
                ·
                  refine ⟨13990298476674380966431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9326865651116253977620867 13990298476674380966431301)
                  ·
                    refine ⟨2623180964376446431205869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13990298476674380966431301 2623180964376446431205869)
                    ·
                      refine ⟨983692861641167411702201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623180964376446431205869 983692861641167411702201)
                      ·
                        rfl

theorem cell23_1915735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1915735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915735 prefixEnd_1915735 := by exact prefixLift 1915735
  have htrace : WordTrace (prefixWord ++ tailWord_1915735) baseStart_1915735 baseEnd_1915735 := by
    simpa [prefixWord, tailWord_1915735, baseEnd_1915735] using wordTrace_append hprefix tailTrace_1915735
  have hstable : (prefixWord ++ tailWord_1915735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915735).length < 2 ^ (prefixWord ++ tailWord_1915735).sum := by decide
  have hdescent : baseEnd_1915735 < baseStart_1915735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915802 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1915802 : Nat := 118140960795 + 1915802 * 2 ^ 59
def prefixEnd_1915802 : Nat := 4983230072969 + 3 ^ 40 * 1915802 * 2
def baseEnd_1915802 : Nat := 327909088281672883188131

theorem tailTrace_1915802 : CollatzResearch.WordTrace tailWord_1915802 prefixEnd_1915802 327909088281672883188131 := by
  unfold tailWord_1915802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468759851346005444387415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46583359603589347851699773 17468759851346005444387415)
  ·
    refine ⟨26203139777019008166581123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17468759851346005444387415 26203139777019008166581123)
    ·
      refine ⟨39304709665528512249871685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26203139777019008166581123 39304709665528512249871685)
      ·
        refine ⟨7369633062286596046850941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39304709665528512249871685 7369633062286596046850941)
        ·
          refine ⟨2763612398357473517569103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7369633062286596046850941 2763612398357473517569103)
          ·
            refine ⟨4145418597536210276353655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763612398357473517569103 4145418597536210276353655)
            ·
              refine ⟨6218127896304315414530483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145418597536210276353655 6218127896304315414530483)
              ·
                refine ⟨9327191844456473121795725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218127896304315414530483 9327191844456473121795725)
                ·
                  refine ⟨3497696941671177420673397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9327191844456473121795725 3497696941671177420673397)
                  ·
                    refine ⟨327909088281672883188131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3497696941671177420673397 327909088281672883188131)
                    ·
                      rfl

theorem cell23_1915802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1915802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915802 prefixEnd_1915802 := by exact prefixLift 1915802
  have htrace : WordTrace (prefixWord ++ tailWord_1915802) baseStart_1915802 baseEnd_1915802 := by
    simpa [prefixWord, tailWord_1915802, baseEnd_1915802] using wordTrace_append hprefix tailTrace_1915802
  have hstable : (prefixWord ++ tailWord_1915802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915802).length < 2 ^ (prefixWord ++ tailWord_1915802).sum := by decide
  have hdescent : baseEnd_1915802 < baseStart_1915802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915809 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1915809 : Nat := 118140960795 + 1915809 * 2 ^ 59
def prefixEnd_1915809 : Nat := 4983230072969 + 3 ^ 40 * 1915809 * 2
def baseEnd_1915809 : Nat := 983730859209600122176861

theorem tailTrace_1915809 : CollatzResearch.WordTrace tailWord_1915809 prefixEnd_1915809 983730859209600122176861 := by
  unfold tailWord_1915809
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875294716358661973054481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46583529810905774648702987 69875294716358661973054481)
  ·
    refine ⟨52406471037268996479790861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69875294716358661973054481 52406471037268996479790861)
    ·
      refine ⟨19652426638975873679921573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52406471037268996479790861 19652426638975873679921573)
      ·
        refine ⟨3684829994807976314985295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19652426638975873679921573 3684829994807976314985295)
        ·
          refine ⟨5527244992211964472477943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684829994807976314985295 5527244992211964472477943)
          ·
            refine ⟨8290867488317946708716915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527244992211964472477943 8290867488317946708716915)
            ·
              refine ⟨12436301232476920063075373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290867488317946708716915 12436301232476920063075373)
              ·
                refine ⟨4663612962178845023653265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12436301232476920063075373 4663612962178845023653265)
                ·
                  refine ⟨3497709721634133767739949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663612962178845023653265 3497709721634133767739949)
                  ·
                    refine ⟨1311641145612800162902481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497709721634133767739949 1311641145612800162902481)
                    ·
                      refine ⟨983730859209600122176861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311641145612800162902481 983730859209600122176861)
                      ·
                        rfl

theorem cell23_1915809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1915809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915809 prefixEnd_1915809 := by exact prefixLift 1915809
  have htrace : WordTrace (prefixWord ++ tailWord_1915809) baseStart_1915809 baseEnd_1915809 := by
    simpa [prefixWord, tailWord_1915809, baseEnd_1915809] using wordTrace_append hprefix tailTrace_1915809
  have hstable : (prefixWord ++ tailWord_1915809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915809).length < 2 ^ (prefixWord ++ tailWord_1915809).sum := by decide
  have hdescent : baseEnd_1915809 < baseStart_1915809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915832 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_1915832 : Nat := 118140960795 + 1915832 * 2 ^ 59
def prefixEnd_1915832 : Nat := 4983230072969 + 3 ^ 40 * 1915832 * 2
def baseEnd_1915832 : Nat := 327914223088217844063085

theorem tailTrace_1915832 : CollatzResearch.WordTrace tailWord_1915832 prefixEnd_1915832 327914223088217844063085 := by
  unfold tailWord_1915832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34938066797637668450570875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46584089063516891267427833 34938066797637668450570875)
  ·
    refine ⟨52407100196456502675856313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34938066797637668450570875 52407100196456502675856313)
    ·
      refine ⟨39305325147342377006892235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52407100196456502675856313 39305325147342377006892235)
      ·
        refine ⟨58957987721013565510338353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39305325147342377006892235 58957987721013565510338353)
        ·
          refine ⟨44218490790760174132753765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58957987721013565510338353 44218490790760174132753765)
          ·
            refine ⟨8290967023267532649891331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44218490790760174132753765 8290967023267532649891331)
            ·
              refine ⟨12436450534901298974836997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290967023267532649891331 12436450534901298974836997)
              ·
                refine ⟨2331834475293993557781937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12436450534901298974836997 2331834475293993557781937)
                ·
                  refine ⟨1748875856470495168336453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2331834475293993557781937 1748875856470495168336453)
                  ·
                    refine ⟨327914223088217844063085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1748875856470495168336453 327914223088217844063085)
                    ·
                      rfl

theorem cell23_1915832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_1915832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915832 prefixEnd_1915832 := by exact prefixLift 1915832
  have htrace : WordTrace (prefixWord ++ tailWord_1915832) baseStart_1915832 baseEnd_1915832 := by
    simpa [prefixWord, tailWord_1915832, baseEnd_1915832] using wordTrace_append hprefix tailTrace_1915832
  have hstable : (prefixWord ++ tailWord_1915832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915832).length < 2 ^ (prefixWord ++ tailWord_1915832).sum := by decide
  have hdescent : baseEnd_1915832 < baseStart_1915832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915833 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 1, 1, 3]
def baseStart_1915833 : Nat := 118140960795 + 1915833 * 2 ^ 59
def prefixEnd_1915833 : Nat := 4983230072969 + 3 ^ 40 * 1915833 * 2
def baseEnd_1915833 : Nat := 983743182745308028276751

theorem tailTrace_1915833 : CollatzResearch.WordTrace tailWord_1915833 prefixEnd_1915833 983743182745308028276751 := by
  unfold tailWord_1915833
  simp only [CollatzResearch.WordTrace]
  refine ⟨69876170068271714071928153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46584113378847809381285435 69876170068271714071928153)
  ·
    refine ⟨52407127551203785553946115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69876170068271714071928153 52407127551203785553946115)
    ·
      refine ⟨78610691326805678330919173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52407127551203785553946115 78610691326805678330919173)
      ·
        refine ⟨14739504623776064687047345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78610691326805678330919173 14739504623776064687047345)
        ·
          refine ⟨11054628467832048515285509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14739504623776064687047345 11054628467832048515285509)
          ·
            refine ⟨2072742837718509096616033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11054628467832048515285509 2072742837718509096616033)
            ·
              refine ⟨1554557128288881822462025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072742837718509096616033 1554557128288881822462025)
              ·
                refine ⟨1165917846216661366846519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554557128288881822462025 1165917846216661366846519)
                ·
                  refine ⟨1748876769324992050269779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165917846216661366846519 1748876769324992050269779)
                  ·
                    refine ⟨2623315153987488075404669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748876769324992050269779 2623315153987488075404669)
                    ·
                      refine ⟨983743182745308028276751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623315153987488075404669 983743182745308028276751)
                      ·
                        rfl

theorem cell23_1915833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_1915833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915833 prefixEnd_1915833 := by exact prefixLift 1915833
  have htrace : WordTrace (prefixWord ++ tailWord_1915833) baseStart_1915833 baseEnd_1915833 := by
    simpa [prefixWord, tailWord_1915833, baseEnd_1915833] using wordTrace_append hprefix tailTrace_1915833
  have hstable : (prefixWord ++ tailWord_1915833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915833).length < 2 ^ (prefixWord ++ tailWord_1915833).sum := by decide
  have hdescent : baseEnd_1915833 < baseStart_1915833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915852 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1915852 : Nat := 118140960795 + 1915852 * 2 ^ 59
def prefixEnd_1915852 : Nat := 4983230072969 + 3 ^ 40 * 1915852 * 2
def baseEnd_1915852 : Nat := 983752938877743453939163

theorem tailTrace_1915852 : CollatzResearch.WordTrace tailWord_1915852 prefixEnd_1915852 983752938877743453939163 := by
  unfold tailWord_1915852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34938431527601440158434905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46584575370135253544579873 34938431527601440158434905)
  ·
    refine ⟨26203823645701080118826179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34938431527601440158434905 26203823645701080118826179)
    ·
      refine ⟨39305735468551620178239269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26203823645701080118826179 39305735468551620178239269)
      ·
        refine ⟨7369825400353428783419863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39305735468551620178239269 7369825400353428783419863)
        ·
          refine ⟨11054738100530143175129795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369825400353428783419863 11054738100530143175129795)
          ·
            refine ⟨16582107150795214762694693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054738100530143175129795 16582107150795214762694693)
            ·
              refine ⟨3109145090774102768005255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16582107150795214762694693 3109145090774102768005255)
              ·
                refine ⟨4663717636161154152007883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109145090774102768005255 4663717636161154152007883)
                ·
                  refine ⟨6995576454241731228011825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663717636161154152007883 6995576454241731228011825)
                  ·
                    refine ⟨5246682340681298421008869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6995576454241731228011825 5246682340681298421008869)
                    ·
                      refine ⟨983752938877743453939163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5246682340681298421008869 983752938877743453939163)
                      ·
                        rfl

theorem cell23_1915852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1915852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915852 prefixEnd_1915852 := by exact prefixLift 1915852
  have htrace : WordTrace (prefixWord ++ tailWord_1915852) baseStart_1915852 baseEnd_1915852 := by
    simpa [prefixWord, tailWord_1915852, baseEnd_1915852] using wordTrace_append hprefix tailTrace_1915852
  have hstable : (prefixWord ++ tailWord_1915852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915852).length < 2 ^ (prefixWord ++ tailWord_1915852).sum := by decide
  have hdescent : baseEnd_1915852 < baseStart_1915852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915889 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_1915889 : Nat := 118140960795 + 1915889 * 2 ^ 59
def prefixEnd_1915889 : Nat := 4983230072969 + 3 ^ 40 * 1915889 * 2
def baseEnd_1915889 : Nat := 983771937661959809176493

theorem tailTrace_1915889 : CollatzResearch.WordTrace tailWord_1915889 prefixEnd_1915889 983771937661959809176493 := by
  unfold tailWord_1915889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69878212556068835635966721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46585475037379223757311147 69878212556068835635966721)
  ·
    refine ⟨52408659417051626726975041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69878212556068835635966721 52408659417051626726975041)
    ·
      refine ⟨39306494562788720045231281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52408659417051626726975041 39306494562788720045231281)
      ·
        refine ⟨29479870922091540033923461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39306494562788720045231281 29479870922091540033923461)
        ·
          refine ⟨5527475797892163756360649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29479870922091540033923461 5527475797892163756360649)
          ·
            refine ⟨4145606848419122817270487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527475797892163756360649 4145606848419122817270487)
            ·
              refine ⟨6218410272628684225905731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145606848419122817270487 6218410272628684225905731)
              ·
                refine ⟨9327615408943026338858597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218410272628684225905731 9327615408943026338858597)
                ·
                  refine ⟨1748927889176817438535987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9327615408943026338858597 1748927889176817438535987)
                  ·
                    refine ⟨2623391833765226157803981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748927889176817438535987 2623391833765226157803981)
                    ·
                      refine ⟨983771937661959809176493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623391833765226157803981 983771937661959809176493)
                      ·
                        rfl

theorem cell23_1915889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_1915889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915889 prefixEnd_1915889 := by exact prefixLift 1915889
  have htrace : WordTrace (prefixWord ++ tailWord_1915889) baseStart_1915889 baseEnd_1915889 := by
    simpa [prefixWord, tailWord_1915889, baseEnd_1915889] using wordTrace_append hprefix tailTrace_1915889
  have hstable : (prefixWord ++ tailWord_1915889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915889).length < 2 ^ (prefixWord ++ tailWord_1915889).sum := by decide
  have hdescent : baseEnd_1915889 < baseStart_1915889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915916 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_1915916 : Nat := 118140960795 + 1915916 * 2 ^ 59
def prefixEnd_1915916 : Nat := 4983230072969 + 3 ^ 40 * 1915916 * 2
def baseEnd_1915916 : Nat := 983785801639631203538869

theorem tailTrace_1915916 : CollatzResearch.WordTrace tailWord_1915916 prefixEnd_1915916 983785801639631203538869 := by
  unfold tailWord_1915916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34939598663485509623599801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46586131551314012831466401 34939598663485509623599801)
  ·
    refine ⟨26204698997614132217699851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34939598663485509623599801 26204698997614132217699851)
    ·
      refine ⟨39307048496421198326549777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26204698997614132217699851 39307048496421198326549777)
      ·
        refine ⟨29480286372315898744912333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39307048496421198326549777 29480286372315898744912333)
        ·
          refine ⟨11055107389618462029342125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29480286372315898744912333 11055107389618462029342125)
          ·
            refine ⟨4145665271106923261003297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11055107389618462029342125 4145665271106923261003297)
            ·
              refine ⟨3109248953330192445752473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145665271106923261003297 3109248953330192445752473)
              ·
                refine ⟨2331936714997644334314355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3109248953330192445752473 2331936714997644334314355)
                ·
                  refine ⟨3497905072496466501471533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331936714997644334314355 3497905072496466501471533)
                  ·
                    refine ⟨1311714402186174938051825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497905072496466501471533 1311714402186174938051825)
                    ·
                      refine ⟨983785801639631203538869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311714402186174938051825 983785801639631203538869)
                      ·
                        rfl

theorem cell23_1915916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_1915916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915916 prefixEnd_1915916 := by exact prefixLift 1915916
  have htrace : WordTrace (prefixWord ++ tailWord_1915916) baseStart_1915916 baseEnd_1915916 := by
    simpa [prefixWord, tailWord_1915916, baseEnd_1915916] using wordTrace_append hprefix tailTrace_1915916
  have hstable : (prefixWord ++ tailWord_1915916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915916).length < 2 ^ (prefixWord ++ tailWord_1915916).sum := by decide
  have hdescent : baseEnd_1915916 < baseStart_1915916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915929 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 4, 2, 2]
def baseStart_1915929 : Nat := 118140960795 + 1915929 * 2 ^ 59
def prefixEnd_1915929 : Nat := 4983230072969 + 3 ^ 40 * 1915929 * 2
def baseEnd_1915929 : Nat := 983792476888139652676309

theorem tailTrace_1915929 : CollatzResearch.WordTrace tailWord_1915929 prefixEnd_1915929 983792476888139652676309 := by
  unfold tailWord_1915929
  simp only [CollatzResearch.WordTrace]
  refine ⟨69879671475923922467422841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46586447650615948311615227 69879671475923922467422841)
  ·
    refine ⟨52409753606942941850567131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69879671475923922467422841 52409753606942941850567131)
    ·
      refine ⟨78614630410414412775850697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52409753606942941850567131 78614630410414412775850697)
      ·
        refine ⟨58960972807810809581888023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78614630410414412775850697 58960972807810809581888023)
        ·
          refine ⟨88441459211716214372832035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58960972807810809581888023 88441459211716214372832035)
          ·
            refine ⟨132662188817574321559248053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88441459211716214372832035 132662188817574321559248053)
            ·
              refine ⟨12437080201647592646179505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132662188817574321559248053 12437080201647592646179505)
              ·
                refine ⟨9327810151235694484634629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437080201647592646179505 9327810151235694484634629)
                ·
                  refine ⟨1748964403356692715868993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9327810151235694484634629 1748964403356692715868993)
                  ·
                    refine ⟨1311723302517519536901745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1748964403356692715868993 1311723302517519536901745)
                    ·
                      refine ⟨983792476888139652676309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311723302517519536901745 983792476888139652676309)
                      ·
                        rfl

theorem cell23_1915929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_1915929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915929 prefixEnd_1915929 := by exact prefixLift 1915929
  have htrace : WordTrace (prefixWord ++ tailWord_1915929) baseStart_1915929 baseEnd_1915929 := by
    simpa [prefixWord, tailWord_1915929, baseEnd_1915929] using wordTrace_append hprefix tailTrace_1915929
  have hstable : (prefixWord ++ tailWord_1915929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915929).length < 2 ^ (prefixWord ++ tailWord_1915929).sum := by decide
  have hdescent : baseEnd_1915929 < baseStart_1915929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
