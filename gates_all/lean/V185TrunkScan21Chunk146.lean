import V185TrunkScan21Chunk145

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1780074 : List Nat := [3, 1, 3, 3, 1, 2, 3, 5]
def baseStart_1780074 : Nat := 118140960795 + 1780074 * 2 ^ 59
def prefixEnd_1780074 : Nat := 4983230072969 + 3 ^ 40 * 1780074 * 2
def baseEnd_1780074 : Nat := 135412379640233138664977

theorem tailTrace_1780074 : CollatzResearch.WordTrace tailWord_1780074 prefixEnd_1780074 135412379640233138664977 := by
  unfold tailWord_1780074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16231158138275846320160819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43283088368735590187095517 16231158138275846320160819)
  ·
    refine ⟨24346737207413769480241229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16231158138275846320160819 24346737207413769480241229)
    ·
      refine ⟨9130026452780163555090461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24346737207413769480241229 9130026452780163555090461)
      ·
        refine ⟨3423759919792561333158923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9130026452780163555090461 3423759919792561333158923)
        ·
          refine ⟨5135639879688841999738385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423759919792561333158923 5135639879688841999738385)
          ·
            refine ⟨3851729909766631499803789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135639879688841999738385 3851729909766631499803789)
            ·
              refine ⟨1444398716162486812426421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3851729909766631499803789 1444398716162486812426421)
              ·
                refine ⟨135412379640233138664977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1444398716162486812426421 135412379640233138664977)
                ·
                  rfl

theorem cell21_1780074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_1780074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780074 prefixEnd_1780074 := by exact prefixLift 1780074
  have htrace : WordTrace (prefixWord ++ tailWord_1780074) baseStart_1780074 baseEnd_1780074 := by
    simpa [prefixWord, tailWord_1780074, baseEnd_1780074] using wordTrace_append hprefix tailTrace_1780074
  have hstable : (prefixWord ++ tailWord_1780074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780074).length < 2 ^ (prefixWord ++ tailWord_1780074).sum := by decide
  have hdescent : baseEnd_1780074 < baseStart_1780074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780330 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1780330 : Nat := 118140960795 + 1780330 * 2 ^ 59
def prefixEnd_1780330 : Nat := 4983230072969 + 3 ^ 40 * 1780330 * 2
def baseEnd_1780330 : Nat := 406295561608499859727741

theorem tailTrace_1780330 : CollatzResearch.WordTrace tailWord_1780330 prefixEnd_1780330 406295561608499859727741 := by
  unfold tailWord_1780330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233492410043985250490611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43289313093450627334641629 16233492410043985250490611)
  ·
    refine ⟨24350238615065977875735917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233492410043985250490611 24350238615065977875735917)
    ·
      refine ⟨9131339480649741703400969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24350238615065977875735917 9131339480649741703400969)
      ·
        refine ⟨6848504610487306277550727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131339480649741703400969 6848504610487306277550727)
        ·
          refine ⟨10272756915730959416326091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848504610487306277550727 10272756915730959416326091)
          ·
            refine ⟨15409135373596439124489137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272756915730959416326091 15409135373596439124489137)
            ·
              refine ⟨11556851530197329343366853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15409135373596439124489137 11556851530197329343366853)
              ·
                refine ⟨2166909661911999251881285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11556851530197329343366853 2166909661911999251881285)
                ·
                  refine ⟨406295561608499859727741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166909661911999251881285 406295561608499859727741)
                  ·
                    rfl

theorem cell21_1780330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1780330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780330 prefixEnd_1780330 := by exact prefixLift 1780330
  have htrace : WordTrace (prefixWord ++ tailWord_1780330) baseStart_1780330 baseEnd_1780330 := by
    simpa [prefixWord, tailWord_1780330, baseEnd_1780330] using wordTrace_append hprefix tailTrace_1780330
  have hstable : (prefixWord ++ tailWord_1780330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780330).length < 2 ^ (prefixWord ++ tailWord_1780330).sum := by decide
  have hdescent : baseEnd_1780330 < baseStart_1780330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780437 : List Nat := [1, 3, 2, 5, 1, 1, 8]
def baseStart_1780437 : Nat := 118140960795 + 1780437 * 2 ^ 59
def prefixEnd_1780437 : Nat := 4983230072969 + 3 ^ 40 * 1780437 * 2
def baseEnd_1780437 : Nat := 45146664496254605716021

theorem tailTrace_1780437 : CollatzResearch.WordTrace tailWord_1780437 prefixEnd_1780437 45146664496254605716021 := by
  unfold tailWord_1780437
  simp only [CollatzResearch.WordTrace]
  refine ⟨64937872250788298276107565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43291914833858865517405043 64937872250788298276107565)
  ·
    refine ⟨24351702094045611853540337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64937872250788298276107565 24351702094045611853540337)
    ·
      refine ⟨18263776570534208890155253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24351702094045611853540337 18263776570534208890155253)
      ·
        refine ⟨1712229053487582083452055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18263776570534208890155253 1712229053487582083452055)
        ·
          refine ⟨2568343580231373125178083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712229053487582083452055 2568343580231373125178083)
          ·
            refine ⟨3852515370347059687767125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568343580231373125178083 3852515370347059687767125)
            ·
              refine ⟨45146664496254605716021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3852515370347059687767125 45146664496254605716021)
              ·
                rfl

theorem cell21_1780437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 8].length) (baseStart_1780437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780437 prefixEnd_1780437 := by exact prefixLift 1780437
  have htrace : WordTrace (prefixWord ++ tailWord_1780437) baseStart_1780437 baseEnd_1780437 := by
    simpa [prefixWord, tailWord_1780437, baseEnd_1780437] using wordTrace_append hprefix tailTrace_1780437
  have hstable : (prefixWord ++ tailWord_1780437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780437).length < 2 ^ (prefixWord ++ tailWord_1780437).sum := by decide
  have hdescent : baseEnd_1780437 < baseStart_1780437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780451 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_1780451 : Nat := 118140960795 + 1780451 * 2 ^ 59
def prefixEnd_1780451 : Nat := 4983230072969 + 3 ^ 40 * 1780451 * 2
def baseEnd_1780451 : Nat := 406323175457030538210827

theorem tailTrace_1780451 : CollatzResearch.WordTrace tailWord_1780451 prefixEnd_1780451 406323175457030538210827 := by
  unfold tailWord_1780451
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938382872737578667117207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292255248491719111411471 64938382872737578667117207)
  ·
    refine ⟨97407574309106368000675811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64938382872737578667117207 97407574309106368000675811)
    ·
      refine ⟨146111361463659552001013717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97407574309106368000675811 146111361463659552001013717)
      ·
        refine ⟨3424485034304520750023759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 146111361463659552001013717 3424485034304520750023759)
        ·
          refine ⟨5136727551456781125035639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424485034304520750023759 5136727551456781125035639)
          ·
            refine ⟨7705091327185171687553459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136727551456781125035639 7705091327185171687553459)
            ·
              refine ⟨11557636990777757531330189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705091327185171687553459 11557636990777757531330189)
              ·
                refine ⟨4334113871541659074248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11557636990777757531330189 4334113871541659074248821)
                ·
                  refine ⟨406323175457030538210827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4334113871541659074248821 406323175457030538210827)
                  ·
                    rfl

theorem cell21_1780451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_1780451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780451 prefixEnd_1780451 := by exact prefixLift 1780451
  have htrace : WordTrace (prefixWord ++ tailWord_1780451) baseStart_1780451 baseEnd_1780451 := by
    simpa [prefixWord, tailWord_1780451, baseEnd_1780451] using wordTrace_append hprefix tailTrace_1780451
  have hstable : (prefixWord ++ tailWord_1780451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780451).length < 2 ^ (prefixWord ++ tailWord_1780451).sum := by decide
  have hdescent : baseEnd_1780451 < baseStart_1780451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780482 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1780482 : Nat := 118140960795 + 1780482 * 2 ^ 59
def prefixEnd_1780482 : Nat := 4983230072969 + 3 ^ 40 * 1780482 * 2
def baseEnd_1780482 : Nat := 406330250079381373194097

theorem tailTrace_1780482 : CollatzResearch.WordTrace tailWord_1780482 prefixEnd_1780482 406330250079381373194097 := by
  unfold tailWord_1780482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234878383906317740373925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43293009023750180640997133 16234878383906317740373925)
  ·
    refine ⟨3044039696982434576320111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16234878383906317740373925 3044039696982434576320111)
    ·
      refine ⟨4566059545473651864480167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044039696982434576320111 4566059545473651864480167)
      ·
        refine ⟨6849089318210477796720251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566059545473651864480167 6849089318210477796720251)
        ·
          refine ⟨10273633977315716695080377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849089318210477796720251 10273633977315716695080377)
          ·
            refine ⟨7705225482986787521310283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273633977315716695080377 7705225482986787521310283)
            ·
              refine ⟨11557838224480181281965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705225482986787521310283 11557838224480181281965425)
              ·
                refine ⟨8668378668360135961474069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11557838224480181281965425 8668378668360135961474069)
                ·
                  refine ⟨406330250079381373194097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8668378668360135961474069 406330250079381373194097)
                  ·
                    rfl

theorem cell21_1780482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1780482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780482 prefixEnd_1780482 := by exact prefixLift 1780482
  have htrace : WordTrace (prefixWord ++ tailWord_1780482) baseStart_1780482 baseEnd_1780482 := by
    simpa [prefixWord, tailWord_1780482, baseEnd_1780482] using wordTrace_append hprefix tailTrace_1780482
  have hstable : (prefixWord ++ tailWord_1780482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780482).length < 2 ^ (prefixWord ++ tailWord_1780482).sum := by decide
  have hdescent : baseEnd_1780482 < baseStart_1780482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780516 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_1780516 : Nat := 118140960795 + 1780516 * 2 ^ 59
def prefixEnd_1780516 : Nat := 4983230072969 + 3 ^ 40 * 1780516 * 2
def baseEnd_1780516 : Nat := 406338009342604869627361

theorem tailTrace_1780516 : CollatzResearch.WordTrace tailWord_1780516 prefixEnd_1780516 406338009342604869627361 := by
  unfold tailWord_1780516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470376808751047384116701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43293835745001396512155601 32470376808751047384116701)
  ·
    refine ⟨12176391303281642769043763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32470376808751047384116701 12176391303281642769043763)
    ·
      refine ⟨18264586954922464153565645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176391303281642769043763 18264586954922464153565645)
      ·
        refine ⟨6849220108095924057587117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18264586954922464153565645 6849220108095924057587117)
        ·
          refine ⟨2568457540535971521595169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6849220108095924057587117 2568457540535971521595169)
          ·
            refine ⟨1926343155401978641196377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2568457540535971521595169 1926343155401978641196377)
            ·
              refine ⟨1444757366551483980897283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926343155401978641196377 1444757366551483980897283)
              ·
                refine ⟨2167136049827225971345925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444757366551483980897283 2167136049827225971345925)
                ·
                  refine ⟨406338009342604869627361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167136049827225971345925 406338009342604869627361)
                  ·
                    rfl

theorem cell21_1780516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_1780516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780516 prefixEnd_1780516 := by exact prefixLift 1780516
  have htrace : WordTrace (prefixWord ++ tailWord_1780516) baseStart_1780516 baseEnd_1780516 := by
    simpa [prefixWord, tailWord_1780516, baseEnd_1780516] using wordTrace_append hprefix tailTrace_1780516
  have hstable : (prefixWord ++ tailWord_1780516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780516).length < 2 ^ (prefixWord ++ tailWord_1780516).sum := by decide
  have hdescent : baseEnd_1780516 < baseStart_1780516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780603 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 3]
def baseStart_1780603 : Nat := 118140960795 + 1780603 * 2 ^ 59
def prefixEnd_1780603 : Nat := 4983230072969 + 3 ^ 40 * 1780603 * 2
def baseEnd_1780603 : Nat := 406357863927912051677183

theorem tailTrace_1780603 : CollatzResearch.WordTrace tailWord_1780603 prefixEnd_1780603 406357863927912051677183 := by
  unfold tailWord_1780603
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943926768186908626650463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43295951178791272417766975 64943926768186908626650463)
  ·
    refine ⟨97415890152280362939975695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64943926768186908626650463 97415890152280362939975695)
    ·
      refine ⟨146123835228420544409963543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97415890152280362939975695 146123835228420544409963543)
      ·
        refine ⟨219185752842630816614945315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146123835228420544409963543 219185752842630816614945315)
        ·
          refine ⟨328778629263946224922417973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219185752842630816614945315 328778629263946224922417973)
          ·
            refine ⟨30822996493494958586476685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328778629263946224922417973 30822996493494958586476685)
            ·
              refine ⟨11558623685060609469928757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30822996493494958586476685 11558623685060609469928757)
              ·
                refine ⟨1083620970474432137805821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11558623685060609469928757 1083620970474432137805821)
                ·
                  refine ⟨406357863927912051677183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083620970474432137805821 406357863927912051677183)
                  ·
                    rfl

theorem cell21_1780603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].length) (baseStart_1780603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780603 prefixEnd_1780603 := by exact prefixLift 1780603
  have htrace : WordTrace (prefixWord ++ tailWord_1780603) baseStart_1780603 baseEnd_1780603 := by
    simpa [prefixWord, tailWord_1780603, baseEnd_1780603] using wordTrace_append hprefix tailTrace_1780603
  have hstable : (prefixWord ++ tailWord_1780603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780603).length < 2 ^ (prefixWord ++ tailWord_1780603).sum := by decide
  have hdescent : baseEnd_1780603 < baseStart_1780603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780617 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_1780617 : Nat := 118140960795 + 1780617 * 2 ^ 59
def prefixEnd_1780617 : Nat := 4983230072969 + 3 ^ 40 * 1780617 * 2
def baseEnd_1780617 : Nat := 406361058918651138443821

theorem tailTrace_1780617 : CollatzResearch.WordTrace tailWord_1780617 prefixEnd_1780617 406361058918651138443821 := by
  unfold tailWord_1780617
  simp only [CollatzResearch.WordTrace]
  refine ⟨64944437390136189017660105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43296291593424126011773403 64944437390136189017660105)
  ·
    refine ⟨48708328042602141763245079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64944437390136189017660105 48708328042602141763245079)
    ·
      refine ⟨73062492063903212644867619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48708328042602141763245079 73062492063903212644867619)
      ·
        refine ⟨109593738095854818967301429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73062492063903212644867619 109593738095854818967301429)
        ·
          refine ⟨10274412946486389278184509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109593738095854818967301429 10274412946486389278184509)
          ·
            refine ⟨3852904854932395979319191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10274412946486389278184509 3852904854932395979319191)
            ·
              refine ⟨5779357282398593968978787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852904854932395979319191 5779357282398593968978787)
              ·
                refine ⟨8669035923597890953468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779357282398593968978787 8669035923597890953468181)
                ·
                  refine ⟨406361058918651138443821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8669035923597890953468181 406361058918651138443821)
                  ·
                    rfl

theorem cell21_1780617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_1780617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780617 prefixEnd_1780617 := by exact prefixLift 1780617
  have htrace : WordTrace (prefixWord ++ tailWord_1780617) baseStart_1780617 baseEnd_1780617 := by
    simpa [prefixWord, tailWord_1780617, baseEnd_1780617] using wordTrace_append hprefix tailTrace_1780617
  have hstable : (prefixWord ++ tailWord_1780617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780617).length < 2 ^ (prefixWord ++ tailWord_1780617).sum := by decide
  have hdescent : baseEnd_1780617 < baseStart_1780617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780631 : List Nat := [1, 1, 3, 3, 1, 2, 2, 8]
def baseStart_1780631 : Nat := 118140960795 + 1780631 * 2 ^ 59
def prefixEnd_1780631 : Nat := 4983230072969 + 3 ^ 40 * 1780631 * 2
def baseEnd_1780631 : Nat := 135454751303130075070153

theorem tailTrace_1780631 : CollatzResearch.WordTrace tailWord_1780631 prefixEnd_1780631 135454751303130075070153 := by
  unfold tailWord_1780631
  simp only [CollatzResearch.WordTrace]
  refine ⟨64944948012085469408669747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43296632008056979605779831 64944948012085469408669747)
  ·
    refine ⟨97417422018128204113004621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64944948012085469408669747 97417422018128204113004621)
    ·
      refine ⟨36531533256798076542376733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97417422018128204113004621 36531533256798076542376733)
      ·
        refine ⟨13699324971299278703391275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36531533256798076542376733 13699324971299278703391275)
        ·
          refine ⟨20548987456948918055086913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699324971299278703391275 20548987456948918055086913)
          ·
            refine ⟨15411740592711688541315185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20548987456948918055086913 15411740592711688541315185)
            ·
              refine ⟨11558805444533766405986389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15411740592711688541315185 11558805444533766405986389)
              ·
                refine ⟨135454751303130075070153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11558805444533766405986389 135454751303130075070153)
                ·
                  rfl

theorem cell21_1780631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_1780631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780631 prefixEnd_1780631 := by exact prefixLift 1780631
  have htrace : WordTrace (prefixWord ++ tailWord_1780631) baseStart_1780631 baseEnd_1780631 := by
    simpa [prefixWord, tailWord_1780631, baseEnd_1780631] using wordTrace_append hprefix tailTrace_1780631
  have hstable : (prefixWord ++ tailWord_1780631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780631).length < 2 ^ (prefixWord ++ tailWord_1780631).sum := by decide
  have hdescent : baseEnd_1780631 < baseStart_1780631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780679 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 3]
def baseStart_1780679 : Nat := 118140960795 + 1780679 * 2 ^ 59
def prefixEnd_1780679 : Nat := 4983230072969 + 3 ^ 40 * 1780679 * 2
def baseEnd_1780679 : Nat := 406375208163352808410361

theorem tailTrace_1780679 : CollatzResearch.WordTrace tailWord_1780679 prefixEnd_1780679 406375208163352808410361 := by
  unfold tailWord_1780679
  simp only [CollatzResearch.WordTrace]
  refine ⟨64946698715911573606417091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43297799143941049070944727 64946698715911573606417091)
  ·
    refine ⟨97420048073867360409625637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64946698715911573606417091 97420048073867360409625637)
    ·
      refine ⟨18266259013850130076804807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97420048073867360409625637 18266259013850130076804807)
      ·
        refine ⟨27399388520775195115207211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18266259013850130076804807 27399388520775195115207211)
        ·
          refine ⟨41099082781162792672810817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27399388520775195115207211 41099082781162792672810817)
          ·
            refine ⟨30824312085872094504608113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41099082781162792672810817 30824312085872094504608113)
            ·
              refine ⟨23118234064404070878456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30824312085872094504608113 23118234064404070878456085)
              ·
                refine ⟨1083667221768940822427629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23118234064404070878456085 1083667221768940822427629)
                ·
                  refine ⟨406375208163352808410361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083667221768940822427629 406375208163352808410361)
                  ·
                    rfl

theorem cell21_1780679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].length) (baseStart_1780679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780679 prefixEnd_1780679 := by exact prefixLift 1780679
  have htrace : WordTrace (prefixWord ++ tailWord_1780679) baseStart_1780679 baseEnd_1780679 := by
    simpa [prefixWord, tailWord_1780679, baseEnd_1780679] using wordTrace_append hprefix tailTrace_1780679
  have hstable : (prefixWord ++ tailWord_1780679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780679).length < 2 ^ (prefixWord ++ tailWord_1780679).sum := by decide
  have hdescent : baseEnd_1780679 < baseStart_1780679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780685 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1780685 : Nat := 118140960795 + 1780685 * 2 ^ 59
def prefixEnd_1780685 : Nat := 4983230072969 + 3 ^ 40 * 1780685 * 2
def baseEnd_1780685 : Nat := 406376577445098131310349

theorem tailTrace_1780685 : CollatzResearch.WordTrace tailWord_1780685 prefixEnd_1780685 406376577445098131310349 := by
  unfold tailWord_1780685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64946917553889836631135509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43297945035926557754090339 64946917553889836631135509)
  ·
    refine ⟨3044386760338586092084477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64946917553889836631135509 3044386760338586092084477)
    ·
      refine ⟨1141645035126969784531679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3044386760338586092084477 1141645035126969784531679)
      ·
        refine ⟨1712467552690454676797519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141645035126969784531679 1712467552690454676797519)
        ·
          refine ⟨2568701329035682015196279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712467552690454676797519 2568701329035682015196279)
          ·
            refine ⟨3853051993553523022794419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568701329035682015196279 3853051993553523022794419)
            ·
              refine ⟨5779577990330284534191629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853051993553523022794419 5779577990330284534191629)
              ·
                refine ⟨2167341746373856700321861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5779577990330284534191629 2167341746373856700321861)
                ·
                  refine ⟨406376577445098131310349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167341746373856700321861 406376577445098131310349)
                  ·
                    rfl

theorem cell21_1780685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1780685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780685 prefixEnd_1780685 := by exact prefixLift 1780685
  have htrace : WordTrace (prefixWord ++ tailWord_1780685) baseStart_1780685 baseEnd_1780685 := by
    simpa [prefixWord, tailWord_1780685, baseEnd_1780685] using wordTrace_append hprefix tailTrace_1780685
  have hstable : (prefixWord ++ tailWord_1780685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780685).length < 2 ^ (prefixWord ++ tailWord_1780685).sum := by decide
  have hdescent : baseEnd_1780685 < baseStart_1780685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780707 : List Nat := [1, 1, 1, 6, 1, 1, 1, 9]
def baseStart_1780707 : Nat := 118140960795 + 1780707 * 2 ^ 59
def prefixEnd_1780707 : Nat := 4983230072969 + 3 ^ 40 * 1780707 * 2
def baseEnd_1780707 : Nat := 135460532714943660647879

theorem tailTrace_1780707 : CollatzResearch.WordTrace tailWord_1780707 prefixEnd_1780707 135460532714943660647879 := by
  unfold tailWord_1780707
  simp only [CollatzResearch.WordTrace]
  refine ⟨64947719959810134388436375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43298479973206756258957583 64947719959810134388436375)
  ·
    refine ⟨97421579939715201582654563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64947719959810134388436375 97421579939715201582654563)
    ·
      refine ⟨146132369909572802373981845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97421579939715201582654563 146132369909572802373981845)
      ·
        refine ⟨6849954839511225111280399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146132369909572802373981845 6849954839511225111280399)
        ·
          refine ⟨10274932259266837666920599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849954839511225111280399 10274932259266837666920599)
          ·
            refine ⟨15412398388900256500380899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10274932259266837666920599 15412398388900256500380899)
            ·
              refine ⟨23118597583350384750571349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15412398388900256500380899 23118597583350384750571349)
              ·
                refine ⟨135460532714943660647879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23118597583350384750571349 135460532714943660647879)
                ·
                  rfl

theorem cell21_1780707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_1780707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780707 prefixEnd_1780707 := by exact prefixLift 1780707
  have htrace : WordTrace (prefixWord ++ tailWord_1780707) baseStart_1780707 baseEnd_1780707 := by
    simpa [prefixWord, tailWord_1780707, baseEnd_1780707] using wordTrace_append hprefix tailTrace_1780707
  have hstable : (prefixWord ++ tailWord_1780707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780707).length < 2 ^ (prefixWord ++ tailWord_1780707).sum := by decide
  have hdescent : baseEnd_1780707 < baseStart_1780707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780772 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1780772 : Nat := 118140960795 + 1780772 * 2 ^ 59
def prefixEnd_1780772 : Nat := 4983230072969 + 3 ^ 40 * 1780772 * 2
def baseEnd_1780772 : Nat := 406396432030405313360171

theorem tailTrace_1780772 : CollatzResearch.WordTrace tailWord_1780772 prefixEnd_1780772 406396432030405313360171 := by
  unfold tailWord_1780772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475045352287325244776285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43300060469716433659701713 32475045352287325244776285)
  ·
    refine ⟨12178142007107746966791107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32475045352287325244776285 12178142007107746966791107)
    ·
      refine ⟨18267213010661620450186661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178142007107746966791107 18267213010661620450186661)
      ·
        refine ⟨3425102439499053834409999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18267213010661620450186661 3425102439499053834409999)
        ·
          refine ⟨5137653659248580751614999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425102439499053834409999 5137653659248580751614999)
          ·
            refine ⟨7706480488872871127422499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137653659248580751614999 7706480488872871127422499)
            ·
              refine ⟨11559720733309306691133749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7706480488872871127422499 11559720733309306691133749)
              ·
                refine ⟨1083723818747747502293789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11559720733309306691133749 1083723818747747502293789)
                ·
                  refine ⟨406396432030405313360171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083723818747747502293789 406396432030405313360171)
                  ·
                    rfl

theorem cell21_1780772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1780772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780772 prefixEnd_1780772 := by exact prefixLift 1780772
  have htrace : WordTrace (prefixWord ++ tailWord_1780772) baseStart_1780772 baseEnd_1780772 := by
    simpa [prefixWord, tailWord_1780772, baseEnd_1780772] using wordTrace_append hprefix tailTrace_1780772
  have hstable : (prefixWord ++ tailWord_1780772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780772).length < 2 ^ (prefixWord ++ tailWord_1780772).sum := by decide
  have hdescent : baseEnd_1780772 < baseStart_1780772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780814 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1780814 : Nat := 118140960795 + 1780814 * 2 ^ 59
def prefixEnd_1780814 : Nat := 4983230072969 + 3 ^ 40 * 1780814 * 2
def baseEnd_1780814 : Nat := 406406017002622573660085

theorem tailTrace_1780814 : CollatzResearch.WordTrace tailWord_1780814 prefixEnd_1780814 406406017002622573660085 := by
  unfold tailWord_1780814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118952821302811457822687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43301081713614994441720997 8118952821302811457822687)
  ·
    refine ⟨12178429231954217186734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118952821302811457822687 12178429231954217186734031)
    ·
      refine ⟨18267643847931325780101047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178429231954217186734031 18267643847931325780101047)
      ·
        refine ⟨27401465771896988670151571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18267643847931325780101047 27401465771896988670151571)
        ·
          refine ⟨41102198657845483005227357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27401465771896988670151571 41102198657845483005227357)
          ·
            refine ⟨15413324496692056126960259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41102198657845483005227357 15413324496692056126960259)
            ·
              refine ⟨23119986745038084190440389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15413324496692056126960259 23119986745038084190440389)
              ·
                refine ⟨4334997514694640785707573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23119986745038084190440389 4334997514694640785707573)
                ·
                  refine ⟨406406017002622573660085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4334997514694640785707573 406406017002622573660085)
                  ·
                    rfl

theorem cell21_1780814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1780814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780814 prefixEnd_1780814 := by exact prefixLift 1780814
  have htrace : WordTrace (prefixWord ++ tailWord_1780814) baseStart_1780814 baseEnd_1780814 := by
    simpa [prefixWord, tailWord_1780814, baseEnd_1780814] using wordTrace_append hprefix tailTrace_1780814
  have hstable : (prefixWord ++ tailWord_1780814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780814).length < 2 ^ (prefixWord ++ tailWord_1780814).sum := by decide
  have hdescent : baseEnd_1780814 < baseStart_1780814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780845 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1780845 : Nat := 118140960795 + 1780845 * 2 ^ 59
def prefixEnd_1780845 : Nat := 4983230072969 + 3 ^ 40 * 1780845 * 2
def baseEnd_1780845 : Nat := 406413091624973408643355

theorem tailTrace_1780845 : CollatzResearch.WordTrace tailWord_1780845 prefixEnd_1780845 406413091624973408643355 := by
  unfold tailWord_1780845
  simp only [CollatzResearch.WordTrace]
  refine ⟨64952753233310183956959989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43301835488873455971306659 64952753233310183956959989)
  ·
    refine ⟨6089320615622829745964999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64952753233310183956959989 6089320615622829745964999)
    ·
      refine ⟨9133980923434244618947499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089320615622829745964999 9133980923434244618947499)
      ·
        refine ⟨13700971385151366928421249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133980923434244618947499 13700971385151366928421249)
        ·
          refine ⟨10275728538863525196315937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13700971385151366928421249 10275728538863525196315937)
          ·
            refine ⟨7706796404147643897236953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10275728538863525196315937 7706796404147643897236953)
            ·
              refine ⟨5780097303110732922927715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7706796404147643897236953 5780097303110732922927715)
              ·
                refine ⟨8670145954666099384391573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780097303110732922927715 8670145954666099384391573)
                ·
                  refine ⟨406413091624973408643355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8670145954666099384391573 406413091624973408643355)
                  ·
                    rfl

theorem cell21_1780845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1780845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780845 prefixEnd_1780845 := by exact prefixLift 1780845
  have htrace : WordTrace (prefixWord ++ tailWord_1780845) baseStart_1780845 baseEnd_1780845 := by
    simpa [prefixWord, tailWord_1780845, baseEnd_1780845] using wordTrace_append hprefix tailTrace_1780845
  have hstable : (prefixWord ++ tailWord_1780845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780845).length < 2 ^ (prefixWord ++ tailWord_1780845).sum := by decide
  have hdescent : baseEnd_1780845 < baseStart_1780845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780848 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_1780848 : Nat := 118140960795 + 1780848 * 2 ^ 59
def prefixEnd_1780848 : Nat := 4983230072969 + 3 ^ 40 * 1780848 * 2
def baseEnd_1780848 : Nat := 406413776265846070093349

theorem tailTrace_1780848 : CollatzResearch.WordTrace tailWord_1780848 prefixEnd_1780848 406413776265846070093349 := by
  unfold tailWord_1780848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476431326149657734659599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43301908434866210312879465 32476431326149657734659599)
  ·
    refine ⟨48714646989224486601989399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32476431326149657734659599 48714646989224486601989399)
    ·
      refine ⟨73071970483836729902984099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48714646989224486601989399 73071970483836729902984099)
      ·
        refine ⟨109607955725755094854476149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73071970483836729902984099 109607955725755094854476149)
        ·
          refine ⟨10275745849289540142607139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109607955725755094854476149 10275745849289540142607139)
          ·
            refine ⟨15413618773934310213910709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275745849289540142607139 15413618773934310213910709)
            ·
              refine ⟨1445026760056341582554129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15413618773934310213910709 1445026760056341582554129)
              ·
                refine ⟨1083770070042256186915597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445026760056341582554129 1083770070042256186915597)
                ·
                  refine ⟨406413776265846070093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083770070042256186915597 406413776265846070093349)
                  ·
                    rfl

theorem cell21_1780848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_1780848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780848 prefixEnd_1780848 := by exact prefixLift 1780848
  have htrace : WordTrace (prefixWord ++ tailWord_1780848) baseStart_1780848 baseEnd_1780848 := by
    simpa [prefixWord, tailWord_1780848, baseEnd_1780848] using wordTrace_append hprefix tailTrace_1780848
  have hstable : (prefixWord ++ tailWord_1780848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780848).length < 2 ^ (prefixWord ++ tailWord_1780848).sum := by decide
  have hdescent : baseEnd_1780848 < baseStart_1780848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780921 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_1780921 : Nat := 118140960795 + 1780921 * 2 ^ 59
def prefixEnd_1780921 : Nat := 4983230072969 + 3 ^ 40 * 1780921 * 2
def baseEnd_1780921 : Nat := 406430435860414165376533

theorem tailTrace_1780921 : CollatzResearch.WordTrace tailWord_1780921 prefixEnd_1780921 406430435860414165376533 := by
  unfold tailWord_1780921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64955525181034848936726617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43303683454023232624484411 64955525181034848936726617)
  ·
    refine ⟨48716643885776136702544963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64955525181034848936726617 48716643885776136702544963)
    ·
      refine ⟨73074965828664205053817445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48716643885776136702544963 73074965828664205053817445)
      ·
        refine ⟨13701556092874538447590771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73074965828664205053817445 13701556092874538447590771)
        ·
          refine ⟨20552334139311807671386157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701556092874538447590771 20552334139311807671386157)
          ·
            refine ⟨7707125302241927876769809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20552334139311807671386157 7707125302241927876769809)
            ·
              refine ⟨5780343976681445907577357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707125302241927876769809 5780343976681445907577357)
              ·
                refine ⟨2167628991255542215341509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780343976681445907577357 2167628991255542215341509)
                ·
                  refine ⟨406430435860414165376533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167628991255542215341509 406430435860414165376533)
                  ·
                    rfl

theorem cell21_1780921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_1780921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780921 prefixEnd_1780921 := by exact prefixLift 1780921
  have htrace : WordTrace (prefixWord ++ tailWord_1780921) baseStart_1780921 baseEnd_1780921 := by
    simpa [prefixWord, tailWord_1780921, baseEnd_1780921] using wordTrace_append hprefix tailTrace_1780921
  have hstable : (prefixWord ++ tailWord_1780921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780921).length < 2 ^ (prefixWord ++ tailWord_1780921).sum := by decide
  have hdescent : baseEnd_1780921 < baseStart_1780921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781062 : List Nat := [6, 1, 1, 3, 2, 8]
def baseStart_1781062 : Nat := 118140960795 + 1781062 * 2 ^ 59
def prefixEnd_1781062 : Nat := 4983230072969 + 3 ^ 40 * 1781062 * 2
def baseEnd_1781062 : Nat := 15054170888201083463935

theorem tailTrace_1781062 : CollatzResearch.WordTrace tailWord_1781062 prefixEnd_1781062 15054170888201083463935 := by
  unfold tailWord_1781062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030020871047625938050295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43307111915682686678406293 2030020871047625938050295)
  ·
    refine ⟨3045031306571438907075443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030020871047625938050295 3045031306571438907075443)
    ·
      refine ⟨4567546959857158360613165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045031306571438907075443 4567546959857158360613165)
      ·
        refine ⟨1712830109946434385229937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4567546959857158360613165 1712830109946434385229937)
        ·
          refine ⟨1284622582459825788922453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1712830109946434385229937 1284622582459825788922453)
          ·
            refine ⟨15054170888201083463935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1284622582459825788922453 15054170888201083463935)
            ·
              rfl

theorem cell21_1781062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 8].length) (baseStart_1781062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781062 prefixEnd_1781062 := by exact prefixLift 1781062
  have htrace : WordTrace (prefixWord ++ tailWord_1781062) baseStart_1781062 baseEnd_1781062 := by
    simpa [prefixWord, tailWord_1781062, baseEnd_1781062] using wordTrace_append hprefix tailTrace_1781062
  have hstable : (prefixWord ++ tailWord_1781062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781062).length < 2 ^ (prefixWord ++ tailWord_1781062).sum := by decide
  have hdescent : baseEnd_1781062 < baseStart_1781062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781073 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_1781073 : Nat := 118140960795 + 1781073 * 2 ^ 59
def prefixEnd_1781073 : Nat := 4983230072969 + 3 ^ 40 * 1781073 * 2
def baseEnd_1781073 : Nat := 406465124331295678842889

theorem tailTrace_1781073 : CollatzResearch.WordTrace tailWord_1781073 prefixEnd_1781073 406465124331295678842889 := by
  unfold tailWord_1781073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64961069076484178896259873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43307379384322785930839915 64961069076484178896259873)
  ·
    refine ⟨48720801807363134172194905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64961069076484178896259873 48720801807363134172194905)
    ·
      refine ⟨36540601355522350629146179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48720801807363134172194905 36540601355522350629146179)
      ·
        refine ⟨54810902033283525943719269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36540601355522350629146179 54810902033283525943719269)
        ·
          refine ⟨10277044131240661114447363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54810902033283525943719269 10277044131240661114447363)
          ·
            refine ⟨15415566196860991671671045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277044131240661114447363 15415566196860991671671045)
            ·
              refine ⟨2890418661911435938438321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15415566196860991671671045 2890418661911435938438321)
              ·
                refine ⟨2167813996433576953828741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890418661911435938438321 2167813996433576953828741)
                ·
                  refine ⟨406465124331295678842889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167813996433576953828741 406465124331295678842889)
                  ·
                    rfl

theorem cell21_1781073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_1781073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781073 prefixEnd_1781073 := by exact prefixLift 1781073
  have htrace : WordTrace (prefixWord ++ tailWord_1781073) baseStart_1781073 baseEnd_1781073 := by
    simpa [prefixWord, tailWord_1781073, baseEnd_1781073] using wordTrace_append hprefix tailTrace_1781073
  have hstable : (prefixWord ++ tailWord_1781073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781073).length < 2 ^ (prefixWord ++ tailWord_1781073).sum := by decide
  have hdescent : baseEnd_1781073 < baseStart_1781073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781132 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1781132 : Nat := 118140960795 + 1781132 * 2 ^ 59
def prefixEnd_1781132 : Nat := 4983230072969 + 3 ^ 40 * 1781132 * 2
def baseEnd_1781132 : Nat := 406478588935124687359435

theorem tailTrace_1781132 : CollatzResearch.WordTrace tailWord_1781132 prefixEnd_1781132 406478588935124687359435 := by
  unfold tailWord_1781132
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481610491635215986328825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43308813988846954648438433 32481610491635215986328825)
  ·
    refine ⟨24361207868726411989746619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32481610491635215986328825 24361207868726411989746619)
    ·
      refine ⟨36541811803089617984619929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24361207868726411989746619 36541811803089617984619929)
      ·
        refine ⟨27406358852317213488464947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36541811803089617984619929 27406358852317213488464947)
        ·
          refine ⟨41109538278475820232697421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27406358852317213488464947 41109538278475820232697421)
          ·
            refine ⟨15416076854428432587261533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41109538278475820232697421 15416076854428432587261533)
            ·
              refine ⟨5781028820410662220223075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15416076854428432587261533 5781028820410662220223075)
              ·
                refine ⟨8671543230615993330334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781028820410662220223075 8671543230615993330334613)
                ·
                  refine ⟨406478588935124687359435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8671543230615993330334613 406478588935124687359435)
                  ·
                    rfl

theorem cell21_1781132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1781132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781132 prefixEnd_1781132 := by exact prefixLift 1781132
  have htrace : WordTrace (prefixWord ++ tailWord_1781132) baseStart_1781132 baseEnd_1781132 := by
    simpa [prefixWord, tailWord_1781132, baseEnd_1781132] using wordTrace_append hprefix tailTrace_1781132
  have hstable : (prefixWord ++ tailWord_1781132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781132).length < 2 ^ (prefixWord ++ tailWord_1781132).sum := by decide
  have hdescent : baseEnd_1781132 < baseStart_1781132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781180 : List Nat := [2, 2, 2, 4, 2, 2, 7]
def baseStart_1781180 : Nat := 118140960795 + 1781180 * 2 ^ 59
def prefixEnd_1781180 : Nat := 4983230072969 + 3 ^ 40 * 1781180 * 2
def baseEnd_1781180 : Nat := 45165504798787474506593

theorem tailTrace_1781180 : CollatzResearch.WordTrace tailWord_1781180 prefixEnd_1781180 45165504798787474506593 := by
  unfold tailWord_1781180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32482485843548268085202497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43309981124731024113603329 32482485843548268085202497)
  ·
    refine ⟨24361864382661201063901873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32482485843548268085202497 24361864382661201063901873)
    ·
      refine ⟨18271398286995900797926405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24361864382661201063901873 18271398286995900797926405)
      ·
        refine ⟨3425887178811731399611201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18271398286995900797926405 3425887178811731399611201)
        ·
          refine ⟨2569415384108798549708401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425887178811731399611201 2569415384108798549708401)
          ·
            refine ⟨1927061538081598912281301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2569415384108798549708401 1927061538081598912281301)
            ·
              refine ⟨45165504798787474506593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1927061538081598912281301 45165504798787474506593)
              ·
                rfl

theorem cell21_1781180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 7].length) (baseStart_1781180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781180 prefixEnd_1781180 := by exact prefixLift 1781180
  have htrace : WordTrace (prefixWord ++ tailWord_1781180) baseStart_1781180 baseEnd_1781180 := by
    simpa [prefixWord, tailWord_1781180, baseEnd_1781180] using wordTrace_append hprefix tailTrace_1781180
  have hstable : (prefixWord ++ tailWord_1781180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781180).length < 2 ^ (prefixWord ++ tailWord_1781180).sum := by decide
  have hdescent : baseEnd_1781180 < baseStart_1781180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781194 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1781194 : Nat := 118140960795 + 1781194 * 2 ^ 59
def prefixEnd_1781194 : Nat := 4983230072969 + 3 ^ 40 * 1781194 * 2
def baseEnd_1781194 : Nat := 406492738179826357325975

theorem tailTrace_1781194 : CollatzResearch.WordTrace tailWord_1781194 prefixEnd_1781194 406492738179826357325975 := by
  unfold tailWord_1781194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241370577261454140353659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43310321539363877707609757 16241370577261454140353659)
  ·
    refine ⟨24362055865892181210530489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241370577261454140353659 24362055865892181210530489)
    ·
      refine ⟨18271541899419135907897867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24362055865892181210530489 18271541899419135907897867)
      ·
        refine ⟨27407312849128703861846801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18271541899419135907897867 27407312849128703861846801)
        ·
          refine ⟨20555484636846527896385101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27407312849128703861846801 20555484636846527896385101)
          ·
            refine ⟨7708306738817447961144413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20555484636846527896385101 7708306738817447961144413)
            ·
              refine ⟨2890615027056542985429155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7708306738817447961144413 2890615027056542985429155)
              ·
                refine ⟨4335922540584814478143733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890615027056542985429155 4335922540584814478143733)
                ·
                  refine ⟨406492738179826357325975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335922540584814478143733 406492738179826357325975)
                  ·
                    rfl

theorem cell21_1781194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1781194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781194 prefixEnd_1781194 := by exact prefixLift 1781194
  have htrace : WordTrace (prefixWord ++ tailWord_1781194) baseStart_1781194 baseEnd_1781194 := by
    simpa [prefixWord, tailWord_1781194, baseEnd_1781194] using wordTrace_append hprefix tailTrace_1781194
  have hstable : (prefixWord ++ tailWord_1781194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781194).length < 2 ^ (prefixWord ++ tailWord_1781194).sum := by decide
  have hdescent : baseEnd_1781194 < baseStart_1781194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781253 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1781253 : Nat := 118140960795 + 1781253 * 2 ^ 59
def prefixEnd_1781253 : Nat := 4983230072969 + 3 ^ 40 * 1781253 * 2
def baseEnd_1781253 : Nat := 406506202783655365842521

theorem tailTrace_1781253 : CollatzResearch.WordTrace tailWord_1781253 prefixEnd_1781253 406506202783655365842521 := by
  unfold tailWord_1781253
  simp only [CollatzResearch.WordTrace]
  refine ⟨64967634215832069637812413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43311756143888046425208275 64967634215832069637812413)
  ·
    refine ⟨24362862830937026114179655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64967634215832069637812413 24362862830937026114179655)
    ·
      refine ⟨36544294246405539171269483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24362862830937026114179655 36544294246405539171269483)
      ·
        refine ⟨54816441369608308756904225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36544294246405539171269483 54816441369608308756904225)
        ·
          refine ⟨41112331027206231567678169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54816441369608308756904225 41112331027206231567678169)
          ·
            refine ⟨30834248270404673675758627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41112331027206231567678169 30834248270404673675758627)
            ·
              refine ⟨46251372405607010513637941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30834248270404673675758627 46251372405607010513637941)
              ·
                refine ⟨4336066163025657235653557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46251372405607010513637941 4336066163025657235653557)
                ·
                  refine ⟨406506202783655365842521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336066163025657235653557 406506202783655365842521)
                  ·
                    rfl

theorem cell21_1781253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1781253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781253 prefixEnd_1781253 := by exact prefixLift 1781253
  have htrace : WordTrace (prefixWord ++ tailWord_1781253) baseStart_1781253 baseEnd_1781253 := by
    simpa [prefixWord, tailWord_1781253, baseEnd_1781253] using wordTrace_append hprefix tailTrace_1781253
  have hstable : (prefixWord ++ tailWord_1781253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781253).length < 2 ^ (prefixWord ++ tailWord_1781253).sum := by decide
  have hdescent : baseEnd_1781253 < baseStart_1781253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781301 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1781301 : Nat := 118140960795 + 1781301 * 2 ^ 59
def prefixEnd_1781301 : Nat := 4983230072969 + 3 ^ 40 * 1781301 * 2
def baseEnd_1781301 : Nat := 406517157037617949042423

theorem tailTrace_1781301 : CollatzResearch.WordTrace tailWord_1781301 prefixEnd_1781301 406517157037617949042423 := by
  unfold tailWord_1781301
  simp only [CollatzResearch.WordTrace]
  refine ⟨64969384919658173835559757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43312923279772115890373171 64969384919658173835559757)
  ·
    refine ⟨24363519344871815188334909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64969384919658173835559757 24363519344871815188334909)
    ·
      refine ⟨9136319754326930695625591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24363519344871815188334909 9136319754326930695625591)
      ·
        refine ⟨13704479631490396043438387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9136319754326930695625591 13704479631490396043438387)
        ·
          refine ⟨20556719447235594065157581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704479631490396043438387 20556719447235594065157581)
          ·
            refine ⟨7708769792713347774434093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20556719447235594065157581 7708769792713347774434093)
            ·
              refine ⟨2890788672267505415412785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7708769792713347774434093 2890788672267505415412785)
              ·
                refine ⟨2168091504200629061559589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890788672267505415412785 2168091504200629061559589)
                ·
                  refine ⟨406517157037617949042423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168091504200629061559589 406517157037617949042423)
                  ·
                    rfl

theorem cell21_1781301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1781301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781301 prefixEnd_1781301 := by exact prefixLift 1781301
  have htrace : WordTrace (prefixWord ++ tailWord_1781301) baseStart_1781301 baseEnd_1781301 := by
    simpa [prefixWord, tailWord_1781301, baseEnd_1781301] using wordTrace_append hprefix tailTrace_1781301
  have hstable : (prefixWord ++ tailWord_1781301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781301).length < 2 ^ (prefixWord ++ tailWord_1781301).sum := by decide
  have hdescent : baseEnd_1781301 < baseStart_1781301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781329 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_1781329 : Nat := 118140960795 + 1781329 * 2 ^ 59
def prefixEnd_1781329 : Nat := 4983230072969 + 3 ^ 40 * 1781329 * 2
def baseEnd_1781329 : Nat := 406523547019096122575699

theorem tailTrace_1781329 : CollatzResearch.WordTrace tailWord_1781329 prefixEnd_1781329 406523547019096122575699 := by
  unfold tailWord_1781329
  simp only [CollatzResearch.WordTrace]
  refine ⟨64970406163556734617579041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43313604109037823078386027 64970406163556734617579041)
  ·
    refine ⟨48727804622667550963184281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64970406163556734617579041 48727804622667550963184281)
    ·
      refine ⟨36545853467000663222388211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48727804622667550963184281 36545853467000663222388211)
      ·
        refine ⟨54818780200500994833582317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36545853467000663222388211 54818780200500994833582317)
        ·
          refine ⟨20557042575187873062593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54818780200500994833582317 20557042575187873062593369)
          ·
            refine ⟨15417781931390904796945027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20557042575187873062593369 15417781931390904796945027)
            ·
              refine ⟨23126672897086357195417541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417781931390904796945027 23126672897086357195417541)
              ·
                refine ⟨4336251168203691974140789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23126672897086357195417541 4336251168203691974140789)
                ·
                  refine ⟨406523547019096122575699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336251168203691974140789 406523547019096122575699)
                  ·
                    rfl

theorem cell21_1781329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_1781329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781329 prefixEnd_1781329 := by exact prefixLift 1781329
  have htrace : WordTrace (prefixWord ++ tailWord_1781329) baseStart_1781329 baseEnd_1781329 := by
    simpa [prefixWord, tailWord_1781329, baseEnd_1781329] using wordTrace_append hprefix tailTrace_1781329
  have hstable : (prefixWord ++ tailWord_1781329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781329).length < 2 ^ (prefixWord ++ tailWord_1781329).sum := by decide
  have hdescent : baseEnd_1781329 < baseStart_1781329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781360 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_1781360 : Nat := 118140960795 + 1781360 * 2 ^ 59
def prefixEnd_1781360 : Nat := 4983230072969 + 3 ^ 40 * 1781360 * 2
def baseEnd_1781360 : Nat := 406530621641446957558969

theorem tailTrace_1781360 : CollatzResearch.WordTrace tailWord_1781360 prefixEnd_1781360 406530621641446957558969 := by
  unfold tailWord_1781360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485768413222213455978767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43314357884296284607971689 32485768413222213455978767)
  ·
    refine ⟨48728652619833320183968151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32485768413222213455978767 48728652619833320183968151)
    ·
      refine ⟨73092978929749980275952227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48728652619833320183968151 73092978929749980275952227)
      ·
        refine ⟨109639468394624970413928341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73092978929749980275952227 109639468394624970413928341)
        ·
          refine ⟨5139350080998045488152891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109639468394624970413928341 5139350080998045488152891)
          ·
            refine ⟨7709025121497068232229337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139350080998045488152891 7709025121497068232229337)
            ·
              refine ⟨5781768841122801174172003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709025121497068232229337 5781768841122801174172003)
              ·
                refine ⟨8672653261684201761258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781768841122801174172003 8672653261684201761258005)
                ·
                  refine ⟨406530621641446957558969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8672653261684201761258005 406530621641446957558969)
                  ·
                    rfl

theorem cell21_1781360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_1781360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781360 prefixEnd_1781360 := by exact prefixLift 1781360
  have htrace : WordTrace (prefixWord ++ tailWord_1781360) baseStart_1781360 baseEnd_1781360 := by
    simpa [prefixWord, tailWord_1781360, baseEnd_1781360] using wordTrace_append hprefix tailTrace_1781360
  have hstable : (prefixWord ++ tailWord_1781360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781360).length < 2 ^ (prefixWord ++ tailWord_1781360).sum := by decide
  have hdescent : baseEnd_1781360 < baseStart_1781360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781377 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_1781377 : Nat := 118140960795 + 1781377 * 2 ^ 59
def prefixEnd_1781377 : Nat := 4983230072969 + 3 ^ 40 * 1781377 * 2
def baseEnd_1781377 : Nat := 406534501273058705775601

theorem tailTrace_1781377 : CollatzResearch.WordTrace tailWord_1781377 prefixEnd_1781377 406534501273058705775601 := by
  unfold tailWord_1781377
  simp only [CollatzResearch.WordTrace]
  refine ⟨64972156867382838815326385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43314771244921892543550923 64972156867382838815326385)
  ·
    refine ⟨48729117650537129111494789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64972156867382838815326385 48729117650537129111494789)
    ·
      refine ⟨9136709559475711708405273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48729117650537129111494789 9136709559475711708405273)
      ·
        refine ⟨6852532169606783781303955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136709559475711708405273 6852532169606783781303955)
        ·
          refine ⟨10278798254410175671955933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852532169606783781303955 10278798254410175671955933)
          ·
            refine ⟨3854549345403815876983475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10278798254410175671955933 3854549345403815876983475)
            ·
              refine ⟨5781824018105723815475213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854549345403815876983475 5781824018105723815475213)
              ·
                refine ⟨2168184006789646430803205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5781824018105723815475213 2168184006789646430803205)
                ·
                  refine ⟨406534501273058705775601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168184006789646430803205 406534501273058705775601)
                  ·
                    rfl

theorem cell21_1781377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_1781377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781377 prefixEnd_1781377 := by exact prefixLift 1781377
  have htrace : WordTrace (prefixWord ++ tailWord_1781377) baseStart_1781377 baseEnd_1781377 := by
    simpa [prefixWord, tailWord_1781377, baseEnd_1781377] using wordTrace_append hprefix tailTrace_1781377
  have hstable : (prefixWord ++ tailWord_1781377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781377).length < 2 ^ (prefixWord ++ tailWord_1781377).sum := by decide
  have hdescent : baseEnd_1781377 < baseStart_1781377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781591 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 3]
def baseStart_1781591 : Nat := 118140960795 + 1781591 * 2 ^ 59
def prefixEnd_1781591 : Nat := 4983230072969 + 3 ^ 40 * 1781591 * 2
def baseEnd_1781591 : Nat := 406583338988641889208497

theorem tailTrace_1781591 : CollatzResearch.WordTrace tailWord_1781591 prefixEnd_1781591 406583338988641889208497 := by
  unfold tailWord_1781591
  simp only [CollatzResearch.WordTrace]
  refine ⟨64979962088607553363616627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43319974725738368909077751 64979962088607553363616627)
  ·
    refine ⟨97469943132911330045424941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64979962088607553363616627 97469943132911330045424941)
    ·
      refine ⟨36551228674841748767034353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97469943132911330045424941 36551228674841748767034353)
      ·
        refine ⟨27413421506131311575275765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36551228674841748767034353 27413421506131311575275765)
        ·
          refine ⟨2570008266199810460182103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27413421506131311575275765 2570008266199810460182103)
          ·
            refine ⟨3855012399299715690273155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570008266199810460182103 3855012399299715690273155)
            ·
              refine ⟨5782518598949573535409733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855012399299715690273155 5782518598949573535409733)
              ·
                refine ⟨1084222237303045037889325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5782518598949573535409733 1084222237303045037889325)
                ·
                  refine ⟨406583338988641889208497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084222237303045037889325 406583338988641889208497)
                  ·
                    rfl

theorem cell21_1781591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].length) (baseStart_1781591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781591 prefixEnd_1781591 := by exact prefixLift 1781591
  have htrace : WordTrace (prefixWord ++ tailWord_1781591) baseStart_1781591 baseEnd_1781591 := by
    simpa [prefixWord, tailWord_1781591, baseEnd_1781591] using wordTrace_append hprefix tailTrace_1781591
  have hstable : (prefixWord ++ tailWord_1781591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781591).length < 2 ^ (prefixWord ++ tailWord_1781591).sum := by decide
  have hdescent : baseEnd_1781591 < baseStart_1781591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781650 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1781650 : Nat := 118140960795 + 1781650 * 2 ^ 59
def prefixEnd_1781650 : Nat := 4983230072969 + 3 ^ 40 * 1781650 * 2
def baseEnd_1781650 : Nat := 406596803592470897725043

theorem tailTrace_1781650 : CollatzResearch.WordTrace tailWord_1781650 prefixEnd_1781650 406596803592470897725043 := by
  unfold tailWord_1781650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16245528498848451610003601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43321409330262537626676269 16245528498848451610003601)
  ·
    refine ⟨12184146374136338707502701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16245528498848451610003601 12184146374136338707502701)
    ·
      refine ⟨4569054890301127015313513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12184146374136338707502701 4569054890301127015313513)
      ·
        refine ⟨3426791167725845261485135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4569054890301127015313513 3426791167725845261485135)
        ·
          refine ⟨5140186751588767892227703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426791167725845261485135 5140186751588767892227703)
          ·
            refine ⟨7710280127383151838341555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140186751588767892227703 7710280127383151838341555)
            ·
              refine ⟨11565420191074727757512333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710280127383151838341555 11565420191074727757512333)
              ·
                refine ⟨4337032571653022909067125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11565420191074727757512333 4337032571653022909067125)
                ·
                  refine ⟨406596803592470897725043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4337032571653022909067125 406596803592470897725043)
                  ·
                    rfl

theorem cell21_1781650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1781650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781650 prefixEnd_1781650 := by exact prefixLift 1781650
  have htrace : WordTrace (prefixWord ++ tailWord_1781650) baseStart_1781650 baseEnd_1781650 := by
    simpa [prefixWord, tailWord_1781650, baseEnd_1781650] using wordTrace_append hprefix tailTrace_1781650
  have hstable : (prefixWord ++ tailWord_1781650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781650).length < 2 ^ (prefixWord ++ tailWord_1781650).sum := by decide
  have hdescent : baseEnd_1781650 < baseStart_1781650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781816 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_1781816 : Nat := 118140960795 + 1781816 * 2 ^ 59
def prefixEnd_1781816 : Nat := 4983230072969 + 3 ^ 40 * 1781816 * 2
def baseEnd_1781816 : Nat := 406634687054091497958037

theorem tailTrace_1781816 : CollatzResearch.WordTrace tailWord_1781816 prefixEnd_1781816 406634687054091497958037 := by
  unfold tailWord_1781816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494084256396208395278651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43325445675194944527038201 32494084256396208395278651)
  ·
    refine ⟨48741126384594312592917977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32494084256396208395278651 48741126384594312592917977)
    ·
      refine ⟨36555844788445734444688483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48741126384594312592917977 36555844788445734444688483)
      ·
        refine ⟨54833767182668601667032725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36555844788445734444688483 54833767182668601667032725)
        ·
          refine ⟨2570332836687590703142159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54833767182668601667032725 2570332836687590703142159)
          ·
            refine ⟨3855499255031386054713239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570332836687590703142159 3855499255031386054713239)
            ·
              refine ⟨5783248882547079082069859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855499255031386054713239 5783248882547079082069859)
              ·
                refine ⟨8674873323820618623104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783248882547079082069859 8674873323820618623104789)
                ·
                  refine ⟨406634687054091497958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8674873323820618623104789 406634687054091497958037)
                  ·
                    rfl

theorem cell21_1781816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_1781816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781816 prefixEnd_1781816 := by exact prefixLift 1781816
  have htrace : WordTrace (prefixWord ++ tailWord_1781816) baseStart_1781816 baseEnd_1781816 := by
    simpa [prefixWord, tailWord_1781816, baseEnd_1781816] using wordTrace_append hprefix tailTrace_1781816
  have hstable : (prefixWord ++ tailWord_1781816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781816).length < 2 ^ (prefixWord ++ tailWord_1781816).sum := by decide
  have hdescent : baseEnd_1781816 < baseStart_1781816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781878 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1781878 : Nat := 118140960795 + 1781878 * 2 ^ 59
def prefixEnd_1781878 : Nat := 4983230072969 + 3 ^ 40 * 1781878 * 2
def baseEnd_1781878 : Nat := 406648836298793167924577

theorem tailTrace_1781878 : CollatzResearch.WordTrace tailWord_1781878 prefixEnd_1781878 406648836298793167924577 := by
  unfold tailWord_1781878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061901864910487586207143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43326953225711867586209525 4061901864910487586207143)
  ·
    refine ⟨6092852797365731379310715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061901864910487586207143 6092852797365731379310715)
    ·
      refine ⟨9139279196048597068966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092852797365731379310715 9139279196048597068966073)
      ·
        refine ⟨6854459397036447801724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9139279196048597068966073 6854459397036447801724555)
        ·
          refine ⟨10281689095554671702586833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854459397036447801724555 10281689095554671702586833)
          ·
            refine ⟨7711266821666003776940125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281689095554671702586833 7711266821666003776940125)
            ·
              refine ⟨2891725058124751416352547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7711266821666003776940125 2891725058124751416352547)
              ·
                refine ⟨4337587587187127124528821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891725058124751416352547 4337587587187127124528821)
                ·
                  refine ⟨406648836298793167924577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4337587587187127124528821 406648836298793167924577)
                  ·
                    rfl

theorem cell21_1781878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1781878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781878 prefixEnd_1781878 := by exact prefixLift 1781878
  have htrace : WordTrace (prefixWord ++ tailWord_1781878) baseStart_1781878 baseEnd_1781878 := by
    simpa [prefixWord, tailWord_1781878, baseEnd_1781878] using wordTrace_append hprefix tailTrace_1781878
  have hstable : (prefixWord ++ tailWord_1781878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781878).length < 2 ^ (prefixWord ++ tailWord_1781878).sum := by decide
  have hdescent : baseEnd_1781878 < baseStart_1781878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781892 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1781892 : Nat := 118140960795 + 1781892 * 2 ^ 59
def prefixEnd_1781892 : Nat := 4983230072969 + 3 ^ 40 * 1781892 * 2
def baseEnd_1781892 : Nat := 406652031289532254691215

theorem tailTrace_1781892 : CollatzResearch.WordTrace tailWord_1781892 prefixEnd_1781892 406652031289532254691215 := by
  unfold tailWord_1781892
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495470230258540885161965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43327293640344721180215953 32495470230258540885161965)
  ·
    refine ⟨12185801336346952831935737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32495470230258540885161965 12185801336346952831935737)
    ·
      refine ⟨9139351002260214623951803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12185801336346952831935737 9139351002260214623951803)
      ·
        refine ⟨13709026503390321935927705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139351002260214623951803 13709026503390321935927705)
        ·
          refine ⟨10281769877542741451945779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13709026503390321935927705 10281769877542741451945779)
          ·
            refine ⟨15422654816314112177918669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281769877542741451945779 15422654816314112177918669)
            ·
              refine ⟨5783495556117792066719501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15422654816314112177918669 5783495556117792066719501)
              ·
                refine ⟨2168810833544172025019813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783495556117792066719501 2168810833544172025019813)
                ·
                  refine ⟨406652031289532254691215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168810833544172025019813 406652031289532254691215)
                  ·
                    rfl

theorem cell21_1781892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1781892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781892 prefixEnd_1781892 := by exact prefixLift 1781892
  have htrace : WordTrace (prefixWord ++ tailWord_1781892) baseStart_1781892 baseEnd_1781892 := by
    simpa [prefixWord, tailWord_1781892, baseEnd_1781892] using wordTrace_append hprefix tailTrace_1781892
  have hstable : (prefixWord ++ tailWord_1781892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781892).length < 2 ^ (prefixWord ++ tailWord_1781892).sum := by decide
  have hdescent : baseEnd_1781892 < baseStart_1781892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781906 : List Nat := [3, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1781906 : Nat := 118140960795 + 1781906 * 2 ^ 59
def prefixEnd_1781906 : Nat := 4983230072969 + 3 ^ 40 * 1781906 * 2
def baseEnd_1781906 : Nat := 135551742093423780485951

theorem tailTrace_1781906 : CollatzResearch.WordTrace tailWord_1781906 prefixEnd_1781906 135551742093423780485951 := by
  unfold tailWord_1781906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16247862770616590540333393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43327634054977574774222381 16247862770616590540333393)
  ·
    refine ⟨12185897077962442905250045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16247862770616590540333393 12185897077962442905250045)
    ·
      refine ⟨4569711404235916089468767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12185897077962442905250045 4569711404235916089468767)
      ·
        refine ⟨6854567106353874134203151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569711404235916089468767 6854567106353874134203151)
        ·
          refine ⟨10281850659530811201304727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854567106353874134203151 10281850659530811201304727)
          ·
            refine ⟨15422775989296216801957091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281850659530811201304727 15422775989296216801957091)
            ·
              refine ⟨23134163983944325202935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15422775989296216801957091 23134163983944325202935637)
              ·
                refine ⟨135551742093423780485951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23134163983944325202935637 135551742093423780485951)
                ·
                  rfl

theorem cell21_1781906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1781906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1781906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1781906 prefixEnd_1781906 := by exact prefixLift 1781906
  have htrace : WordTrace (prefixWord ++ tailWord_1781906) baseStart_1781906 baseEnd_1781906 := by
    simpa [prefixWord, tailWord_1781906, baseEnd_1781906] using wordTrace_append hprefix tailTrace_1781906
  have hstable : (prefixWord ++ tailWord_1781906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781906).length < 2 ^ (prefixWord ++ tailWord_1781906).sum := by decide
  have hdescent : baseEnd_1781906 < baseStart_1781906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782047 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 3]
def baseStart_1782047 : Nat := 118140960795 + 1782047 * 2 ^ 59
def prefixEnd_1782047 : Nat := 4983230072969 + 3 ^ 40 * 1782047 * 2
def baseEnd_1782047 : Nat := 406687404401286429607565

theorem tailTrace_1782047 : CollatzResearch.WordTrace tailWord_1782047 prefixEnd_1782047 406687404401286429607565 := by
  unfold tailWord_1782047
  simp only [CollatzResearch.WordTrace]
  refine ⟨64996593774955543242216395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43331062516637028828144263 64996593774955543242216395)
  ·
    refine ⟨97494890662433314863324593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64996593774955543242216395 97494890662433314863324593)
    ·
      refine ⟨73121167996824986147493445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97494890662433314863324593 73121167996824986147493445)
      ·
        refine ⟨13710218999404684902655021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73121167996824986147493445 13710218999404684902655021)
        ·
          refine ⟨5141332124776756838495633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13710218999404684902655021 5141332124776756838495633)
          ·
            refine ⟨3855999093582567628871725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141332124776756838495633 3855999093582567628871725)
            ·
              refine ⟨1445999660093462860826897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855999093582567628871725 1445999660093462860826897)
              ·
                refine ⟨1084499745070097145620173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445999660093462860826897 1084499745070097145620173)
                ·
                  refine ⟨406687404401286429607565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084499745070097145620173 406687404401286429607565)
                  ·
                    rfl

theorem cell21_1782047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].length) (baseStart_1782047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782047 prefixEnd_1782047 := by exact prefixLift 1782047
  have htrace : WordTrace (prefixWord ++ tailWord_1782047) baseStart_1782047 baseEnd_1782047 := by
    simpa [prefixWord, tailWord_1782047, baseEnd_1782047] using wordTrace_append hprefix tailTrace_1782047
  have hstable : (prefixWord ++ tailWord_1782047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782047).length < 2 ^ (prefixWord ++ tailWord_1782047).sum := by decide
  have hdescent : baseEnd_1782047 < baseStart_1782047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782072 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_1782072 : Nat := 118140960795 + 1782072 * 2 ^ 59
def prefixEnd_1782072 : Nat := 4983230072969 + 3 ^ 40 * 1782072 * 2
def baseEnd_1782072 : Nat := 406693109741891941690847

theorem tailTrace_1782072 : CollatzResearch.WordTrace tailWord_1782072 prefixEnd_1782072 406693109741891941690847 := by
  unfold tailWord_1782072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32498752799932486255938235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43331670399909981674584313 32498752799932486255938235)
  ·
    refine ⟨48748129199898729383907353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32498752799932486255938235 48748129199898729383907353)
    ·
      refine ⟨36561096899924047037930515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48748129199898729383907353 36561096899924047037930515)
      ·
        refine ⟨54841645349886070556895773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36561096899924047037930515 54841645349886070556895773)
        ·
          refine ⟨20565617006207276458835915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54841645349886070556895773 20565617006207276458835915)
          ·
            refine ⟨30848425509310914688253873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565617006207276458835915 30848425509310914688253873)
            ·
              refine ⟨23136319131983186016190405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30848425509310914688253873 23136319131983186016190405)
              ·
                refine ⟨4338059837246847378035701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23136319131983186016190405 4338059837246847378035701)
                ·
                  refine ⟨406693109741891941690847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338059837246847378035701 406693109741891941690847)
                  ·
                    rfl

theorem cell21_1782072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_1782072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782072 prefixEnd_1782072 := by exact prefixLift 1782072
  have htrace : WordTrace (prefixWord ++ tailWord_1782072) baseStart_1782072 baseEnd_1782072 := by
    simpa [prefixWord, tailWord_1782072, baseEnd_1782072] using wordTrace_append hprefix tailTrace_1782072
  have hstable : (prefixWord ++ tailWord_1782072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782072).length < 2 ^ (prefixWord ++ tailWord_1782072).sum := by decide
  have hdescent : baseEnd_1782072 < baseStart_1782072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782089 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 3]
def baseStart_1782089 : Nat := 118140960795 + 1782089 * 2 ^ 59
def prefixEnd_1782089 : Nat := 4983230072969 + 3 ^ 40 * 1782089 * 2
def baseEnd_1782089 : Nat := 406696989373503689907479

theorem tailTrace_1782089 : CollatzResearch.WordTrace tailWord_1782089 prefixEnd_1782089 406696989373503689907479 := by
  unfold tailWord_1782089
  simp only [CollatzResearch.WordTrace]
  refine ⟨64998125640803384415245321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43332083760535589610163547 64998125640803384415245321)
  ·
    refine ⟨48748594230602538311433991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64998125640803384415245321 48748594230602538311433991)
    ·
      refine ⟨73122891345903807467150987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48748594230602538311433991 73122891345903807467150987)
      ·
        refine ⟨109684337018855711200726481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73122891345903807467150987 109684337018855711200726481)
        ·
          refine ⟨82263252764141783400544861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109684337018855711200726481 82263252764141783400544861)
          ·
            refine ⟨30848719786553168775204323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82263252764141783400544861 30848719786553168775204323)
            ·
              refine ⟨46273079679829753162806485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30848719786553168775204323 46273079679829753162806485)
              ·
                refine ⟨1084525304996009839753277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46273079679829753162806485 1084525304996009839753277)
                ·
                  refine ⟨406696989373503689907479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084525304996009839753277 406696989373503689907479)
                  ·
                    rfl

theorem cell21_1782089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_1782089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782089 prefixEnd_1782089 := by exact prefixLift 1782089
  have htrace : WordTrace (prefixWord ++ tailWord_1782089) baseStart_1782089 baseEnd_1782089 := by
    simpa [prefixWord, tailWord_1782089, baseEnd_1782089] using wordTrace_append hprefix tailTrace_1782089
  have hstable : (prefixWord ++ tailWord_1782089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782089).length < 2 ^ (prefixWord ++ tailWord_1782089).sum := by decide
  have hdescent : baseEnd_1782089 < baseStart_1782089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782120 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_1782120 : Nat := 118140960795 + 1782120 * 2 ^ 59
def prefixEnd_1782120 : Nat := 4983230072969 + 3 ^ 40 * 1782120 * 2
def baseEnd_1782120 : Nat := 406704063995854524890749

theorem tailTrace_1782120 : CollatzResearch.WordTrace tailWord_1782120 prefixEnd_1782120 406704063995854524890749 := by
  unfold tailWord_1782120
  simp only [CollatzResearch.WordTrace]
  refine ⟨32499628151845538354811907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43332837535794051139749209 32499628151845538354811907)
  ·
    refine ⟨48749442227768307532217861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32499628151845538354811907 48749442227768307532217861)
    ·
      refine ⟨9140520417706557662290849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48749442227768307532217861 9140520417706557662290849)
      ·
        refine ⟨6855390313279918246718137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9140520417706557662290849 6855390313279918246718137)
        ·
          refine ⟨5141542734959938685038603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855390313279918246718137 5141542734959938685038603)
          ·
            refine ⟨7712314102439908027557905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141542734959938685038603 7712314102439908027557905)
            ·
              refine ⟨5784235576829931020668429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7712314102439908027557905 5784235576829931020668429)
              ·
                refine ⟨2169088341311224132750661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5784235576829931020668429 2169088341311224132750661)
                ·
                  refine ⟨406704063995854524890749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169088341311224132750661 406704063995854524890749)
                  ·
                    rfl

theorem cell21_1782120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_1782120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782120 prefixEnd_1782120 := by exact prefixLift 1782120
  have htrace : WordTrace (prefixWord ++ tailWord_1782120) baseStart_1782120 baseEnd_1782120 := by
    simpa [prefixWord, tailWord_1782120, baseEnd_1782120] using wordTrace_append hprefix tailTrace_1782120
  have hstable : (prefixWord ++ tailWord_1782120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782120).length < 2 ^ (prefixWord ++ tailWord_1782120).sum := by decide
  have hdescent : baseEnd_1782120 < baseStart_1782120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782148 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1782148 : Nat := 118140960795 + 1782148 * 2 ^ 59
def prefixEnd_1782148 : Nat := 4983230072969 + 3 ^ 40 * 1782148 * 2
def baseEnd_1782148 : Nat := 406710453977332698424025

theorem tailTrace_1782148 : CollatzResearch.WordTrace tailWord_1782148 prefixEnd_1782148 406710453977332698424025 := by
  unfold tailWord_1782148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500138773794818745821549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43333518365059758327762065 32500138773794818745821549)
  ·
    refine ⟨12187552040173057029683081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32500138773794818745821549 12187552040173057029683081)
    ·
      refine ⟨9140664030129792772262311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12187552040173057029683081 9140664030129792772262311)
      ·
        refine ⟨13710996045194689158393467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140664030129792772262311 13710996045194689158393467)
        ·
          refine ⟨20566494067792033737590201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710996045194689158393467 20566494067792033737590201)
          ·
            refine ⟨15424870550844025303192651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20566494067792033737590201 15424870550844025303192651)
            ·
              refine ⟨23137305826266037954788977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15424870550844025303192651 23137305826266037954788977)
              ·
                refine ⟨17352979369699528466091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23137305826266037954788977 17352979369699528466091733)
                ·
                  refine ⟨406710453977332698424025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17352979369699528466091733 406710453977332698424025)
                  ·
                    rfl

theorem cell21_1782148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1782148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782148 prefixEnd_1782148 := by exact prefixLift 1782148
  have htrace : WordTrace (prefixWord ++ tailWord_1782148) baseStart_1782148 baseEnd_1782148 := by
    simpa [prefixWord, tailWord_1782148, baseEnd_1782148] using wordTrace_append hprefix tailTrace_1782148
  have hstable : (prefixWord ++ tailWord_1782148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782148).length < 2 ^ (prefixWord ++ tailWord_1782148).sum := by decide
  have hdescent : baseEnd_1782148 < baseStart_1782148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782154 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1782154 : Nat := 118140960795 + 1782154 * 2 ^ 59
def prefixEnd_1782154 : Nat := 4983230072969 + 3 ^ 40 * 1782154 * 2
def baseEnd_1782154 : Nat := 406711823259078021324013

theorem tailTrace_1782154 : CollatzResearch.WordTrace tailWord_1782154 prefixEnd_1782154 406711823259078021324013 := by
  unfold tailWord_1782154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250124096391975129090379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43333664257045267010907677 16250124096391975129090379)
  ·
    refine ⟨24375186144587962693635569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16250124096391975129090379 24375186144587962693635569)
    ·
      refine ⟨18281389608440972020226677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24375186144587962693635569 18281389608440972020226677)
      ·
        refine ⟨1713880275791341126896251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18281389608440972020226677 1713880275791341126896251)
        ·
          refine ⟨2570820413687011690344377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713880275791341126896251 2570820413687011690344377)
          ·
            refine ⟨1928115310265258767758283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570820413687011690344377 1928115310265258767758283)
            ·
              refine ⟨2892172965397888151637425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928115310265258767758283 2892172965397888151637425)
              ·
                refine ⟨2169129724048416113728069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892172965397888151637425 2169129724048416113728069)
                ·
                  refine ⟨406711823259078021324013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169129724048416113728069 406711823259078021324013)
                  ·
                    rfl

theorem cell21_1782154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1782154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782154 prefixEnd_1782154 := by exact prefixLift 1782154
  have htrace : WordTrace (prefixWord ++ tailWord_1782154) baseStart_1782154 baseEnd_1782154 := by
    simpa [prefixWord, tailWord_1782154, baseEnd_1782154] using wordTrace_append hprefix tailTrace_1782154
  have hstable : (prefixWord ++ tailWord_1782154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782154).length < 2 ^ (prefixWord ++ tailWord_1782154).sum := by decide
  have hdescent : baseEnd_1782154 < baseStart_1782154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782286 : List Nat := [4, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1782286 : Nat := 118140960795 + 1782286 * 2 ^ 59
def prefixEnd_1782286 : Nat := 4983230072969 + 3 ^ 40 * 1782286 * 2
def baseEnd_1782286 : Nat := 135580649152491708374581

theorem tailTrace_1782286 : CollatzResearch.WordTrace tailWord_1782286 prefixEnd_1782286 135580649152491708374581 := by
  unfold tailWord_1782286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125663852636210882520839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43336873880726458040111141 8125663852636210882520839)
  ·
    refine ⟨12188495778954316323781259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125663852636210882520839 12188495778954316323781259)
    ·
      refine ⟨18282743668431474485671889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188495778954316323781259 18282743668431474485671889)
      ·
        refine ⟨13712057751323605864253917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18282743668431474485671889 13712057751323605864253917)
        ·
          refine ⟨5142021656746352199095219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13712057751323605864253917 5142021656746352199095219)
          ·
            refine ⟨7713032485119528298642829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142021656746352199095219 7713032485119528298642829)
            ·
              refine ⟨2892387181919823111991061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7713032485119528298642829 2892387181919823111991061)
              ·
                refine ⟨135580649152491708374581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2892387181919823111991061 135580649152491708374581)
                ·
                  rfl

theorem cell21_1782286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1782286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782286 prefixEnd_1782286 := by exact prefixLift 1782286
  have htrace : WordTrace (prefixWord ++ tailWord_1782286) baseStart_1782286 baseEnd_1782286 := by
    simpa [prefixWord, tailWord_1782286, baseEnd_1782286] using wordTrace_append hprefix tailTrace_1782286
  have hstable : (prefixWord ++ tailWord_1782286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782286).length < 2 ^ (prefixWord ++ tailWord_1782286).sum := by decide
  have hdescent : baseEnd_1782286 < baseStart_1782286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782300 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1782300 : Nat := 118140960795 + 1782300 * 2 ^ 59
def prefixEnd_1782300 : Nat := 4983230072969 + 3 ^ 40 * 1782300 * 2
def baseEnd_1782300 : Nat := 406745142448214211890381

theorem tailTrace_1782300 : CollatzResearch.WordTrace tailWord_1782300 prefixEnd_1782300 406745142448214211890381 := by
  unfold tailWord_1782300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32502910721519483725588177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43337214295359311634117569 32502910721519483725588177)
  ·
    refine ⟨24377183041139612794191133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32502910721519483725588177 24377183041139612794191133)
    ·
      refine ⟨9141443640427354797821675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24377183041139612794191133 9141443640427354797821675)
      ·
        refine ⟨13712165460641032196732513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141443640427354797821675 13712165460641032196732513)
        ·
          refine ⟨10284124095480774147549385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13712165460641032196732513 10284124095480774147549385)
          ·
            refine ⟨7713093071610580610662039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284124095480774147549385 7713093071610580610662039)
            ·
              refine ⟨11569639607415870915993059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713093071610580610662039 11569639607415870915993059)
              ·
                refine ⟨17354459411123806373989589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11569639607415870915993059 17354459411123806373989589)
                ·
                  refine ⟨406745142448214211890381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17354459411123806373989589 406745142448214211890381)
                  ·
                    rfl

theorem cell21_1782300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1782300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782300 prefixEnd_1782300 := by exact prefixLift 1782300
  have htrace : WordTrace (prefixWord ++ tailWord_1782300) baseStart_1782300 baseEnd_1782300 := by
    simpa [prefixWord, tailWord_1782300, baseEnd_1782300] using wordTrace_append hprefix tailTrace_1782300
  have hstable : (prefixWord ++ tailWord_1782300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782300).length < 2 ^ (prefixWord ++ tailWord_1782300).sum := by decide
  have hdescent : baseEnd_1782300 < baseStart_1782300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782348 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1782348 : Nat := 118140960795 + 1782348 * 2 ^ 59
def prefixEnd_1782348 : Nat := 4983230072969 + 3 ^ 40 * 1782348 * 2
def baseEnd_1782348 : Nat := 406756096702176795090283

theorem tailTrace_1782348 : CollatzResearch.WordTrace tailWord_1782348 prefixEnd_1782348 406756096702176795090283 := by
  unfold tailWord_1782348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32503786073432535824461849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43338381431243381099282465 32503786073432535824461849)
  ·
    refine ⟨24377839555074401868346387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32503786073432535824461849 24377839555074401868346387)
    ·
      refine ⟨36566759332611602802519581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24377839555074401868346387 36566759332611602802519581)
      ·
        refine ⟨13712534749729351050944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36566759332611602802519581 13712534749729351050944843)
        ·
          refine ⟨20568802124594026576417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712534749729351050944843 20568802124594026576417265)
          ·
            refine ⟨15426601593445519932312949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20568802124594026576417265 15426601593445519932312949)
            ·
              refine ⟨1446243899385517493654339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15426601593445519932312949 1446243899385517493654339)
              ·
                refine ⟨2169365849078276240481509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446243899385517493654339 2169365849078276240481509)
                ·
                  refine ⟨406756096702176795090283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169365849078276240481509 406756096702176795090283)
                  ·
                    rfl

theorem cell21_1782348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1782348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782348 prefixEnd_1782348 := by exact prefixLift 1782348
  have htrace : WordTrace (prefixWord ++ tailWord_1782348) baseStart_1782348 baseEnd_1782348 := by
    simpa [prefixWord, tailWord_1782348, baseEnd_1782348] using wordTrace_append hprefix tailTrace_1782348
  have hstable : (prefixWord ++ tailWord_1782348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782348).length < 2 ^ (prefixWord ++ tailWord_1782348).sum := by decide
  have hdescent : baseEnd_1782348 < baseStart_1782348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782393 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_1782393 : Nat := 118140960795 + 1782393 * 2 ^ 59
def prefixEnd_1782393 : Nat := 4983230072969 + 3 ^ 40 * 1782393 * 2
def baseEnd_1782393 : Nat := 406766366315266716840191

theorem tailTrace_1782393 : CollatzResearch.WordTrace tailWord_1782393 prefixEnd_1782393 406766366315266716840191 := by
  unfold tailWord_1782393
  simp only [CollatzResearch.WordTrace]
  refine ⟨65009213431702044334311833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43339475621134696222874555 65009213431702044334311833)
  ·
    refine ⟨48756910073776533250733875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65009213431702044334311833 48756910073776533250733875)
    ·
      refine ⟨73135365110664799876100813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48756910073776533250733875 73135365110664799876100813)
      ·
        refine ⟨27425761916499299953537805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73135365110664799876100813 27425761916499299953537805)
        ·
          refine ⟨10284660718687237482576677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27425761916499299953537805 10284660718687237482576677)
          ·
            refine ⟨1928373884753857027983127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10284660718687237482576677 1928373884753857027983127)
            ·
              refine ⟨2892560827130785541974691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928373884753857027983127 2892560827130785541974691)
              ·
                refine ⟨4338841240696178312962037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892560827130785541974691 4338841240696178312962037)
                ·
                  refine ⟨406766366315266716840191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338841240696178312962037 406766366315266716840191)
                  ·
                    rfl

theorem cell21_1782393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_1782393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782393 prefixEnd_1782393 := by exact prefixLift 1782393
  have htrace : WordTrace (prefixWord ++ tailWord_1782393) baseStart_1782393 baseEnd_1782393 := by
    simpa [prefixWord, tailWord_1782393, baseEnd_1782393] using wordTrace_append hprefix tailTrace_1782393
  have hstable : (prefixWord ++ tailWord_1782393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782393).length < 2 ^ (prefixWord ++ tailWord_1782393).sum := by decide
  have hdescent : baseEnd_1782393 < baseStart_1782393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782407 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_1782407 : Nat := 118140960795 + 1782407 * 2 ^ 59
def prefixEnd_1782407 : Nat := 4983230072969 + 3 ^ 40 * 1782407 * 2
def baseEnd_1782407 : Nat := 406769561306005803606829

theorem tailTrace_1782407 : CollatzResearch.WordTrace tailWord_1782407 prefixEnd_1782407 406769561306005803606829 := by
  unfold tailWord_1782407
  simp only [CollatzResearch.WordTrace]
  refine ⟨65009724053651324725321475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43339816035767549816880983 65009724053651324725321475)
  ·
    refine ⟨97514586080476987087982213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65009724053651324725321475 97514586080476987087982213)
    ·
      refine ⟨18283984890089435078996665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97514586080476987087982213 18283984890089435078996665)
      ·
        refine ⟨13712988667567076309247499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18283984890089435078996665 13712988667567076309247499)
        ·
          refine ⟨20569483001350614463871249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712988667567076309247499 20569483001350614463871249)
          ·
            refine ⟨15427112251012960847903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20569483001350614463871249 15427112251012960847903437)
            ·
              refine ⟨5785167094129860317963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15427112251012960847903437 5785167094129860317963789)
              ·
                refine ⟨2169437660298697619236421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5785167094129860317963789 2169437660298697619236421)
                ·
                  refine ⟨406769561306005803606829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169437660298697619236421 406769561306005803606829)
                  ·
                    rfl

theorem cell21_1782407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_1782407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782407 prefixEnd_1782407 := by exact prefixLift 1782407
  have htrace : WordTrace (prefixWord ++ tailWord_1782407) baseStart_1782407 baseEnd_1782407 := by
    simpa [prefixWord, tailWord_1782407, baseEnd_1782407] using wordTrace_append hprefix tailTrace_1782407
  have hstable : (prefixWord ++ tailWord_1782407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782407).length < 2 ^ (prefixWord ++ tailWord_1782407).sum := by decide
  have hdescent : baseEnd_1782407 < baseStart_1782407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782435 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_1782435 : Nat := 118140960795 + 1782435 * 2 ^ 59
def prefixEnd_1782435 : Nat := 4983230072969 + 3 ^ 40 * 1782435 * 2
def baseEnd_1782435 : Nat := 406775951287483977140105

theorem tailTrace_1782435 : CollatzResearch.WordTrace tailWord_1782435 prefixEnd_1782435 406775951287483977140105 := by
  unfold tailWord_1782435
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010745297549885507340759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43340496865033257004893839 65010745297549885507340759)
  ·
    refine ⟨97516117946324828261011139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65010745297549885507340759 97516117946324828261011139)
    ·
      refine ⟨146274176919487242391516709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97516117946324828261011139 146274176919487242391516709)
      ·
        refine ⟨27426408172403857948409383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146274176919487242391516709 27426408172403857948409383)
        ·
          refine ⟨41139612258605786922614075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27426408172403857948409383 41139612258605786922614075)
          ·
            refine ⟨61709418387908680383921113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41139612258605786922614075 61709418387908680383921113)
            ·
              refine ⟨46282063790931510287940835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61709418387908680383921113 46282063790931510287940835)
              ·
                refine ⟨69423095686397265431911253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46282063790931510287940835 69423095686397265431911253)
                ·
                  refine ⟨406775951287483977140105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69423095686397265431911253 406775951287483977140105)
                  ·
                    rfl

theorem cell21_1782435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_1782435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782435 prefixEnd_1782435 := by exact prefixLift 1782435
  have htrace : WordTrace (prefixWord ++ tailWord_1782435) baseStart_1782435 baseEnd_1782435 := by
    simpa [prefixWord, tailWord_1782435, baseEnd_1782435] using wordTrace_append hprefix tailTrace_1782435
  have hstable : (prefixWord ++ tailWord_1782435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782435).length < 2 ^ (prefixWord ++ tailWord_1782435).sum := by decide
  have hdescent : baseEnd_1782435 < baseStart_1782435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782455 : List Nat := [1, 1, 3, 1, 7, 1, 1, 6]
def baseStart_1782455 : Nat := 118140960795 + 1782455 * 2 ^ 59
def prefixEnd_1782455 : Nat := 4983230072969 + 3 ^ 40 * 1782455 * 2
def baseEnd_1782455 : Nat := 135593505186656128935577

theorem tailTrace_1782455 : CollatzResearch.WordTrace tailWord_1782455 prefixEnd_1782455 135593505186656128935577 := by
  unfold tailWord_1782455
  simp only [CollatzResearch.WordTrace]
  refine ⟨65011474757477428923068819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43340983171651619282045879 65011474757477428923068819)
  ·
    refine ⟨97517212136216143384603229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65011474757477428923068819 97517212136216143384603229)
    ·
      refine ⟨36568954551081053769226211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97517212136216143384603229 36568954551081053769226211)
      ·
        refine ⟨54853431826621580653839317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36568954551081053769226211 54853431826621580653839317)
        ·
          refine ⟨1285627308436443296574359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54853431826621580653839317 1285627308436443296574359)
          ·
            refine ⟨1928440962654664944861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285627308436443296574359 1928440962654664944861539)
            ·
              refine ⟨2892661443981997417292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928440962654664944861539 2892661443981997417292309)
              ·
                refine ⟨135593505186656128935577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2892661443981997417292309 135593505186656128935577)
                ·
                  rfl

theorem cell21_1782455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].length) (baseStart_1782455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782455 prefixEnd_1782455 := by exact prefixLift 1782455
  have htrace : WordTrace (prefixWord ++ tailWord_1782455) baseStart_1782455 baseEnd_1782455 := by
    simpa [prefixWord, tailWord_1782455, baseEnd_1782455] using wordTrace_append hprefix tailTrace_1782455
  have hstable : (prefixWord ++ tailWord_1782455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782455).length < 2 ^ (prefixWord ++ tailWord_1782455).sum := by decide
  have hdescent : baseEnd_1782455 < baseStart_1782455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782497 : List Nat := [1, 2, 3, 1, 4, 2, 8]
def baseStart_1782497 : Nat := 118140960795 + 1782497 * 2 ^ 59
def prefixEnd_1782497 : Nat := 4983230072969 + 3 ^ 40 * 1782497 * 2
def baseEnd_1782497 : Nat := 45198900059131738567405

theorem tailTrace_1782497 : CollatzResearch.WordTrace tailWord_1782497 prefixEnd_1782497 45198900059131738567405 := by
  unfold tailWord_1782497
  simp only [CollatzResearch.WordTrace]
  refine ⟨65013006623325270096097745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43342004415550180064065163 65013006623325270096097745)
  ·
    refine ⟨48759754967493952572073309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65013006623325270096097745 48759754967493952572073309)
    ·
      refine ⟨18284908112810232214527491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48759754967493952572073309 18284908112810232214527491)
      ·
        refine ⟨27427362169215348321791237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18284908112810232214527491 27427362169215348321791237)
        ·
          refine ⟨5142630406727877810335857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27427362169215348321791237 5142630406727877810335857)
          ·
            refine ⟨3856972805045908357751893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142630406727877810335857 3856972805045908357751893)
            ·
              refine ⟨45198900059131738567405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3856972805045908357751893 45198900059131738567405)
              ·
                rfl

theorem cell21_1782497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 8].length) (baseStart_1782497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782497 prefixEnd_1782497 := by exact prefixLift 1782497
  have htrace : WordTrace (prefixWord ++ tailWord_1782497) baseStart_1782497 baseEnd_1782497 := by
    simpa [prefixWord, tailWord_1782497, baseEnd_1782497] using wordTrace_append hprefix tailTrace_1782497
  have hstable : (prefixWord ++ tailWord_1782497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782497).length < 2 ^ (prefixWord ++ tailWord_1782497).sum := by decide
  have hdescent : baseEnd_1782497 < baseStart_1782497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782500 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1782500 : Nat := 118140960795 + 1782500 * 2 ^ 59
def prefixEnd_1782500 : Nat := 4983230072969 + 3 ^ 40 * 1782500 * 2
def baseEnd_1782500 : Nat := 406790785173058308556639

theorem tailTrace_1782500 : CollatzResearch.WordTrace tailWord_1782500 prefixEnd_1782500 406790785173058308556639 := by
  unfold tailWord_1782500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32506558021157200804228477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43342077361542934405637969 32506558021157200804228477)
  ·
    refine ⟨12189959257933950301585679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32506558021157200804228477 12189959257933950301585679)
    ·
      refine ⟨18284938886900925452378519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12189959257933950301585679 18284938886900925452378519)
      ·
        refine ⟨27427408330351388178567779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18284938886900925452378519 27427408330351388178567779)
        ·
          refine ⟨41141112495527082267851669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27427408330351388178567779 41141112495527082267851669)
          ·
            refine ⟨1928489648227831981305547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41141112495527082267851669 1928489648227831981305547)
            ·
              refine ⟨2892734472341747971958321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928489648227831981305547 2892734472341747971958321)
              ·
                refine ⟨2169550854256310978968741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892734472341747971958321 2169550854256310978968741)
                ·
                  refine ⟨406790785173058308556639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169550854256310978968741 406790785173058308556639)
                  ·
                    rfl

theorem cell21_1782500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1782500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782500 prefixEnd_1782500 := by exact prefixLift 1782500
  have htrace : WordTrace (prefixWord ++ tailWord_1782500) baseStart_1782500 baseEnd_1782500 := by
    simpa [prefixWord, tailWord_1782500, baseEnd_1782500] using wordTrace_append hprefix tailTrace_1782500
  have hstable : (prefixWord ++ tailWord_1782500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782500).length < 2 ^ (prefixWord ++ tailWord_1782500).sum := by decide
  have hdescent : baseEnd_1782500 < baseStart_1782500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782545 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 3]
def baseStart_1782545 : Nat := 118140960795 + 1782545 * 2 ^ 59
def prefixEnd_1782545 : Nat := 4983230072969 + 3 ^ 40 * 1782545 * 2
def baseEnd_1782545 : Nat := 406801054786148230306547

theorem tailTrace_1782545 : CollatzResearch.WordTrace tailWord_1782545 prefixEnd_1782545 406801054786148230306547 := by
  unfold tailWord_1782545
  simp only [CollatzResearch.WordTrace]
  refine ⟨65014757327151374293845089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43343171551434249529230059 65014757327151374293845089)
  ·
    refine ⟨48761067995363530720383817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65014757327151374293845089 48761067995363530720383817)
    ·
      refine ⟨36570800996522648040287863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48761067995363530720383817 36570800996522648040287863)
      ·
        refine ⟨54856201494783972060431795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36570800996522648040287863 54856201494783972060431795)
        ·
          refine ⟨82284302242175958090647693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54856201494783972060431795 82284302242175958090647693)
          ·
            refine ⟨30856613340815984283992885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82284302242175958090647693 30856613340815984283992885)
            ·
              refine ⟨2892807500701498526624333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30856613340815984283992885 2892807500701498526624333)
              ·
                refine ⟨1084802812763061947484125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2892807500701498526624333 1084802812763061947484125)
                ·
                  refine ⟨406801054786148230306547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084802812763061947484125 406801054786148230306547)
                  ·
                    rfl

theorem cell21_1782545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_1782545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782545 prefixEnd_1782545 := by exact prefixLift 1782545
  have htrace : WordTrace (prefixWord ++ tailWord_1782545) baseStart_1782545 baseEnd_1782545 := by
    simpa [prefixWord, tailWord_1782545, baseEnd_1782545] using wordTrace_append hprefix tailTrace_1782545
  have hstable : (prefixWord ++ tailWord_1782545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782545).length < 2 ^ (prefixWord ++ tailWord_1782545).sum := by decide
  have hdescent : baseEnd_1782545 < baseStart_1782545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782742 : List Nat := [5, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1782742 : Nat := 118140960795 + 1782742 * 2 ^ 59
def prefixEnd_1782742 : Nat := 4983230072969 + 3 ^ 40 * 1782742 * 2
def baseEnd_1782742 : Nat := 135615337623373221840937

theorem tailTrace_1782742 : CollatzResearch.WordTrace tailWord_1782742 prefixEnd_1782742 135615337623373221840937 := by
  unfold tailWord_1782742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063871406714854808672905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43347961671625117959177653 4063871406714854808672905)
  ·
    refine ⟨3047903555036141106504679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063871406714854808672905 3047903555036141106504679)
    ·
      refine ⟨4571855332554211659757019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047903555036141106504679 4571855332554211659757019)
      ·
        refine ⟨6857782998831317489635529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571855332554211659757019 6857782998831317489635529)
        ·
          refine ⟨5143337249123488117226647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857782998831317489635529 5143337249123488117226647)
          ·
            refine ⟨7715005873685232175839971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143337249123488117226647 7715005873685232175839971)
            ·
              refine ⟨11572508810527848263759957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715005873685232175839971 11572508810527848263759957)
              ·
                refine ⟨135615337623373221840937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11572508810527848263759957 135615337623373221840937)
                ·
                  rfl

theorem cell21_1782742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1782742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782742 prefixEnd_1782742 := by exact prefixLift 1782742
  have htrace : WordTrace (prefixWord ++ tailWord_1782742) baseStart_1782742 baseEnd_1782742 := by
    simpa [prefixWord, tailWord_1782742, baseEnd_1782742] using wordTrace_append hprefix tailTrace_1782742
  have hstable : (prefixWord ++ tailWord_1782742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782742).length < 2 ^ (prefixWord ++ tailWord_1782742).sum := by decide
  have hdescent : baseEnd_1782742 < baseStart_1782742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782815 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_1782815 : Nat := 118140960795 + 1782815 * 2 ^ 59
def prefixEnd_1782815 : Nat := 4983230072969 + 3 ^ 40 * 1782815 * 2
def baseEnd_1782815 : Nat := 406862672464687760805995

theorem tailTrace_1782815 : CollatzResearch.WordTrace tailWord_1782815 prefixEnd_1782815 406862672464687760805995 := by
  unfold tailWord_1782815
  simp only [CollatzResearch.WordTrace]
  refine ⟨65024605036173210406173899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43349736690782140270782599 65024605036173210406173899)
  ·
    refine ⟨97536907554259815609260849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65024605036173210406173899 97536907554259815609260849)
    ·
      refine ⟨73152680665694861706945637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97536907554259815609260849 73152680665694861706945637)
      ·
        refine ⟨13716127624817786570052307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73152680665694861706945637 13716127624817786570052307)
        ·
          refine ⟨20574191437226679855078461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716127624817786570052307 20574191437226679855078461)
          ·
            refine ⟨7715321788960004945654423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20574191437226679855078461 7715321788960004945654423)
            ·
              refine ⟨11572982683440007418481635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715321788960004945654423 11572982683440007418481635)
              ·
                refine ⟨17359474025160011127722453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11572982683440007418481635 17359474025160011127722453)
                ·
                  refine ⟨406862672464687760805995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17359474025160011127722453 406862672464687760805995)
                  ·
                    rfl

theorem cell21_1782815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_1782815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782815 prefixEnd_1782815 := by exact prefixLift 1782815
  have htrace : WordTrace (prefixWord ++ tailWord_1782815) baseStart_1782815 baseEnd_1782815 := by
    simpa [prefixWord, tailWord_1782815, baseEnd_1782815] using wordTrace_append hprefix tailTrace_1782815
  have hstable : (prefixWord ++ tailWord_1782815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782815).length < 2 ^ (prefixWord ++ tailWord_1782815).sum := by decide
  have hdescent : baseEnd_1782815 < baseStart_1782815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782818 : List Nat := [3, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1782818 : Nat := 118140960795 + 1782818 * 2 ^ 59
def prefixEnd_1782818 : Nat := 4983230072969 + 3 ^ 40 * 1782818 * 2
def baseEnd_1782818 : Nat := 135621119035186807418663

theorem tailTrace_1782818 : CollatzResearch.WordTrace tailWord_1782818 prefixEnd_1782818 135621119035186807418663 := by
  unfold tailWord_1782818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16256178613790585479633277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43349809636774894612355405 16256178613790585479633277)
  ·
    refine ⟨6096066980171469554862479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16256178613790585479633277 6096066980171469554862479)
    ·
      refine ⟨9144100470257204332293719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096066980171469554862479 9144100470257204332293719)
      ·
        refine ⟨13716150705385806498440579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9144100470257204332293719 13716150705385806498440579)
        ·
          refine ⟨20574226058078709747660869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716150705385806498440579 20574226058078709747660869)
          ·
            refine ⟨3857667385889758077686413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20574226058078709747660869 3857667385889758077686413)
            ·
              refine ⟨1446625269708659279132405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3857667385889758077686413 1446625269708659279132405)
              ·
                refine ⟨135621119035186807418663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1446625269708659279132405 135621119035186807418663)
                ·
                  rfl

theorem cell21_1782818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1782818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782818 prefixEnd_1782818 := by exact prefixLift 1782818
  have htrace : WordTrace (prefixWord ++ tailWord_1782818) baseStart_1782818 baseEnd_1782818 := by
    simpa [prefixWord, tailWord_1782818, baseEnd_1782818] using wordTrace_append hprefix tailTrace_1782818
  have hstable : (prefixWord ++ tailWord_1782818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782818).length < 2 ^ (prefixWord ++ tailWord_1782818).sum := by decide
  have hdescent : baseEnd_1782818 < baseStart_1782818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782849 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_1782849 : Nat := 118140960795 + 1782849 * 2 ^ 59
def prefixEnd_1782849 : Nat := 4983230072969 + 3 ^ 40 * 1782849 * 2
def baseEnd_1782849 : Nat := 406870431727911257239259

theorem tailTrace_1782849 : CollatzResearch.WordTrace tailWord_1782849 prefixEnd_1782849 406870431727911257239259 := by
  unfold tailWord_1782849
  simp only [CollatzResearch.WordTrace]
  refine ⟨65025845118050034212911601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43350563412033356141941067 65025845118050034212911601)
  ·
    refine ⟨48769383838537525659683701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65025845118050034212911601 48769383838537525659683701)
    ·
      refine ⟨4572129734862893030595347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48769383838537525659683701 4572129734862893030595347)
      ·
        refine ⟨6858194602294339545893021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572129734862893030595347 6858194602294339545893021)
        ·
          refine ⟨2571822975860377329709883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6858194602294339545893021 2571822975860377329709883)
          ·
            refine ⟨3857734463790565994564825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571822975860377329709883 3857734463790565994564825)
            ·
              refine ⟨2893300847842924495923619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857734463790565994564825 2893300847842924495923619)
              ·
                refine ⟨4339951271764386743885429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893300847842924495923619 4339951271764386743885429)
                ·
                  refine ⟨406870431727911257239259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4339951271764386743885429 406870431727911257239259)
                  ·
                    rfl

theorem cell21_1782849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_1782849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782849 prefixEnd_1782849 := by exact prefixLift 1782849
  have htrace : WordTrace (prefixWord ++ tailWord_1782849) baseStart_1782849 baseEnd_1782849 := by
    simpa [prefixWord, tailWord_1782849, baseEnd_1782849] using wordTrace_append hprefix tailTrace_1782849
  have hstable : (prefixWord ++ tailWord_1782849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782849).length < 2 ^ (prefixWord ++ tailWord_1782849).sum := by decide
  have hdescent : baseEnd_1782849 < baseStart_1782849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782860 : List Nat := [2, 2, 1, 3, 1, 1, 1, 10]
def baseStart_1782860 : Nat := 118140960795 + 1782860 * 2 ^ 59
def prefixEnd_1782860 : Nat := 4983230072969 + 3 ^ 40 * 1782860 * 2
def baseEnd_1782860 : Nat := 135624314025925894185301

theorem tailTrace_1782860 : CollatzResearch.WordTrace tailWord_1782860 prefixEnd_1782860 135624314025925894185301 := by
  unfold tailWord_1782860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32513123160505091545781017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43350830880673455394374689 32513123160505091545781017)
  ·
    refine ⟨24384842370378818659335763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32513123160505091545781017 24384842370378818659335763)
    ·
      refine ⟨36577263555568227989003645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24384842370378818659335763 36577263555568227989003645)
      ·
        refine ⟨13716473833338085495876367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36577263555568227989003645 13716473833338085495876367)
        ·
          refine ⟨20574710750007128243814551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716473833338085495876367 20574710750007128243814551)
          ·
            refine ⟨30862066125010692365721827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574710750007128243814551 30862066125010692365721827)
            ·
              refine ⟨46293099187516038548582741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30862066125010692365721827 46293099187516038548582741)
              ·
                refine ⟨135624314025925894185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46293099187516038548582741 135624314025925894185301)
                ·
                  rfl

theorem cell21_1782860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_1782860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782860 prefixEnd_1782860 := by exact prefixLift 1782860
  have htrace : WordTrace (prefixWord ++ tailWord_1782860) baseStart_1782860 baseEnd_1782860 := by
    simpa [prefixWord, tailWord_1782860, baseEnd_1782860] using wordTrace_append hprefix tailTrace_1782860
  have hstable : (prefixWord ++ tailWord_1782860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782860).length < 2 ^ (prefixWord ++ tailWord_1782860).sum := by decide
  have hdescent : baseEnd_1782860 < baseStart_1782860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782967 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_1782967 : Nat := 118140960795 + 1782967 * 2 ^ 59
def prefixEnd_1782967 : Nat := 4983230072969 + 3 ^ 40 * 1782967 * 2
def baseEnd_1782967 : Nat := 406897360935569274272351

theorem tailTrace_1782967 : CollatzResearch.WordTrace tailWord_1782967 prefixEnd_1782967 406897360935569274272351 := by
  unfold tailWord_1782967
  simp only [CollatzResearch.WordTrace]
  refine ⟨65030148931622540365707155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43353432621081693577138103 65030148931622540365707155)
  ·
    refine ⟨97545223397433810548560733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65030148931622540365707155 97545223397433810548560733)
    ·
      refine ⟨36579458774037678955710275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97545223397433810548560733 36579458774037678955710275)
      ·
        refine ⟨54869188161056518433565413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36579458774037678955710275 54869188161056518433565413)
        ·
          refine ⟨10287972780198097206293515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54869188161056518433565413 10287972780198097206293515)
          ·
            refine ⟨15431959170297145809440273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287972780198097206293515 15431959170297145809440273)
            ·
              refine ⟨11573969377722859357080205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15431959170297145809440273 11573969377722859357080205)
              ·
                refine ⟨4340238516646072258905077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11573969377722859357080205 4340238516646072258905077)
                ·
                  refine ⟨406897360935569274272351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340238516646072258905077 406897360935569274272351)
                  ·
                    rfl

theorem cell21_1782967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_1782967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782967 prefixEnd_1782967 := by exact prefixLift 1782967
  have htrace : WordTrace (prefixWord ++ tailWord_1782967) baseStart_1782967 baseEnd_1782967 := by
    simpa [prefixWord, tailWord_1782967, baseEnd_1782967] using wordTrace_append hprefix tailTrace_1782967
  have hstable : (prefixWord ++ tailWord_1782967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782967).length < 2 ^ (prefixWord ++ tailWord_1782967).sum := by decide
  have hdescent : baseEnd_1782967 < baseStart_1782967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782981 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1782981 : Nat := 118140960795 + 1782981 * 2 ^ 59
def prefixEnd_1782981 : Nat := 4983230072969 + 3 ^ 40 * 1782981 * 2
def baseEnd_1782981 : Nat := 406900555926308361038989

theorem tailTrace_1782981 : CollatzResearch.WordTrace tailWord_1782981 prefixEnd_1782981 406900555926308361038989 := by
  unfold tailWord_1782981
  simp only [CollatzResearch.WordTrace]
  refine ⟨65030659553571820756716797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43353773035714547171144531 65030659553571820756716797)
  ·
    refine ⟨24386497332589432783768799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65030659553571820756716797 24386497332589432783768799)
    ·
      refine ⟨36579745998884149175653199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24386497332589432783768799 36579745998884149175653199)
      ·
        refine ⟨54869618998326223763479799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36579745998884149175653199 54869618998326223763479799)
        ·
          refine ⟨82304428497489335645219699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54869618998326223763479799 82304428497489335645219699)
          ·
            refine ⟨123456642746234003467829549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82304428497489335645219699 123456642746234003467829549)
            ·
              refine ⟨46296241029837751300436081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123456642746234003467829549 46296241029837751300436081)
              ·
                refine ⟨34722180772378313475327061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46296241029837751300436081 34722180772378313475327061)
                ·
                  refine ⟨406900555926308361038989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34722180772378313475327061 406900555926308361038989)
                  ·
                    rfl

theorem cell21_1782981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1782981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1782981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1782981 prefixEnd_1782981 := by exact prefixLift 1782981
  have htrace : WordTrace (prefixWord ++ tailWord_1782981) baseStart_1782981 baseEnd_1782981 := by
    simpa [prefixWord, tailWord_1782981, baseEnd_1782981] using wordTrace_append hprefix tailTrace_1782981
  have hstable : (prefixWord ++ tailWord_1782981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782981).length < 2 ^ (prefixWord ++ tailWord_1782981).sum := by decide
  have hdescent : baseEnd_1782981 < baseStart_1782981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783015 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_1783015 : Nat := 118140960795 + 1783015 * 2 ^ 59
def prefixEnd_1783015 : Nat := 4983230072969 + 3 ^ 40 * 1783015 * 2
def baseEnd_1783015 : Nat := 406908315189531857472253

theorem tailTrace_1783015 : CollatzResearch.WordTrace tailWord_1783015 prefixEnd_1783015 406908315189531857472253 := by
  unfold tailWord_1783015
  simp only [CollatzResearch.WordTrace]
  refine ⟨65031899635448644563454499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43354599756965763042302999 65031899635448644563454499)
  ·
    refine ⟨97547849453172966845181749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65031899635448644563454499 97547849453172966845181749)
    ·
      refine ⟨9145110886234965641735789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97547849453172966845181749 9145110886234965641735789)
      ·
        refine ⟨3429416582338112115650921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9145110886234965641735789 3429416582338112115650921)
        ·
          refine ⟨2572062436753584086738191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429416582338112115650921 2572062436753584086738191)
          ·
            refine ⟨3858093655130376130107287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572062436753584086738191 3858093655130376130107287)
            ·
              refine ⟨5787140482695564195160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858093655130376130107287 5787140482695564195160931)
              ·
                refine ⟨8680710724043346292741397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787140482695564195160931 8680710724043346292741397)
                ·
                  refine ⟨406908315189531857472253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8680710724043346292741397 406908315189531857472253)
                  ·
                    rfl

theorem cell21_1783015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_1783015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783015 prefixEnd_1783015 := by exact prefixLift 1783015
  have htrace : WordTrace (prefixWord ++ tailWord_1783015) baseStart_1783015 baseEnd_1783015 := by
    simpa [prefixWord, tailWord_1783015, baseEnd_1783015] using wordTrace_append hprefix tailTrace_1783015
  have hstable : (prefixWord ++ tailWord_1783015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783015).length < 2 ^ (prefixWord ++ tailWord_1783015).sum := by decide
  have hdescent : baseEnd_1783015 < baseStart_1783015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783043 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_1783043 : Nat := 118140960795 + 1783043 * 2 ^ 59
def prefixEnd_1783043 : Nat := 4983230072969 + 3 ^ 40 * 1783043 * 2
def baseEnd_1783043 : Nat := 406914705171010031005529

theorem tailTrace_1783043 : CollatzResearch.WordTrace tailWord_1783043 prefixEnd_1783043 406914705171010031005529 := by
  unfold tailWord_1783043
  simp only [CollatzResearch.WordTrace]
  refine ⟨65032920879347205345473783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43355280586231470230315855 65032920879347205345473783)
  ·
    refine ⟨97549381319020808018210675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65032920879347205345473783 97549381319020808018210675)
    ·
      refine ⟨146324071978531212027316013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97549381319020808018210675 146324071978531212027316013)
      ·
        refine ⟨54871526991949204510243505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146324071978531212027316013 54871526991949204510243505)
        ·
          refine ⟨41153645243961903382682629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54871526991949204510243505 41153645243961903382682629)
          ·
            refine ⟨7716308483242856884252993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41153645243961903382682629 7716308483242856884252993)
            ·
              refine ⟨5787231362432142663189745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716308483242856884252993 5787231362432142663189745)
              ·
                refine ⟨4340423521824106997392309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787231362432142663189745 4340423521824106997392309)
                ·
                  refine ⟨406914705171010031005529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340423521824106997392309 406914705171010031005529)
                  ·
                    rfl

theorem cell21_1783043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_1783043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783043 prefixEnd_1783043 := by exact prefixLift 1783043
  have htrace : WordTrace (prefixWord ++ tailWord_1783043) baseStart_1783043 baseEnd_1783043 := by
    simpa [prefixWord, tailWord_1783043, baseEnd_1783043] using wordTrace_append hprefix tailTrace_1783043
  have hstable : (prefixWord ++ tailWord_1783043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783043).length < 2 ^ (prefixWord ++ tailWord_1783043).sum := by decide
  have hdescent : baseEnd_1783043 < baseStart_1783043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783057 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_1783057 : Nat := 118140960795 + 1783057 * 2 ^ 59
def prefixEnd_1783057 : Nat := 4983230072969 + 3 ^ 40 * 1783057 * 2
def baseEnd_1783057 : Nat := 406917900161749117772167

theorem tailTrace_1783057 : CollatzResearch.WordTrace tailWord_1783057 prefixEnd_1783057 406917900161749117772167 := by
  unfold tailWord_1783057
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033431501296485736483425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43355621000864323824322283 65033431501296485736483425)
  ·
    refine ⟨48775073625972364302362569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65033431501296485736483425 48775073625972364302362569)
    ·
      refine ⟨36581305219479273226771927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48775073625972364302362569 36581305219479273226771927)
      ·
        refine ⟨54871957829218909840157891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36581305219479273226771927 54871957829218909840157891)
        ·
          refine ⟨82307936743828364760236837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54871957829218909840157891 82307936743828364760236837)
          ·
            refine ⟨15432738139467818392544407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82307936743828364760236837 15432738139467818392544407)
            ·
              refine ⟨23149107209201727588816611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15432738139467818392544407 23149107209201727588816611)
              ·
                refine ⟨34723660813802591383224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23149107209201727588816611 34723660813802591383224917)
                ·
                  refine ⟨406917900161749117772167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34723660813802591383224917 406917900161749117772167)
                  ·
                    rfl

theorem cell21_1783057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_1783057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783057 prefixEnd_1783057 := by exact prefixLift 1783057
  have htrace : WordTrace (prefixWord ++ tailWord_1783057) baseStart_1783057 baseEnd_1783057 := by
    simpa [prefixWord, tailWord_1783057, baseEnd_1783057] using wordTrace_append hprefix tailTrace_1783057
  have hstable : (prefixWord ++ tailWord_1783057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783057).length < 2 ^ (prefixWord ++ tailWord_1783057).sum := by decide
  have hdescent : baseEnd_1783057 < baseStart_1783057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783088 : List Nat := [2, 1, 1, 1, 2, 2, 6, 6]
def baseStart_1783088 : Nat := 118140960795 + 1783088 * 2 ^ 59
def prefixEnd_1783088 : Nat := 4983230072969 + 3 ^ 40 * 1783088 * 2
def baseEnd_1783088 : Nat := 135641658261366650918479

theorem tailTrace_1783088 : CollatzResearch.WordTrace tailWord_1783088 prefixEnd_1783088 135641658261366650918479 := by
  unfold tailWord_1783088
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517281082092089015430959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43356374776122785353907945 32517281082092089015430959)
  ·
    refine ⟨48775921623138133523146439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32517281082092089015430959 48775921623138133523146439)
    ·
      refine ⟨73163882434707200284719659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48775921623138133523146439 73163882434707200284719659)
      ·
        refine ⟨109745823652060800427079489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73163882434707200284719659 109745823652060800427079489)
        ·
          refine ⟨82309367739045600320309617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109745823652060800427079489 82309367739045600320309617)
          ·
            refine ⟨61732025804284200240232213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82309367739045600320309617 61732025804284200240232213)
            ·
              refine ⟨2893688709575821886260885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61732025804284200240232213 2893688709575821886260885)
              ·
                refine ⟨135641658261366650918479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2893688709575821886260885 135641658261366650918479)
                ·
                  rfl

theorem cell21_1783088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_1783088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783088 prefixEnd_1783088 := by exact prefixLift 1783088
  have htrace : WordTrace (prefixWord ++ tailWord_1783088) baseStart_1783088 baseEnd_1783088 := by
    simpa [prefixWord, tailWord_1783088, baseEnd_1783088] using wordTrace_append hprefix tailTrace_1783088
  have hstable : (prefixWord ++ tailWord_1783088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783088).length < 2 ^ (prefixWord ++ tailWord_1783088).sum := by decide
  have hdescent : baseEnd_1783088 < baseStart_1783088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783091 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 4]
def baseStart_1783091 : Nat := 118140960795 + 1783091 * 2 ^ 59
def prefixEnd_1783091 : Nat := 4983230072969 + 3 ^ 40 * 1783091 * 2
def baseEnd_1783091 : Nat := 406925659424972614205431

theorem tailTrace_1783091 : CollatzResearch.WordTrace tailWord_1783091 prefixEnd_1783091 406925659424972614205431 := by
  unfold tailWord_1783091
  simp only [CollatzResearch.WordTrace]
  refine ⟨65034671583173309543221127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43356447722115539695480751 65034671583173309543221127)
  ·
    refine ⟨97552007374759964314831691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65034671583173309543221127 97552007374759964314831691)
    ·
      refine ⟨146328011062139946472247537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97552007374759964314831691 146328011062139946472247537)
      ·
        refine ⟨109746008296604959854185653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146328011062139946472247537 109746008296604959854185653)
        ·
          refine ⟨10288688277806714986329905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109746008296604959854185653 10288688277806714986329905)
          ·
            refine ⟨7716516208355036239747429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288688277806714986329905 7716516208355036239747429)
            ·
              refine ⟨1446846789066569294952643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7716516208355036239747429 1446846789066569294952643)
              ·
                refine ⟨2170270183599853942428965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446846789066569294952643 2170270183599853942428965)
                ·
                  refine ⟨406925659424972614205431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170270183599853942428965 406925659424972614205431)
                  ·
                    rfl

theorem cell21_1783091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_1783091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783091 prefixEnd_1783091 := by exact prefixLift 1783091
  have htrace : WordTrace (prefixWord ++ tailWord_1783091) baseStart_1783091 baseEnd_1783091 := by
    simpa [prefixWord, tailWord_1783091, baseEnd_1783091] using wordTrace_append hprefix tailTrace_1783091
  have hstable : (prefixWord ++ tailWord_1783091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783091).length < 2 ^ (prefixWord ++ tailWord_1783091).sum := by decide
  have hdescent : baseEnd_1783091 < baseStart_1783091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783105 : List Nat := [1, 2, 5, 2, 1, 1, 2, 7]
def baseStart_1783105 : Nat := 118140960795 + 1783105 * 2 ^ 59
def prefixEnd_1783105 : Nat := 4983230072969 + 3 ^ 40 * 1783105 * 2
def baseEnd_1783105 : Nat := 135642951471903900324023

theorem tailTrace_1783105 : CollatzResearch.WordTrace tailWord_1783105 prefixEnd_1783105 135642951471903900324023 := by
  unfold tailWord_1783105
  simp only [CollatzResearch.WordTrace]
  refine ⟨65035182205122589934230769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43356788136748393289487179 65035182205122589934230769)
  ·
    refine ⟨48776386653841942450673077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65035182205122589934230769 48776386653841942450673077)
    ·
      refine ⟨4572786248797682104750601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48776386653841942450673077 4572786248797682104750601)
      ·
        refine ⟨3429589686598261578562951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4572786248797682104750601 3429589686598261578562951)
        ·
          refine ⟨5144384529897392367844427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429589686598261578562951 5144384529897392367844427)
          ·
            refine ⟨7716576794846088551766641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144384529897392367844427 7716576794846088551766641)
            ·
              refine ⟨5787432596134566413824981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716576794846088551766641 5787432596134566413824981)
              ·
                refine ⟨135642951471903900324023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5787432596134566413824981 135642951471903900324023)
                ·
                  rfl

theorem cell21_1783105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_1783105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783105 prefixEnd_1783105 := by exact prefixLift 1783105
  have htrace : WordTrace (prefixWord ++ tailWord_1783105) baseStart_1783105 baseEnd_1783105 := by
    simpa [prefixWord, tailWord_1783105, baseEnd_1783105] using wordTrace_append hprefix tailTrace_1783105
  have hstable : (prefixWord ++ tailWord_1783105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783105).length < 2 ^ (prefixWord ++ tailWord_1783105).sum := by decide
  have hdescent : baseEnd_1783105 < baseStart_1783105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783170 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1783170 : Nat := 118140960795 + 1783170 * 2 ^ 59
def prefixEnd_1783170 : Nat := 4983230072969 + 3 ^ 40 * 1783170 * 2
def baseEnd_1783170 : Nat := 406943688301286032388603

theorem tailTrace_1783170 : CollatzResearch.WordTrace tailWord_1783170 prefixEnd_1783170 406943688301286032388603 := by
  unfold tailWord_1783170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259388237471776508836741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43358368633258070690231309 16259388237471776508836741)
  ·
    refine ⟨3048635294525958095406889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16259388237471776508836741 3048635294525958095406889)
    ·
      refine ⟨2286476470894468571555167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3048635294525958095406889 2286476470894468571555167)
      ·
        refine ⟨3429714706341702857332751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286476470894468571555167 3429714706341702857332751)
        ·
          refine ⟨5144572059512554285999127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429714706341702857332751 5144572059512554285999127)
          ·
            refine ⟨7716858089268831428998691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144572059512554285999127 7716858089268831428998691)
            ·
              refine ⟨11575287133903247143498037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716858089268831428998691 11575287133903247143498037)
              ·
                refine ⟨1085183168803429419702941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11575287133903247143498037 1085183168803429419702941)
                ·
                  refine ⟨406943688301286032388603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085183168803429419702941 406943688301286032388603)
                  ·
                    rfl

theorem cell21_1783170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1783170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783170 prefixEnd_1783170 := by exact prefixLift 1783170
  have htrace : WordTrace (prefixWord ++ tailWord_1783170) baseStart_1783170 baseEnd_1783170 := by
    simpa [prefixWord, tailWord_1783170, baseEnd_1783170] using wordTrace_append hprefix tailTrace_1783170
  have hstable : (prefixWord ++ tailWord_1783170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783170).length < 2 ^ (prefixWord ++ tailWord_1783170).sum := by decide
  have hdescent : baseEnd_1783170 < baseStart_1783170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783375 : List Nat := [1, 1, 2, 1, 1, 2, 3, 10]
def baseStart_1783375 : Nat := 118140960795 + 1783375 * 2 ^ 59
def prefixEnd_1783375 : Nat := 4983230072969 + 3 ^ 40 * 1783375 * 2
def baseEnd_1783375 : Nat := 135663490698083743823839

theorem tailTrace_1783375 : CollatzResearch.WordTrace tailWord_1783375 prefixEnd_1783375 135663490698083743823839 := by
  unfold tailWord_1783375
  simp only [CollatzResearch.WordTrace]
  refine ⟨65045029914144426046559579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43363353276096284031039719 65045029914144426046559579)
  ·
    refine ⟨97567544871216639069839369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65045029914144426046559579 97567544871216639069839369)
    ·
      refine ⟨73175658653412479302379527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97567544871216639069839369 73175658653412479302379527)
      ·
        refine ⟨109763487980118718953569291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73175658653412479302379527 109763487980118718953569291)
        ·
          refine ⟨164645231970178078430353937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109763487980118718953569291 164645231970178078430353937)
          ·
            refine ⟨123483923977633558822765453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164645231970178078430353937 123483923977633558822765453)
            ·
              refine ⟨46306471491612584558537045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123483923977633558822765453 46306471491612584558537045)
              ·
                refine ⟨135663490698083743823839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46306471491612584558537045 135663490698083743823839)
                ·
                  rfl

theorem cell21_1783375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_1783375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783375 prefixEnd_1783375 := by exact prefixLift 1783375
  have htrace : WordTrace (prefixWord ++ tailWord_1783375) baseStart_1783375 baseEnd_1783375 := by
    simpa [prefixWord, tailWord_1783375, baseEnd_1783375] using wordTrace_append hprefix tailTrace_1783375
  have hstable : (prefixWord ++ tailWord_1783375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783375).length < 2 ^ (prefixWord ++ tailWord_1783375).sum := by decide
  have hdescent : baseEnd_1783375 < baseStart_1783375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783530 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1783530 : Nat := 118140960795 + 1783530 * 2 ^ 59
def prefixEnd_1783530 : Nat := 4983230072969 + 3 ^ 40 * 1783530 * 2
def baseEnd_1783530 : Nat := 407025845206005406387867

theorem tailTrace_1783530 : CollatzResearch.WordTrace tailWord_1783530 prefixEnd_1783530 407025845206005406387867 := by
  unfold tailWord_1783530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16262670807145721879613011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43367122152388591678968029 16262670807145721879613011)
  ·
    refine ⟨24394006210718582819419517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16262670807145721879613011 24394006210718582819419517)
    ·
      refine ⟨9147752329019468557282319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24394006210718582819419517 9147752329019468557282319)
      ·
        refine ⟨13721628493529202835923479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147752329019468557282319 13721628493529202835923479)
        ·
          refine ⟨20582442740293804253885219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721628493529202835923479 20582442740293804253885219)
          ·
            refine ⟨30873664110440706380827829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20582442740293804253885219 30873664110440706380827829)
            ·
              refine ⟨2894406010353816223202609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30873664110440706380827829 2894406010353816223202609)
              ·
                refine ⟨2170804507765362167401957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2894406010353816223202609 2170804507765362167401957)
                ·
                  refine ⟨407025845206005406387867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170804507765362167401957 407025845206005406387867)
                  ·
                    rfl

theorem cell21_1783530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1783530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783530 prefixEnd_1783530 := by exact prefixLift 1783530
  have htrace : WordTrace (prefixWord ++ tailWord_1783530) baseStart_1783530 baseEnd_1783530 := by
    simpa [prefixWord, tailWord_1783530, baseEnd_1783530] using wordTrace_append hprefix tailTrace_1783530
  have hstable : (prefixWord ++ tailWord_1783530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783530).length < 2 ^ (prefixWord ++ tailWord_1783530).sum := by decide
  have hdescent : baseEnd_1783530 < baseStart_1783530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783589 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1783589 : Nat := 118140960795 + 1783589 * 2 ^ 59
def prefixEnd_1783589 : Nat := 4983230072969 + 3 ^ 40 * 1783589 * 2
def baseEnd_1783589 : Nat := 407039309809834414904413

theorem tailTrace_1783589 : CollatzResearch.WordTrace tailWord_1783589 prefixEnd_1783589 407039309809834414904413 := by
  unfold tailWord_1783589
  simp only [CollatzResearch.WordTrace]
  refine ⟨65052835135369140594849821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43368556756912760396566547 65052835135369140594849821)
  ·
    refine ⟨24394813175763427723068683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65052835135369140594849821 24394813175763427723068683)
    ·
      refine ⟨36592219763645141584603025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24394813175763427723068683 36592219763645141584603025)
      ·
        refine ⟨27444164822733856188452269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36592219763645141584603025 27444164822733856188452269)
        ·
          refine ⟨10291561808525196070669601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27444164822733856188452269 10291561808525196070669601)
          ·
            refine ⟨7718671356393897053002201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291561808525196070669601 7718671356393897053002201)
            ·
              refine ⟨5789003517295422789751651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718671356393897053002201 5789003517295422789751651)
              ·
                refine ⟨8683505275943134184627477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789003517295422789751651 8683505275943134184627477)
                ·
                  refine ⟨407039309809834414904413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8683505275943134184627477 407039309809834414904413)
                  ·
                    rfl

theorem cell21_1783589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1783589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783589 prefixEnd_1783589 := by exact prefixLift 1783589
  have htrace : WordTrace (prefixWord ++ tailWord_1783589) baseStart_1783589 baseEnd_1783589 := by
    simpa [prefixWord, tailWord_1783589, baseEnd_1783589] using wordTrace_append hprefix tailTrace_1783589
  have hstable : (prefixWord ++ tailWord_1783589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783589).length < 2 ^ (prefixWord ++ tailWord_1783589).sum := by decide
  have hdescent : baseEnd_1783589 < baseStart_1783589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783592 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_1783592 : Nat := 118140960795 + 1783592 * 2 ^ 59
def prefixEnd_1783592 : Nat := 4983230072969 + 3 ^ 40 * 1783592 * 2
def baseEnd_1783592 : Nat := 407039994450707076354407

theorem tailTrace_1783592 : CollatzResearch.WordTrace tailWord_1783592 prefixEnd_1783592 407039994450707076354407 := by
  unfold tailWord_1783592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526472277179136053604515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43368629702905514738139353 32526472277179136053604515)
  ·
    refine ⟨48789708415768704080406773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32526472277179136053604515 48789708415768704080406773)
    ·
      refine ⟨4574035163978316007538135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48789708415768704080406773 4574035163978316007538135)
      ·
        refine ⟨6861052745967474011307203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574035163978316007538135 6861052745967474011307203)
        ·
          refine ⟨10291579118951211016960805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861052745967474011307203 10291579118951211016960805)
          ·
            refine ⟨1929671084803352065680151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10291579118951211016960805 1929671084803352065680151)
            ·
              refine ⟨2894506627205028098520227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929671084803352065680151 2894506627205028098520227)
              ·
                refine ⟨4341759940807542147780341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894506627205028098520227 4341759940807542147780341)
                ·
                  refine ⟨407039994450707076354407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4341759940807542147780341 407039994450707076354407)
                  ·
                    rfl

theorem cell21_1783592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_1783592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783592 prefixEnd_1783592 := by exact prefixLift 1783592
  have htrace : WordTrace (prefixWord ++ tailWord_1783592) baseStart_1783592 baseEnd_1783592 := by
    simpa [prefixWord, tailWord_1783592, baseEnd_1783592] using wordTrace_append hprefix tailTrace_1783592
  have hstable : (prefixWord ++ tailWord_1783592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783592).length < 2 ^ (prefixWord ++ tailWord_1783592).sum := by decide
  have hdescent : baseEnd_1783592 < baseStart_1783592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783665 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_1783665 : Nat := 118140960795 + 1783665 * 2 ^ 59
def prefixEnd_1783665 : Nat := 4983230072969 + 3 ^ 40 * 1783665 * 2
def baseEnd_1783665 : Nat := 407056654045275171637591

theorem tailTrace_1783665 : CollatzResearch.WordTrace tailWord_1783665 prefixEnd_1783665 407056654045275171637591 := by
  unfold tailWord_1783665
  simp only [CollatzResearch.WordTrace]
  refine ⟨65055607083093805574616449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43370404722062537049744299 65055607083093805574616449)
  ·
    refine ⟨48791705312320354180962337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65055607083093805574616449 48791705312320354180962337)
    ·
      refine ⟨36593778984240265635721753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48791705312320354180962337 36593778984240265635721753)
      ·
        refine ⟨27445334238180199226791315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36593778984240265635721753 27445334238180199226791315)
        ·
          refine ⟨41168001357270298840186973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27445334238180199226791315 41168001357270298840186973)
          ·
            refine ⟨15438000508976362065070115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41168001357270298840186973 15438000508976362065070115)
            ·
              refine ⟨23157000763464543097605173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438000508976362065070115 23157000763464543097605173)
              ·
                refine ⟨2170968821574800915400485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23157000763464543097605173 2170968821574800915400485)
                ·
                  refine ⟨407056654045275171637591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170968821574800915400485 407056654045275171637591)
                  ·
                    rfl

theorem cell21_1783665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_1783665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783665 prefixEnd_1783665 := by exact prefixLift 1783665
  have htrace : WordTrace (prefixWord ++ tailWord_1783665) baseStart_1783665 baseEnd_1783665 := by
    simpa [prefixWord, tailWord_1783665, baseEnd_1783665] using wordTrace_append hprefix tailTrace_1783665
  have hstable : (prefixWord ++ tailWord_1783665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783665).length < 2 ^ (prefixWord ++ tailWord_1783665).sum := by decide
  have hdescent : baseEnd_1783665 < baseStart_1783665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783702 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1783702 : Nat := 118140960795 + 1783702 * 2 ^ 59
def prefixEnd_1783702 : Nat := 4983230072969 + 3 ^ 40 * 1783702 * 2
def baseEnd_1783702 : Nat := 407065097949371329520849

theorem tailTrace_1783702 : CollatzResearch.WordTrace tailWord_1783702 prefixEnd_1783702 407065097949371329520849 := by
  unfold tailWord_1783702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066059786497485055857085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43371304389306507262475573 4066059786497485055857085)
  ·
    refine ⟨1524772419936556895946407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4066059786497485055857085 1524772419936556895946407)
    ·
      refine ⟨2287158629904835343919611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524772419936556895946407 2287158629904835343919611)
      ·
        refine ⟨3430737944857253015879417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287158629904835343919611 3430737944857253015879417)
        ·
          refine ⟨2573053458642939761909563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3430737944857253015879417 2573053458642939761909563)
          ·
            refine ⟨3859580187964409642864345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573053458642939761909563 3859580187964409642864345)
            ·
              refine ⟨2894685140973307232148259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859580187964409642864345 2894685140973307232148259)
              ·
                refine ⟨4342027711459960848222389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894685140973307232148259 4342027711459960848222389)
                ·
                  refine ⟨407065097949371329520849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4342027711459960848222389 407065097949371329520849)
                  ·
                    rfl

theorem cell21_1783702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1783702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783702 prefixEnd_1783702 := by exact prefixLift 1783702
  have htrace : WordTrace (prefixWord ++ tailWord_1783702) baseStart_1783702 baseEnd_1783702 := by
    simpa [prefixWord, tailWord_1783702, baseEnd_1783702] using wordTrace_append hprefix tailTrace_1783702
  have hstable : (prefixWord ++ tailWord_1783702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783702).length < 2 ^ (prefixWord ++ tailWord_1783702).sum := by decide
  have hdescent : baseEnd_1783702 < baseStart_1783702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783724 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1783724 : Nat := 118140960795 + 1783724 * 2 ^ 59
def prefixEnd_1783724 : Nat := 4983230072969 + 3 ^ 40 * 1783724 * 2
def baseEnd_1783724 : Nat := 407070118649104180154137

theorem tailTrace_1783724 : CollatzResearch.WordTrace tailWord_1783724 prefixEnd_1783724 407070118649104180154137 := by
  unfold tailWord_1783724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32528879494940029325507113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43371839326586705767342817 32528879494940029325507113)
  ·
    refine ⟨24396659621205021994130335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32528879494940029325507113 24396659621205021994130335)
    ·
      refine ⟨36594989431807532991195503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24396659621205021994130335 36594989431807532991195503)
      ·
        refine ⟨54892484147711299486793255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36594989431807532991195503 54892484147711299486793255)
        ·
          refine ⟨82338726221566949230189883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54892484147711299486793255 82338726221566949230189883)
          ·
            refine ⟨123508089332350423845284825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82338726221566949230189883 123508089332350423845284825)
            ·
              refine ⟨92631066999262817883963619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123508089332350423845284825 92631066999262817883963619)
              ·
                refine ⟨138946600498894226825945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92631066999262817883963619 138946600498894226825945429)
                ·
                  refine ⟨407070118649104180154137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138946600498894226825945429 407070118649104180154137)
                  ·
                    rfl

theorem cell21_1783724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1783724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783724 prefixEnd_1783724 := by exact prefixLift 1783724
  have htrace : WordTrace (prefixWord ++ tailWord_1783724) baseStart_1783724 baseEnd_1783724 := by
    simpa [prefixWord, tailWord_1783724, baseEnd_1783724] using wordTrace_append hprefix tailTrace_1783724
  have hstable : (prefixWord ++ tailWord_1783724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783724).length < 2 ^ (prefixWord ++ tailWord_1783724).sum := by decide
  have hdescent : baseEnd_1783724 < baseStart_1783724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783741 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1783741 : Nat := 118140960795 + 1783741 * 2 ^ 59
def prefixEnd_1783741 : Nat := 4983230072969 + 3 ^ 40 * 1783741 * 2
def baseEnd_1783741 : Nat := 407073998280715928370769

theorem tailTrace_1783741 : CollatzResearch.WordTrace tailWord_1783741 prefixEnd_1783741 407073998280715928370769 := by
  unfold tailWord_1783741
  simp only [CollatzResearch.WordTrace]
  refine ⟨65058379030818470554383077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43372252687212313702922051 65058379030818470554383077)
  ·
    refine ⟨12198446068278463228946827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65058379030818470554383077 12198446068278463228946827)
    ·
      refine ⟨18297669102417694843420241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198446068278463228946827 18297669102417694843420241)
      ·
        refine ⟨13723251826813271132565181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18297669102417694843420241 13723251826813271132565181)
        ·
          refine ⟨5146219435054976674711943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13723251826813271132565181 5146219435054976674711943)
          ·
            refine ⟨7719329152582465012067915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146219435054976674711943 7719329152582465012067915)
            ·
              refine ⟨11578993728873697518101873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719329152582465012067915 11578993728873697518101873)
              ·
                refine ⟨8684245296655273138576405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11578993728873697518101873 8684245296655273138576405)
                ·
                  refine ⟨407073998280715928370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8684245296655273138576405 407073998280715928370769)
                  ·
                    rfl

theorem cell21_1783741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1783741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783741 prefixEnd_1783741 := by exact prefixLift 1783741
  have htrace : WordTrace (prefixWord ++ tailWord_1783741) baseStart_1783741 baseEnd_1783741 := by
    simpa [prefixWord, tailWord_1783741, baseEnd_1783741] using wordTrace_append hprefix tailTrace_1783741
  have hstable : (prefixWord ++ tailWord_1783741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783741).length < 2 ^ (prefixWord ++ tailWord_1783741).sum := by decide
  have hdescent : baseEnd_1783741 < baseStart_1783741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783775 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 4]
def baseStart_1783775 : Nat := 118140960795 + 1783775 * 2 ^ 59
def prefixEnd_1783775 : Nat := 4983230072969 + 3 ^ 40 * 1783775 * 2
def baseEnd_1783775 : Nat := 407081757543939424804033

theorem tailTrace_1783775 : CollatzResearch.WordTrace tailWord_1783775 prefixEnd_1783775 407081757543939424804033 := by
  unfold tailWord_1783775
  simp only [CollatzResearch.WordTrace]
  refine ⟨65059619112695294361120779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43373079408463529574080519 65059619112695294361120779)
  ·
    refine ⟨97589428669042941541681169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65059619112695294361120779 97589428669042941541681169)
    ·
      refine ⟨73192071501782206156260877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97589428669042941541681169 73192071501782206156260877)
      ·
        refine ⟨27447026813168327308597829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73192071501782206156260877 27447026813168327308597829)
        ·
          refine ⟨5146317527469061370362093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27447026813168327308597829 5146317527469061370362093)
          ·
            refine ⟨1929869072800898013885785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5146317527469061370362093 1929869072800898013885785)
            ·
              refine ⟨1447401804600673510414339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929869072800898013885785 1447401804600673510414339)
              ·
                refine ⟨2171102706901010265621509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447401804600673510414339 2171102706901010265621509)
                ·
                  refine ⟨407081757543939424804033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171102706901010265621509 407081757543939424804033)
                  ·
                    rfl

theorem cell21_1783775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_1783775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783775 prefixEnd_1783775 := by exact prefixLift 1783775
  have htrace : WordTrace (prefixWord ++ tailWord_1783775) baseStart_1783775 baseEnd_1783775 := by
    simpa [prefixWord, tailWord_1783775, baseEnd_1783775] using wordTrace_append hprefix tailTrace_1783775
  have hstable : (prefixWord ++ tailWord_1783775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783775).length < 2 ^ (prefixWord ++ tailWord_1783775).sum := by decide
  have hdescent : baseEnd_1783775 < baseStart_1783775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783786 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1783786 : Nat := 118140960795 + 1783786 * 2 ^ 59
def prefixEnd_1783786 : Nat := 4983230072969 + 3 ^ 40 * 1783786 * 2
def baseEnd_1783786 : Nat := 407084267893805850120677

theorem tailTrace_1783786 : CollatzResearch.WordTrace tailWord_1783786 prefixEnd_1783786 407084267893805850120677 := by
  unfold tailWord_1783786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265005078913860809942803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43373346877103628826514141 16265005078913860809942803)
  ·
    refine ⟨24397507618370791214914205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16265005078913860809942803 24397507618370791214914205)
    ·
      refine ⟨9149065356889046705592827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24397507618370791214914205 9149065356889046705592827)
      ·
        refine ⟨13723598035333570058389241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149065356889046705592827 13723598035333570058389241)
        ·
          refine ⟨10292698526500177543791931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13723598035333570058389241 10292698526500177543791931)
          ·
            refine ⟨15439047789750266315687897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10292698526500177543791931 15439047789750266315687897)
            ·
              refine ⟨11579285842312699736765923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15439047789750266315687897 11579285842312699736765923)
              ·
                refine ⟨17368928763469049605148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579285842312699736765923 17368928763469049605148885)
                ·
                  refine ⟨407084267893805850120677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17368928763469049605148885 407084267893805850120677)
                  ·
                    rfl

theorem cell21_1783786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1783786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783786 prefixEnd_1783786 := by exact prefixLift 1783786
  have htrace : WordTrace (prefixWord ++ tailWord_1783786) baseStart_1783786 baseEnd_1783786 := by
    simpa [prefixWord, tailWord_1783786, baseEnd_1783786] using wordTrace_append hprefix tailTrace_1783786
  have hstable : (prefixWord ++ tailWord_1783786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783786).length < 2 ^ (prefixWord ++ tailWord_1783786).sum := by decide
  have hdescent : baseEnd_1783786 < baseStart_1783786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783800 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_1783800 : Nat := 118140960795 + 1783800 * 2 ^ 59
def prefixEnd_1783800 : Nat := 4983230072969 + 3 ^ 40 * 1783800 * 2
def baseEnd_1783800 : Nat := 407087462884544936887315

theorem tailTrace_1783800 : CollatzResearch.WordTrace tailWord_1783800 prefixEnd_1783800 407087462884544936887315 := by
  unfold tailWord_1783800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530265468802361815390427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43373687291736482420520569 32530265468802361815390427)
  ·
    refine ⟨48795398203203542723085641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32530265468802361815390427 48795398203203542723085641)
    ·
      refine ⟨36596548652402657042314231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48795398203203542723085641 36596548652402657042314231)
      ·
        refine ⟨54894822978603985563471347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36596548652402657042314231 54894822978603985563471347)
        ·
          refine ⟨82342234467905978345207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54894822978603985563471347 82342234467905978345207021)
          ·
            refine ⟨30878337925464741879452633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82342234467905978345207021 30878337925464741879452633)
            ·
              refine ⟨23158753444098556409589475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30878337925464741879452633 23158753444098556409589475)
              ·
                refine ⟨34738130166147834614384213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23158753444098556409589475 34738130166147834614384213)
                ·
                  refine ⟨407087462884544936887315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34738130166147834614384213 407087462884544936887315)
                  ·
                    rfl

theorem cell21_1783800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_1783800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783800 prefixEnd_1783800 := by exact prefixLift 1783800
  have htrace : WordTrace (prefixWord ++ tailWord_1783800) baseStart_1783800 baseEnd_1783800 := by
    simpa [prefixWord, tailWord_1783800, baseEnd_1783800] using wordTrace_append hprefix tailTrace_1783800
  have hstable : (prefixWord ++ tailWord_1783800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783800).length < 2 ^ (prefixWord ++ tailWord_1783800).sum := by decide
  have hdescent : baseEnd_1783800 < baseStart_1783800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783879 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 3]
def baseStart_1783879 : Nat := 118140960795 + 1783879 * 2 ^ 59
def prefixEnd_1783879 : Nat := 4983230072969 + 3 ^ 40 * 1783879 * 2
def baseEnd_1783879 : Nat := 407105491760858355070487

theorem tailTrace_1783879 : CollatzResearch.WordTrace tailWord_1783879 prefixEnd_1783879 407105491760858355070487 := by
  unfold tailWord_1783879
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063412304318520122906691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43375608202879013415271127 65063412304318520122906691)
  ·
    refine ⟨97595118456477780184360037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65063412304318520122906691 97595118456477780184360037)
    ·
      refine ⟨18299084710589583784567507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97595118456477780184360037 18299084710589583784567507)
      ·
        refine ⟨27448627065884375676851261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299084710589583784567507 27448627065884375676851261)
        ·
          refine ⟨10293235149706640878819223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27448627065884375676851261 10293235149706640878819223)
          ·
            refine ⟨15439852724559961318228835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293235149706640878819223 15439852724559961318228835)
            ·
              refine ⟨23159779086839941977343253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439852724559961318228835 23159779086839941977343253)
              ·
                refine ⟨1085614644695622280187965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23159779086839941977343253 1085614644695622280187965)
                ·
                  refine ⟨407105491760858355070487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085614644695622280187965 407105491760858355070487)
                  ·
                    rfl

theorem cell21_1783879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].length) (baseStart_1783879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783879 prefixEnd_1783879 := by exact prefixLift 1783879
  have htrace : WordTrace (prefixWord ++ tailWord_1783879) baseStart_1783879 baseEnd_1783879 := by
    simpa [prefixWord, tailWord_1783879, baseEnd_1783879] using wordTrace_append hprefix tailTrace_1783879
  have hstable : (prefixWord ++ tailWord_1783879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783879).length < 2 ^ (prefixWord ++ tailWord_1783879).sum := by decide
  have hdescent : baseEnd_1783879 < baseStart_1783879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783989 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 3]
def baseStart_1783989 : Nat := 118140960795 + 1783989 * 2 ^ 59
def prefixEnd_1783989 : Nat := 4983230072969 + 3 ^ 40 * 1783989 * 2
def baseEnd_1783989 : Nat := 407130595259522608236929

theorem tailTrace_1783989 : CollatzResearch.WordTrace tailWord_1783989 prefixEnd_1783989 407130595259522608236929 := by
  unfold tailWord_1783989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65067424333920008909411021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43378282889280005939607347 65067424333920008909411021)
  ·
    refine ⟨24400284125220003341029133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65067424333920008909411021 24400284125220003341029133)
    ·
      refine ⟨9150106546957501252885925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24400284125220003341029133 9150106546957501252885925)
      ·
        refine ⟨1715644977554531484916111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9150106546957501252885925 1715644977554531484916111)
        ·
          refine ⟨2573467466331797227374167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715644977554531484916111 2573467466331797227374167)
          ·
            refine ⟨3860201199497695841061251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573467466331797227374167 3860201199497695841061251)
            ·
              refine ⟨5790301799246543761591877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860201199497695841061251 5790301799246543761591877)
              ·
                refine ⟨1085681587358726955298477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5790301799246543761591877 1085681587358726955298477)
                ·
                  refine ⟨407130595259522608236929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085681587358726955298477 407130595259522608236929)
                  ·
                    rfl

theorem cell21_1783989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_1783989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1783989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1783989 prefixEnd_1783989 := by exact prefixLift 1783989
  have htrace : WordTrace (prefixWord ++ tailWord_1783989) baseStart_1783989 baseEnd_1783989 := by
    simpa [prefixWord, tailWord_1783989, baseEnd_1783989] using wordTrace_append hprefix tailTrace_1783989
  have hstable : (prefixWord ++ tailWord_1783989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783989).length < 2 ^ (prefixWord ++ tailWord_1783989).sum := by decide
  have hdescent : baseEnd_1783989 < baseStart_1783989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784000 : List Nat := [2, 1, 1, 2, 5, 3, 1, 6]
def baseStart_1784000 : Nat := 118140960795 + 1784000 * 2 ^ 59
def prefixEnd_1784000 : Nat := 4983230072969 + 3 ^ 40 * 1784000 * 2
def baseEnd_1784000 : Nat := 135711035203129677851191

theorem tailTrace_1784000 : CollatzResearch.WordTrace tailWord_1784000 prefixEnd_1784000 135711035203129677851191 := by
  unfold tailWord_1784000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32533912768440078894030727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43378550357920105192040969 32533912768440078894030727)
  ·
    refine ⟨48800869152660118341046091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32533912768440078894030727 48800869152660118341046091)
    ·
      refine ⟨73201303728990177511569137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48800869152660118341046091 73201303728990177511569137)
      ·
        refine ⟨54900977796742633133676853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73201303728990177511569137 54900977796742633133676853)
        ·
          refine ⟨5146966668444621856282205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54900977796742633133676853 5146966668444621856282205)
          ·
            refine ⟨1930112500666733196105827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5146966668444621856282205 1930112500666733196105827)
            ·
              refine ⟨2895168751000099794158741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930112500666733196105827 2895168751000099794158741)
              ·
                refine ⟨135711035203129677851191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2895168751000099794158741 135711035203129677851191)
                ·
                  rfl

theorem cell21_1784000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_1784000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784000 prefixEnd_1784000 := by exact prefixLift 1784000
  have htrace : WordTrace (prefixWord ++ tailWord_1784000) baseStart_1784000 baseEnd_1784000 := by
    simpa [prefixWord, tailWord_1784000, baseEnd_1784000] using wordTrace_append hprefix tailTrace_1784000
  have hstable : (prefixWord ++ tailWord_1784000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784000).length < 2 ^ (prefixWord ++ tailWord_1784000).sum := by decide
  have hdescent : baseEnd_1784000 < baseStart_1784000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784014 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1784014 : Nat := 118140960795 + 1784014 * 2 ^ 59
def prefixEnd_1784014 : Nat := 4983230072969 + 3 ^ 40 * 1784014 * 2
def baseEnd_1784014 : Nat := 407136300600128120320211

theorem tailTrace_1784014 : CollatzResearch.WordTrace tailWord_1784014 prefixEnd_1784014 407136300600128120320211 := by
  unfold tailWord_1784014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133542019853679772383887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43378890772552958786047397 8133542019853679772383887)
  ·
    refine ⟨12200313029780519658575831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133542019853679772383887 12200313029780519658575831)
    ·
      refine ⟨18300469544670779487863747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200313029780519658575831 18300469544670779487863747)
      ·
        refine ⟨27450704317006169231795621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18300469544670779487863747 27450704317006169231795621)
        ·
          refine ⟨5147007059438656730961679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27450704317006169231795621 5147007059438656730961679)
          ·
            refine ⟨7720510589157985096442519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147007059438656730961679 7720510589157985096442519)
            ·
              refine ⟨11580765883736977644663779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720510589157985096442519 11580765883736977644663779)
              ·
                refine ⟨17371148825605466466995669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580765883736977644663779 17371148825605466466995669)
                ·
                  refine ⟨407136300600128120320211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17371148825605466466995669 407136300600128120320211)
                  ·
                    rfl

theorem cell21_1784014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1784014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784014 prefixEnd_1784014 := by exact prefixLift 1784014
  have htrace : WordTrace (prefixWord ++ tailWord_1784014) baseStart_1784014 baseEnd_1784014 := by
    simpa [prefixWord, tailWord_1784014, baseEnd_1784014] using wordTrace_append hprefix tailTrace_1784014
  have hstable : (prefixWord ++ tailWord_1784014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784014).length < 2 ^ (prefixWord ++ tailWord_1784014).sum := by decide
  have hdescent : baseEnd_1784014 < baseStart_1784014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784034 : List Nat := [3, 3, 4, 1, 1, 1, 8]
def baseStart_1784034 : Nat := 118140960795 + 1784034 * 2 ^ 59
def prefixEnd_1784034 : Nat := 4983230072969 + 3 ^ 40 * 1784034 * 2
def baseEnd_1784034 : Nat := 45237873874734725554093

theorem tailTrace_1784034 : CollatzResearch.WordTrace tailWord_1784034 prefixEnd_1784034 45237873874734725554093 := by
  unfold tailWord_1784034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267266404689245398699789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43379377079171321063199437 16267266404689245398699789)
  ·
    refine ⟨6100224901758467024512421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16267266404689245398699789 6100224901758467024512421)
    ·
      refine ⟨1143792169079712567096079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6100224901758467024512421 1143792169079712567096079)
      ·
        refine ⟨1715688253619568850644119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143792169079712567096079 1715688253619568850644119)
        ·
          refine ⟨2573532380429353275966179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715688253619568850644119 2573532380429353275966179)
          ·
            refine ⟨3860298570644029913949269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573532380429353275966179 3860298570644029913949269)
            ·
              refine ⟨45237873874734725554093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3860298570644029913949269 45237873874734725554093)
              ·
                rfl

theorem cell21_1784034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 8].length) (baseStart_1784034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784034 prefixEnd_1784034 := by exact prefixLift 1784034
  have htrace : WordTrace (prefixWord ++ tailWord_1784034) baseStart_1784034 baseEnd_1784034 := by
    simpa [prefixWord, tailWord_1784034, baseEnd_1784034] using wordTrace_append hprefix tailTrace_1784034
  have hstable : (prefixWord ++ tailWord_1784034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784034).length < 2 ^ (prefixWord ++ tailWord_1784034).sum := by decide
  have hdescent : baseEnd_1784034 < baseStart_1784034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784093 : List Nat := [1, 4, 2, 3, 3, 1, 7]
def baseStart_1784093 : Nat := 118140960795 + 1784093 * 2 ^ 59
def prefixEnd_1784093 : Nat := 4983230072969 + 3 ^ 40 * 1784093 * 2
def baseEnd_1784093 : Nat := 45239369941826837611487

theorem tailTrace_1784093 : CollatzResearch.WordTrace tailWord_1784093 prefixEnd_1784093 45239369941826837611487 := by
  unfold tailWord_1784093
  simp only [CollatzResearch.WordTrace]
  refine ⟨65071217525543234671196933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43380811683695489780797955 65071217525543234671196933)
  ·
    refine ⟨12200853286039356500849425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65071217525543234671196933 12200853286039356500849425)
    ·
      refine ⟨9150639964529517375637069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200853286039356500849425 9150639964529517375637069)
      ·
        refine ⟨3431489986698569015863901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9150639964529517375637069 3431489986698569015863901)
        ·
          refine ⟨1286808745011963380948963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3431489986698569015863901 1286808745011963380948963)
          ·
            refine ⟨1930213117517945071423445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286808745011963380948963 1930213117517945071423445)
            ·
              refine ⟨45239369941826837611487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1930213117517945071423445 45239369941826837611487)
              ·
                rfl

theorem cell21_1784093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 7].length) (baseStart_1784093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784093 prefixEnd_1784093 := by exact prefixLift 1784093
  have htrace : WordTrace (prefixWord ++ tailWord_1784093) baseStart_1784093 baseEnd_1784093 := by
    simpa [prefixWord, tailWord_1784093, baseEnd_1784093] using wordTrace_append hprefix tailTrace_1784093
  have hstable : (prefixWord ++ tailWord_1784093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784093).length < 2 ^ (prefixWord ++ tailWord_1784093).sum := by decide
  have hdescent : baseEnd_1784093 < baseStart_1784093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784245 : List Nat := [1, 3, 3, 2, 3, 2, 2, 5]
def baseStart_1784245 : Nat := 118140960795 + 1784245 * 2 ^ 59
def prefixEnd_1784245 : Nat := 4983230072969 + 3 ^ 40 * 1784245 * 2
def baseEnd_1784245 : Nat := 135729672649107683989913

theorem tailTrace_1784245 : CollatzResearch.WordTrace tailWord_1784245 prefixEnd_1784245 135729672649107683989913 := by
  unfold tailWord_1784245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65076761420992564630730189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43384507613995043087153459 65076761420992564630730189)
  ·
    refine ⟨24403785532872211736523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65076761420992564630730189 24403785532872211736523821)
    ·
      refine ⟨9151419574827079401196433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24403785532872211736523821 9151419574827079401196433)
      ·
        refine ⟨6863564681120309550897325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151419574827079401196433 6863564681120309550897325)
        ·
          refine ⟨2573836755420116081586497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6863564681120309550897325 2573836755420116081586497)
          ·
            refine ⟨1930377566565087061189873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573836755420116081586497 1930377566565087061189873)
            ·
              refine ⟨1447783174923815295892405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930377566565087061189873 1447783174923815295892405)
              ·
                refine ⟨135729672649107683989913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447783174923815295892405 135729672649107683989913)
                ·
                  rfl

theorem cell21_1784245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].length) (baseStart_1784245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784245 prefixEnd_1784245 := by exact prefixLift 1784245
  have htrace : WordTrace (prefixWord ++ tailWord_1784245) baseStart_1784245 baseEnd_1784245 := by
    simpa [prefixWord, tailWord_1784245, baseEnd_1784245] using wordTrace_append hprefix tailTrace_1784245
  have hstable : (prefixWord ++ tailWord_1784245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784245).length < 2 ^ (prefixWord ++ tailWord_1784245).sum := by decide
  have hdescent : baseEnd_1784245 < baseStart_1784245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784287 : List Nat := [1, 1, 2, 3, 3, 3, 2, 6]
def baseStart_1784287 : Nat := 118140960795 + 1784287 * 2 ^ 59
def prefixEnd_1784287 : Nat := 4983230072969 + 3 ^ 40 * 1784287 * 2
def baseEnd_1784287 : Nat := 135732867639846770756551

theorem tailTrace_1784287 : CollatzResearch.WordTrace tailWord_1784287 prefixEnd_1784287 135732867639846770756551 := by
  unfold tailWord_1784287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65078293286840405803759115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43385528857893603869172743 65078293286840405803759115)
  ·
    refine ⟨97617439930260608705638673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65078293286840405803759115 97617439930260608705638673)
    ·
      refine ⟨73213079947695456529229005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97617439930260608705638673 73213079947695456529229005)
      ·
        refine ⟨27454904980385796198460877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73213079947695456529229005 27454904980385796198460877)
        ·
          refine ⟨10295589367644673574422829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27454904980385796198460877 10295589367644673574422829)
          ·
            refine ⟨3860846012866752590408561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10295589367644673574422829 3860846012866752590408561)
            ·
              refine ⟨2895634509650064442806421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860846012866752590408561 2895634509650064442806421)
              ·
                refine ⟨135732867639846770756551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2895634509650064442806421 135732867639846770756551)
                ·
                  rfl

theorem cell21_1784287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_1784287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784287 prefixEnd_1784287 := by exact prefixLift 1784287
  have htrace : WordTrace (prefixWord ++ tailWord_1784287) baseStart_1784287 baseEnd_1784287 := by
    simpa [prefixWord, tailWord_1784287, baseEnd_1784287] using wordTrace_append hprefix tailTrace_1784287
  have hstable : (prefixWord ++ tailWord_1784287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784287).length < 2 ^ (prefixWord ++ tailWord_1784287).sum := by decide
  have hdescent : baseEnd_1784287 < baseStart_1784287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784349 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1784349 : Nat := 118140960795 + 1784349 * 2 ^ 59
def prefixEnd_1784349 : Nat := 4983230072969 + 3 ^ 40 * 1784349 * 2
def baseEnd_1784349 : Nat := 407212752164241982236193

theorem tailTrace_1784349 : CollatzResearch.WordTrace tailWord_1784349 prefixEnd_1784349 407212752164241982236193 := by
  unfold tailWord_1784349
  simp only [CollatzResearch.WordTrace]
  refine ⟨65080554612615790392516101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43387036408410526928344067 65080554612615790392516101)
  ·
    refine ⟨12202603989865460698596769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65080554612615790392516101 12202603989865460698596769)
    ·
      refine ⟨9151952992399095523947577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12202603989865460698596769 9151952992399095523947577)
      ·
        refine ⟨6863964744299321642960683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151952992399095523947577 6863964744299321642960683)
        ·
          refine ⟨10295947116448982464441025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863964744299321642960683 10295947116448982464441025)
          ·
            refine ⟨7721960337336736848330769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10295947116448982464441025 7721960337336736848330769)
            ·
              refine ⟨5791470253002552636248077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7721960337336736848330769 5791470253002552636248077)
              ·
                refine ⟨2171801344875957238593029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5791470253002552636248077 2171801344875957238593029)
                ·
                  refine ⟨407212752164241982236193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171801344875957238593029 407212752164241982236193)
                  ·
                    rfl

theorem cell21_1784349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1784349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784349 prefixEnd_1784349 := by exact prefixLift 1784349
  have htrace : WordTrace (prefixWord ++ tailWord_1784349) baseStart_1784349 baseEnd_1784349 := by
    simpa [prefixWord, tailWord_1784349, baseEnd_1784349] using wordTrace_append hprefix tailTrace_1784349
  have hstable : (prefixWord ++ tailWord_1784349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784349).length < 2 ^ (prefixWord ++ tailWord_1784349).sum := by decide
  have hdescent : baseEnd_1784349 < baseStart_1784349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784377 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_1784377 : Nat := 118140960795 + 1784377 * 2 ^ 59
def prefixEnd_1784377 : Nat := 4983230072969 + 3 ^ 40 * 1784377 * 2
def baseEnd_1784377 : Nat := 407219142145720155769469

theorem tailTrace_1784377 : CollatzResearch.WordTrace tailWord_1784377 prefixEnd_1784377 407219142145720155769469 := by
  unfold tailWord_1784377
  simp only [CollatzResearch.WordTrace]
  refine ⟨65081575856514351174535385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43387717237676234116356923 65081575856514351174535385)
  ·
    refine ⟨48811181892385763380901539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65081575856514351174535385 48811181892385763380901539)
    ·
      refine ⟨73216772838578645071352309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48811181892385763380901539 73216772838578645071352309)
      ·
        refine ⟨6864072453616747975439279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73216772838578645071352309 6864072453616747975439279)
        ·
          refine ⟨10296108680425121963158919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864072453616747975439279 10296108680425121963158919)
          ·
            refine ⟨15444163020637682944738379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296108680425121963158919 15444163020637682944738379)
            ·
              refine ⟨23166244530956524417107569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444163020637682944738379 23166244530956524417107569)
              ·
                refine ⟨17374683398217393312830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23166244530956524417107569 17374683398217393312830677)
                ·
                  refine ⟨407219142145720155769469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17374683398217393312830677 407219142145720155769469)
                  ·
                    rfl

theorem cell21_1784377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_1784377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784377 prefixEnd_1784377 := by exact prefixLift 1784377
  have htrace : WordTrace (prefixWord ++ tailWord_1784377) baseStart_1784377 baseEnd_1784377 := by
    simpa [prefixWord, tailWord_1784377, baseEnd_1784377] using wordTrace_append hprefix tailTrace_1784377
  have hstable : (prefixWord ++ tailWord_1784377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784377).length < 2 ^ (prefixWord ++ tailWord_1784377).sum := by decide
  have hdescent : baseEnd_1784377 < baseStart_1784377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784394 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1784394 : Nat := 118140960795 + 1784394 * 2 ^ 59
def prefixEnd_1784394 : Nat := 4983230072969 + 3 ^ 40 * 1784394 * 2
def baseEnd_1784394 : Nat := 407223021777331903986101

theorem tailTrace_1784394 : CollatzResearch.WordTrace tailWord_1784394 prefixEnd_1784394 407223021777331903986101 := by
  unfold tailWord_1784394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270548974363190769476059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43388130598301842051936157 16270548974363190769476059)
  ·
    refine ⟨24405823461544786154214089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16270548974363190769476059 24405823461544786154214089)
    ·
      refine ⟨18304367596158589615660567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24405823461544786154214089 18304367596158589615660567)
      ·
        refine ⟨27456551394237884423490851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18304367596158589615660567 27456551394237884423490851)
        ·
          refine ⟨41184827091356826635236277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27456551394237884423490851 41184827091356826635236277)
          ·
            refine ⟨3861077539814702497053401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41184827091356826635236277 3861077539814702497053401)
            ·
              refine ⟨2895808154861026872790051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861077539814702497053401 2895808154861026872790051)
              ·
                refine ⟨4343712232291540309185077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895808154861026872790051 4343712232291540309185077)
                ·
                  refine ⟨407223021777331903986101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343712232291540309185077 407223021777331903986101)
                  ·
                    rfl

theorem cell21_1784394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1784394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784394 prefixEnd_1784394 := by exact prefixLift 1784394
  have htrace : WordTrace (prefixWord ++ tailWord_1784394) baseStart_1784394 baseEnd_1784394 := by
    simpa [prefixWord, tailWord_1784394, baseEnd_1784394] using wordTrace_append hprefix tailTrace_1784394
  have hstable : (prefixWord ++ tailWord_1784394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784394).length < 2 ^ (prefixWord ++ tailWord_1784394).sum := by decide
  have hdescent : baseEnd_1784394 < baseStart_1784394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784408 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_1784408 : Nat := 118140960795 + 1784408 * 2 ^ 59
def prefixEnd_1784408 : Nat := 4983230072969 + 3 ^ 40 * 1784408 * 2
def baseEnd_1784408 : Nat := 407226216768070990752739

theorem tailTrace_1784408 : CollatzResearch.WordTrace tailWord_1784408 prefixEnd_1784408 407226216768070990752739 := by
  unfold tailWord_1784408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541353259701021734456939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43388471012934695645942585 32541353259701021734456939)
  ·
    refine ⟨48812029889551532601685409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32541353259701021734456939 48812029889551532601685409)
    ·
      refine ⟨36609022417163649451264057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48812029889551532601685409 36609022417163649451264057)
      ·
        refine ⟨27456766812872737088448043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36609022417163649451264057 27456766812872737088448043)
        ·
          refine ⟨41185150219309105632672065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27456766812872737088448043 41185150219309105632672065)
          ·
            refine ⟨30888862664481829224504049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41185150219309105632672065 30888862664481829224504049)
            ·
              refine ⟨23166646998361371918378037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30888862664481829224504049 23166646998361371918378037)
              ·
                refine ⟨2171873156096378617347941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23166646998361371918378037 2171873156096378617347941)
                ·
                  refine ⟨407226216768070990752739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171873156096378617347941 407226216768070990752739)
                  ·
                    rfl

theorem cell21_1784408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_1784408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784408 prefixEnd_1784408 := by exact prefixLift 1784408
  have htrace : WordTrace (prefixWord ++ tailWord_1784408) baseStart_1784408 baseEnd_1784408 := by
    simpa [prefixWord, tailWord_1784408, baseEnd_1784408] using wordTrace_append hprefix tailTrace_1784408
  have hstable : (prefixWord ++ tailWord_1784408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784408).length < 2 ^ (prefixWord ++ tailWord_1784408).sum := by decide
  have hdescent : baseEnd_1784408 < baseStart_1784408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784414 : List Nat := [4, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1784414 : Nat := 118140960795 + 1784414 * 2 ^ 59
def prefixEnd_1784414 : Nat := 4983230072969 + 3 ^ 40 * 1784414 * 2
def baseEnd_1784414 : Nat := 135742528683272104550909

theorem tailTrace_1784414 : CollatzResearch.WordTrace tailWord_1784414 prefixEnd_1784414 135742528683272104550909 := by
  unfold tailWord_1784414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135365669672538311704037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43388616904920204329088197 8135365669672538311704037)
  ·
    refine ⟨1525381063063600933444507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8135365669672538311704037 1525381063063600933444507)
    ·
      refine ⟨2288071594595401400166761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525381063063600933444507 2288071594595401400166761)
      ·
        refine ⟨1716053695946551050125071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288071594595401400166761 1716053695946551050125071)
        ·
          refine ⟨2574080543919826575187607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716053695946551050125071 2574080543919826575187607)
          ·
            refine ⟨3861120815879739862781411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574080543919826575187607 3861120815879739862781411)
            ·
              refine ⟨5791681223819609794172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861120815879739862781411 5791681223819609794172117)
              ·
                refine ⟨135742528683272104550909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5791681223819609794172117 135742528683272104550909)
                ·
                  rfl

theorem cell21_1784414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1784414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784414 prefixEnd_1784414 := by exact prefixLift 1784414
  have htrace : WordTrace (prefixWord ++ tailWord_1784414) baseStart_1784414 baseEnd_1784414 := by
    simpa [prefixWord, tailWord_1784414, baseEnd_1784414] using wordTrace_append hprefix tailTrace_1784414
  have hstable : (prefixWord ++ tailWord_1784414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784414).length < 2 ^ (prefixWord ++ tailWord_1784414).sum := by decide
  have hdescent : baseEnd_1784414 < baseStart_1784414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784501 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1784501 : Nat := 118140960795 + 1784501 * 2 ^ 59
def prefixEnd_1784501 : Nat := 4983230072969 + 3 ^ 40 * 1784501 * 2
def baseEnd_1784501 : Nat := 407247440635123495702549

theorem tailTrace_1784501 : CollatzResearch.WordTrace tailWord_1784501 prefixEnd_1784501 407247440635123495702549 := by
  unfold tailWord_1784501
  simp only [CollatzResearch.WordTrace]
  refine ⟨65086098508065120352049357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43390732338710080234699571 65086098508065120352049357)
  ·
    refine ⟨24407286940524420132018509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65086098508065120352049357 24407286940524420132018509)
    ·
      refine ⟨9152732602696657549506941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24407286940524420132018509 9152732602696657549506941)
      ·
        refine ⟨3432274726011246581065103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9152732602696657549506941 3432274726011246581065103)
        ·
          refine ⟨5148412089016869871597655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432274726011246581065103 5148412089016869871597655)
          ·
            refine ⟨7722618133525304807396483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148412089016869871597655 7722618133525304807396483)
            ·
              refine ⟨11583927200287957211094725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722618133525304807396483 11583927200287957211094725)
              ·
                refine ⟨2171986350053991977080261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11583927200287957211094725 2171986350053991977080261)
                ·
                  refine ⟨407247440635123495702549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171986350053991977080261 407247440635123495702549)
                  ·
                    rfl

theorem cell21_1784501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1784501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784501 prefixEnd_1784501 := by exact prefixLift 1784501
  have htrace : WordTrace (prefixWord ++ tailWord_1784501) baseStart_1784501 baseEnd_1784501 := by
    simpa [prefixWord, tailWord_1784501, baseEnd_1784501] using wordTrace_append hprefix tailTrace_1784501
  have hstable : (prefixWord ++ tailWord_1784501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784501).length < 2 ^ (prefixWord ++ tailWord_1784501).sum := by decide
  have hdescent : baseEnd_1784501 < baseStart_1784501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784529 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1784529 : Nat := 118140960795 + 1784529 * 2 ^ 59
def prefixEnd_1784529 : Nat := 4983230072969 + 3 ^ 40 * 1784529 * 2
def baseEnd_1784529 : Nat := 407253830616601669235825

theorem tailTrace_1784529 : CollatzResearch.WordTrace tailWord_1784529 prefixEnd_1784529 407253830616601669235825 := by
  unfold tailWord_1784529
  simp only [CollatzResearch.WordTrace]
  refine ⟨65087119751963681134068641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43391413167975787422712427 65087119751963681134068641)
  ·
    refine ⟨48815339813972760850551481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65087119751963681134068641 48815339813972760850551481)
    ·
      refine ⟨36611504860479570637913611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48815339813972760850551481 36611504860479570637913611)
      ·
        refine ⟨54917257290719355956870417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36611504860479570637913611 54917257290719355956870417)
        ·
          refine ⟨41187942968039516967652813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54917257290719355956870417 41187942968039516967652813)
          ·
            refine ⟨15445478613014818862869805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41187942968039516967652813 15445478613014818862869805)
            ·
              refine ⟨5792054479880557073576177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15445478613014818862869805 5792054479880557073576177)
              ·
                refine ⟨4344040859910417805182133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792054479880557073576177 4344040859910417805182133)
                ·
                  refine ⟨407253830616601669235825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344040859910417805182133 407253830616601669235825)
                  ·
                    rfl

theorem cell21_1784529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1784529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784529 prefixEnd_1784529 := by exact prefixLift 1784529
  have htrace : WordTrace (prefixWord ++ tailWord_1784529) baseStart_1784529 baseEnd_1784529 := by
    simpa [prefixWord, tailWord_1784529, baseEnd_1784529] using wordTrace_append hprefix tailTrace_1784529
  have hstable : (prefixWord ++ tailWord_1784529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784529).length < 2 ^ (prefixWord ++ tailWord_1784529).sum := by decide
  have hdescent : baseEnd_1784529 < baseStart_1784529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784628 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1784628 : Nat := 118140960795 + 1784628 * 2 ^ 59
def prefixEnd_1784628 : Nat := 4983230072969 + 3 ^ 40 * 1784628 * 2
def baseEnd_1784628 : Nat := 407276423765399497085623

theorem tailTrace_1784628 : CollatzResearch.WordTrace tailWord_1784628 prefixEnd_1784628 407276423765399497085623 := by
  unfold tailWord_1784628
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545365289302510520961269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43393820385736680694615025 32545365289302510520961269)
  ·
    refine ⟨3051127995872110361340119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32545365289302510520961269 3051127995872110361340119)
    ·
      refine ⟨4576691993808165542010179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051127995872110361340119 4576691993808165542010179)
      ·
        refine ⟨6865037990712248313015269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576691993808165542010179 6865037990712248313015269)
        ·
          refine ⟨1287194623258546558690363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6865037990712248313015269 1287194623258546558690363)
          ·
            refine ⟨1930791934887819838035545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287194623258546558690363 1930791934887819838035545)
            ·
              refine ⟨1448093951165864878526659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930791934887819838035545 1448093951165864878526659)
              ·
                refine ⟨2172140926748797317789989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448093951165864878526659 2172140926748797317789989)
                ·
                  refine ⟨407276423765399497085623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172140926748797317789989 407276423765399497085623)
                  ·
                    rfl

theorem cell21_1784628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1784628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784628 prefixEnd_1784628 := by exact prefixLift 1784628
  have htrace : WordTrace (prefixWord ++ tailWord_1784628) baseStart_1784628 baseEnd_1784628 := by
    simpa [prefixWord, tailWord_1784628, baseEnd_1784628] using wordTrace_append hprefix tailTrace_1784628
  have hstable : (prefixWord ++ tailWord_1784628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784628).length < 2 ^ (prefixWord ++ tailWord_1784628).sum := by decide
  have hdescent : baseEnd_1784628 < baseStart_1784628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784757 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1784757 : Nat := 118140960795 + 1784757 * 2 ^ 59
def prefixEnd_1784757 : Nat := 4983230072969 + 3 ^ 40 * 1784757 * 2
def baseEnd_1784757 : Nat := 407305863322923939435359

theorem tailTrace_1784757 : CollatzResearch.WordTrace tailWord_1784757 prefixEnd_1784757 407305863322923939435359 := by
  unfold tailWord_1784757
  simp only [CollatzResearch.WordTrace]
  refine ⟨65095435595137676073368525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43396957063425117382245683 65095435595137676073368525)
  ·
    refine ⟨24410788348176628527513197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65095435595137676073368525 24410788348176628527513197)
    ·
      refine ⟨9154045630566235697817449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24410788348176628527513197 9154045630566235697817449)
      ·
        refine ⟨6865534222924676773363087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9154045630566235697817449 6865534222924676773363087)
        ·
          refine ⟨10298301334387015160044631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865534222924676773363087 10298301334387015160044631)
          ·
            refine ⟨15447452001580522740066947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298301334387015160044631 15447452001580522740066947)
            ·
              refine ⟨23171178002370784110100421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15447452001580522740066947 23171178002370784110100421)
              ·
                refine ⟨4344595875444522020643829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23171178002370784110100421 4344595875444522020643829)
                ·
                  refine ⟨407305863322923939435359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344595875444522020643829 407305863322923939435359)
                  ·
                    rfl

theorem cell21_1784757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1784757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784757 prefixEnd_1784757 := by exact prefixLift 1784757
  have htrace : WordTrace (prefixWord ++ tailWord_1784757) baseStart_1784757 baseEnd_1784757 := by
    simpa [prefixWord, tailWord_1784757, baseEnd_1784757] using wordTrace_append hprefix tailTrace_1784757
  have hstable : (prefixWord ++ tailWord_1784757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784757).length < 2 ^ (prefixWord ++ tailWord_1784757).sum := by decide
  have hdescent : baseEnd_1784757 < baseStart_1784757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784788 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1784788 : Nat := 118140960795 + 1784788 * 2 ^ 59
def prefixEnd_1784788 : Nat := 4983230072969 + 3 ^ 40 * 1784788 * 2
def baseEnd_1784788 : Nat := 407312937945274774418629

theorem tailTrace_1784788 : CollatzResearch.WordTrace tailWord_1784788 prefixEnd_1784788 407312937945274774418629 := by
  unfold tailWord_1784788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32548283129012684183873509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43397710838683578911831345 32548283129012684183873509)
  ·
    refine ⟨6102803086689878284476283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32548283129012684183873509 6102803086689878284476283)
    ·
      refine ⟨9154204630034817426714425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6102803086689878284476283 9154204630034817426714425)
      ·
        refine ⟨6865653472526113070035819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9154204630034817426714425 6865653472526113070035819)
        ·
          refine ⟨10298480208789169605053729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865653472526113070035819 10298480208789169605053729)
          ·
            refine ⟨7723860156591877203790297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298480208789169605053729 7723860156591877203790297)
            ·
              refine ⟨5792895117443907902842723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723860156591877203790297 5792895117443907902842723)
              ·
                refine ⟨8689342676165861854264085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792895117443907902842723 8689342676165861854264085)
                ·
                  refine ⟨407312937945274774418629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8689342676165861854264085 407312937945274774418629)
                  ·
                    rfl

theorem cell21_1784788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1784788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784788 prefixEnd_1784788 := by exact prefixLift 1784788
  have htrace : WordTrace (prefixWord ++ tailWord_1784788) baseStart_1784788 baseEnd_1784788 := by
    simpa [prefixWord, tailWord_1784788, baseEnd_1784788] using wordTrace_append hprefix tailTrace_1784788
  have hstable : (prefixWord ++ tailWord_1784788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784788).length < 2 ^ (prefixWord ++ tailWord_1784788).sum := by decide
  have hdescent : baseEnd_1784788 < baseStart_1784788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784816 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_1784816 : Nat := 118140960795 + 1784816 * 2 ^ 59
def prefixEnd_1784816 : Nat := 4983230072969 + 3 ^ 40 * 1784816 * 2
def baseEnd_1784816 : Nat := 407319327926752947951905

theorem tailTrace_1784816 : CollatzResearch.WordTrace tailWord_1784816 prefixEnd_1784816 407319327926752947951905 := by
  unfold tailWord_1784816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32548793750961964574883151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43398391667949286099844201 32548793750961964574883151)
  ·
    refine ⟨48823190626442946862324727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32548793750961964574883151 48823190626442946862324727)
    ·
      refine ⟨73234785939664420293487091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48823190626442946862324727 73234785939664420293487091)
      ·
        refine ⟨109852178909496630440230637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73234785939664420293487091 109852178909496630440230637)
        ·
          refine ⟨41194567091061236415086489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109852178909496630440230637 41194567091061236415086489)
          ·
            refine ⟨30895925318295927311314867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41194567091061236415086489 30895925318295927311314867)
            ·
              refine ⟨46343887977443890966972301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30895925318295927311314867 46343887977443890966972301)
              ·
                refine ⟨17378957991541459112614613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46343887977443890966972301 17378957991541459112614613)
                ·
                  refine ⟨407319327926752947951905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17378957991541459112614613 407319327926752947951905)
                  ·
                    rfl

theorem cell21_1784816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_1784816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784816 prefixEnd_1784816 := by exact prefixLift 1784816
  have htrace : WordTrace (prefixWord ++ tailWord_1784816) baseStart_1784816 baseEnd_1784816 := by
    simpa [prefixWord, tailWord_1784816, baseEnd_1784816] using wordTrace_append hprefix tailTrace_1784816
  have hstable : (prefixWord ++ tailWord_1784816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784816).length < 2 ^ (prefixWord ++ tailWord_1784816).sum := by decide
  have hdescent : baseEnd_1784816 < baseStart_1784816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784884 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1784884 : Nat := 118140960795 + 1784884 * 2 ^ 59
def prefixEnd_1784884 : Nat := 4983230072969 + 3 ^ 40 * 1784884 * 2
def baseEnd_1784884 : Nat := 407334846453199940818433

theorem tailTrace_1784884 : CollatzResearch.WordTrace tailWord_1784884 prefixEnd_1784884 407334846453199940818433 := by
  unfold tailWord_1784884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32550033832838788381620853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43400045110451717842161137 32550033832838788381620853)
  ·
    refine ⟨3051565671828636410776955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32550033832838788381620853 3051565671828636410776955)
    ·
      refine ⟨4577348507742954616165433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051565671828636410776955 4577348507742954616165433)
      ·
        refine ⟨3433011380807215962124075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577348507742954616165433 3433011380807215962124075)
        ·
          refine ⟨5149517071210823943186113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433011380807215962124075 5149517071210823943186113)
          ·
            refine ⟨3862137803408117957389585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149517071210823943186113 3862137803408117957389585)
            ·
              refine ⟨2896603352556088468042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862137803408117957389585 2896603352556088468042189)
              ·
                refine ⟨1086226257208533175515821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2896603352556088468042189 1086226257208533175515821)
                ·
                  refine ⟨407334846453199940818433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086226257208533175515821 407334846453199940818433)
                  ·
                    rfl

theorem cell21_1784884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1784884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784884 prefixEnd_1784884 := by exact prefixLift 1784884
  have htrace : WordTrace (prefixWord ++ tailWord_1784884) baseStart_1784884 baseEnd_1784884 := by
    simpa [prefixWord, tailWord_1784884, baseEnd_1784884] using wordTrace_append hprefix tailTrace_1784884
  have hstable : (prefixWord ++ tailWord_1784884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784884).length < 2 ^ (prefixWord ++ tailWord_1784884).sum := by decide
  have hdescent : baseEnd_1784884 < baseStart_1784884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784974 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1784974 : Nat := 118140960795 + 1784974 * 2 ^ 59
def prefixEnd_1784974 : Nat := 4983230072969 + 3 ^ 40 * 1784974 * 2
def baseEnd_1784974 : Nat := 407355385679379784318249

theorem tailTrace_1784974 : CollatzResearch.WordTrace tailWord_1784974 prefixEnd_1784974 407355385679379784318249 := by
  unfold tailWord_1784974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137918779418940266752247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43402233490234348089345317 8137918779418940266752247)
  ·
    refine ⟨12206878169128410400128371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8137918779418940266752247 12206878169128410400128371)
    ·
      refine ⟨18310317253692615600192557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206878169128410400128371 18310317253692615600192557)
      ·
        refine ⟨6866368970134730850072209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18310317253692615600192557 6866368970134730850072209)
        ·
          refine ⟨5149776727601048137554157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866368970134730850072209 5149776727601048137554157)
          ·
            refine ⟨1931166272850393051582809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5149776727601048137554157 1931166272850393051582809)
            ·
              refine ⟨1448374704637794788687107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931166272850393051582809 1448374704637794788687107)
              ·
                refine ⟨2172562056956692183030661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448374704637794788687107 2172562056956692183030661)
                ·
                  refine ⟨407355385679379784318249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172562056956692183030661 407355385679379784318249)
                  ·
                    rfl

theorem cell21_1784974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1784974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1784974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1784974 prefixEnd_1784974 := by exact prefixLift 1784974
  have htrace : WordTrace (prefixWord ++ tailWord_1784974) baseStart_1784974 baseEnd_1784974 := by
    simpa [prefixWord, tailWord_1784974, baseEnd_1784974] using wordTrace_append hprefix tailTrace_1784974
  have hstable : (prefixWord ++ tailWord_1784974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784974).length < 2 ^ (prefixWord ++ tailWord_1784974).sum := by decide
  have hdescent : baseEnd_1784974 < baseStart_1784974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785013 : List Nat := [1, 3, 3, 14]
def baseStart_1785013 : Nat := 118140960795 + 1785013 * 2 ^ 59
def prefixEnd_1785013 : Nat := 4983230072969 + 3 ^ 40 * 1785013 * 2
def baseEnd_1785013 : Nat := 1676396238727260836083

theorem tailTrace_1785013 : CollatzResearch.WordTrace tailWord_1785013 prefixEnd_1785013 1676396238727260836083 := by
  unfold tailWord_1785013
  simp only [CollatzResearch.WordTrace]
  refine ⟨65104772682210231794687693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43403181788140154529791795 65104772682210231794687693)
  ·
    refine ⟨24414289755828836923007885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65104772682210231794687693 24414289755828836923007885)
    ·
      refine ⟨9155358658435813846127957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24414289755828836923007885 9155358658435813846127957)
      ·
        refine ⟨1676396238727260836083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9155358658435813846127957 1676396238727260836083)
        ·
          rfl

theorem cell21_1785013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 14].length) (baseStart_1785013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785013 prefixEnd_1785013 := by exact prefixLift 1785013
  have htrace : WordTrace (prefixWord ++ tailWord_1785013) baseStart_1785013 baseEnd_1785013 := by
    simpa [prefixWord, tailWord_1785013, baseEnd_1785013] using wordTrace_append hprefix tailTrace_1785013
  have hstable : (prefixWord ++ tailWord_1785013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785013).length < 2 ^ (prefixWord ++ tailWord_1785013).sum := by decide
  have hdescent : baseEnd_1785013 < baseStart_1785013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785075 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_1785075 : Nat := 118140960795 + 1785075 * 2 ^ 59
def prefixEnd_1785075 : Nat := 4983230072969 + 3 ^ 40 * 1785075 * 2
def baseEnd_1785075 : Nat := 407378435255426053134709

theorem tailTrace_1785075 : CollatzResearch.WordTrace tailWord_1785075 prefixEnd_1785075 407378435255426053134709 := by
  unfold tailWord_1785075
  simp only [CollatzResearch.WordTrace]
  refine ⟨65107034007985616383444679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43404689338657077588963119 65107034007985616383444679)
  ·
    refine ⟨97660551011978424575167019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65107034007985616383444679 97660551011978424575167019)
    ·
      refine ⟨146490826517967636862750529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97660551011978424575167019 146490826517967636862750529)
      ·
        refine ⟨109868119888475727647062897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146490826517967636862750529 109868119888475727647062897)
        ·
          refine ⟨82401089916356795735297173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109868119888475727647062897 82401089916356795735297173)
          ·
            refine ⟨3862551089829224800092055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82401089916356795735297173 3862551089829224800092055)
            ·
              refine ⟨5793826634743837200138083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862551089829224800092055 5793826634743837200138083)
              ·
                refine ⟨8690739952115755800207125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793826634743837200138083 8690739952115755800207125)
                ·
                  refine ⟨407378435255426053134709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8690739952115755800207125 407378435255426053134709)
                  ·
                    rfl

theorem cell21_1785075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_1785075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785075 prefixEnd_1785075 := by exact prefixLift 1785075
  have htrace : WordTrace (prefixWord ++ tailWord_1785075) baseStart_1785075 baseEnd_1785075 := by
    simpa [prefixWord, tailWord_1785075, baseEnd_1785075] using wordTrace_append hprefix tailTrace_1785075
  have hstable : (prefixWord ++ tailWord_1785075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785075).length < 2 ^ (prefixWord ++ tailWord_1785075).sum := by decide
  have hdescent : baseEnd_1785075 < baseStart_1785075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785137 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_1785137 : Nat := 118140960795 + 1785137 * 2 ^ 59
def prefixEnd_1785137 : Nat := 4983230072969 + 3 ^ 40 * 1785137 * 2
def baseEnd_1785137 : Nat := 407392584500127723101249

theorem tailTrace_1785137 : CollatzResearch.WordTrace tailWord_1785137 prefixEnd_1785137 407392584500127723101249 := by
  unfold tailWord_1785137
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109295333761000972201665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43406196889174000648134443 65109295333761000972201665)
  ·
    refine ⟨48831971500320750729151249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65109295333761000972201665 48831971500320750729151249)
    ·
      refine ⟨36623978625240563046863437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48831971500320750729151249 36623978625240563046863437)
      ·
        refine ⟨13733991984465211142573789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36623978625240563046863437 13733991984465211142573789)
        ·
          refine ⟨5150246994174454178465171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13733991984465211142573789 5150246994174454178465171)
          ·
            refine ⟨7725370491261681267697757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150246994174454178465171 7725370491261681267697757)
            ·
              refine ⟨2897013934223130475386659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7725370491261681267697757 2897013934223130475386659)
              ·
                refine ⟨4345520901334695713079989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897013934223130475386659 4345520901334695713079989)
                ·
                  refine ⟨407392584500127723101249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4345520901334695713079989 407392584500127723101249)
                  ·
                    rfl

theorem cell21_1785137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_1785137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785137 prefixEnd_1785137 := by exact prefixLift 1785137
  have htrace : WordTrace (prefixWord ++ tailWord_1785137) baseStart_1785137 baseEnd_1785137 := by
    simpa [prefixWord, tailWord_1785137, baseEnd_1785137] using wordTrace_append hprefix tailTrace_1785137
  have hstable : (prefixWord ++ tailWord_1785137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785137).length < 2 ^ (prefixWord ++ tailWord_1785137).sum := by decide
  have hdescent : baseEnd_1785137 < baseStart_1785137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785241 : List Nat := [1, 2, 1, 2, 1, 6, 8]
def baseStart_1785241 : Nat := 118140960795 + 1785241 * 2 ^ 59
def prefixEnd_1785241 : Nat := 4983230072969 + 3 ^ 40 * 1785241 * 2
def baseEnd_1785241 : Nat := 45268479857449628151967

theorem tailTrace_1785241 : CollatzResearch.WordTrace tailWord_1785241 prefixEnd_1785241 45268479857449628151967 := by
  unfold tailWord_1785241
  simp only [CollatzResearch.WordTrace]
  refine ⟨65113088525384226733987577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43408725683589484489325051 65113088525384226733987577)
  ·
    refine ⟨48834816394038170050490683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65113088525384226733987577 48834816394038170050490683)
    ·
      refine ⟨73252224591057255075736025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48834816394038170050490683 73252224591057255075736025)
      ·
        refine ⟨54939168443292941306802019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73252224591057255075736025 54939168443292941306802019)
        ·
          refine ⟨82408752664939411960203029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54939168443292941306802019 82408752664939411960203029)
          ·
            refine ⟨3862910281169034935634517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82408752664939411960203029 3862910281169034935634517)
            ·
              refine ⟨45268479857449628151967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3862910281169034935634517 45268479857449628151967)
              ·
                rfl

theorem cell21_1785241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 8].length) (baseStart_1785241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785241 prefixEnd_1785241 := by exact prefixLift 1785241
  have htrace : WordTrace (prefixWord ++ tailWord_1785241) baseStart_1785241 baseEnd_1785241 := by
    simpa [prefixWord, tailWord_1785241, baseEnd_1785241] using wordTrace_append hprefix tailTrace_1785241
  have hstable : (prefixWord ++ tailWord_1785241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785241).length < 2 ^ (prefixWord ++ tailWord_1785241).sum := by decide
  have hdescent : baseEnd_1785241 < baseStart_1785241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785272 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_1785272 : Nat := 118140960795 + 1785272 * 2 ^ 59
def prefixEnd_1785272 : Nat := 4983230072969 + 3 ^ 40 * 1785272 * 2
def baseEnd_1785272 : Nat := 407423393339397488350973

theorem tailTrace_1785272 : CollatzResearch.WordTrace tailWord_1785272 prefixEnd_1785272 407423393339397488350973 := by
  unfold tailWord_1785272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557109594135959514183035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43409479458847946018910713 32557109594135959514183035)
  ·
    refine ⟨48835664391203939271274553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32557109594135959514183035 48835664391203939271274553)
    ·
      refine ⟨36626748293402954453455915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48835664391203939271274553 36626748293402954453455915)
      ·
        refine ⟨54940122440104431680183873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36626748293402954453455915 54940122440104431680183873)
        ·
          refine ⟨41205091830078323760137905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54940122440104431680183873 41205091830078323760137905)
          ·
            refine ⟨30903818872558742820103429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41205091830078323760137905 30903818872558742820103429)
            ·
              refine ⟨5794466038604764278769393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30903818872558742820103429 5794466038604764278769393)
              ·
                refine ⟨4345849528953573209077045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794466038604764278769393 4345849528953573209077045)
                ·
                  refine ⟨407423393339397488350973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4345849528953573209077045 407423393339397488350973)
                  ·
                    rfl

theorem cell21_1785272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_1785272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785272 prefixEnd_1785272 := by exact prefixLift 1785272
  have htrace : WordTrace (prefixWord ++ tailWord_1785272) baseStart_1785272 baseEnd_1785272 := by
    simpa [prefixWord, tailWord_1785272, baseEnd_1785272] using wordTrace_append hprefix tailTrace_1785272
  have hstable : (prefixWord ++ tailWord_1785272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785272).length < 2 ^ (prefixWord ++ tailWord_1785272).sum := by decide
  have hdescent : baseEnd_1785272 < baseStart_1785272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785334 : List Nat := [5, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1785334 : Nat := 118140960795 + 1785334 * 2 ^ 59
def prefixEnd_1785334 : Nat := 4983230072969 + 3 ^ 40 * 1785334 * 2
def baseEnd_1785334 : Nat := 135812514194699719439171

theorem tailTrace_1785334 : CollatzResearch.WordTrace tailWord_1785334 prefixEnd_1785334 135812514194699719439171 := by
  unfold tailWord_1785334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069780032127956476070191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43410987009364869078082037 4069780032127956476070191)
  ·
    refine ⟨6104670048191934714105287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069780032127956476070191 6104670048191934714105287)
    ·
      refine ⟨9157005072287902071157931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104670048191934714105287 9157005072287902071157931)
      ·
        refine ⟨13735507608431853106736897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157005072287902071157931 13735507608431853106736897)
        ·
          refine ⟨10301630706323889830052673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735507608431853106736897 10301630706323889830052673)
          ·
            refine ⟨7726223029742917372539505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10301630706323889830052673 7726223029742917372539505)
            ·
              refine ⟨5794667272307188029404629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7726223029742917372539505 5794667272307188029404629)
              ·
                refine ⟨135812514194699719439171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5794667272307188029404629 135812514194699719439171)
                ·
                  rfl

theorem cell21_1785334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1785334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785334 prefixEnd_1785334 := by exact prefixLift 1785334
  have htrace : WordTrace (prefixWord ++ tailWord_1785334) baseStart_1785334 baseEnd_1785334 := by
    simpa [prefixWord, tailWord_1785334, baseEnd_1785334] using wordTrace_append hprefix tailTrace_1785334
  have hstable : (prefixWord ++ tailWord_1785334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785334).length < 2 ^ (prefixWord ++ tailWord_1785334).sum := by decide
  have hdescent : baseEnd_1785334 < baseStart_1785334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785424 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_1785424 : Nat := 118140960795 + 1785424 * 2 ^ 59
def prefixEnd_1785424 : Nat := 4983230072969 + 3 ^ 40 * 1785424 * 2
def baseEnd_1785424 : Nat := 407458081810279001817329

theorem tailTrace_1785424 : CollatzResearch.WordTrace tailWord_1785424 prefixEnd_1785424 407458081810279001817329 := by
  unfold tailWord_1785424
  simp only [CollatzResearch.WordTrace]
  refine ⟨32559881541860624493949663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43413175389147499325266217 32559881541860624493949663)
  ·
    refine ⟨48839822312790936740924495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32559881541860624493949663 48839822312790936740924495)
    ·
      refine ⟨73259733469186405111386743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48839822312790936740924495 73259733469186405111386743)
      ·
        refine ⟨109889600203779607667080115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73259733469186405111386743 109889600203779607667080115)
        ·
          refine ⟨164834400305669411500620173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109889600203779607667080115 164834400305669411500620173)
          ·
            refine ⟨61812900114626029312732565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164834400305669411500620173 61812900114626029312732565)
            ·
              refine ⟨2897479692873095124034339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61812900114626029312732565 2897479692873095124034339)
              ·
                refine ⟨4346219539309642686051509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897479692873095124034339 4346219539309642686051509)
                ·
                  refine ⟨407458081810279001817329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4346219539309642686051509 407458081810279001817329)
                  ·
                    rfl

theorem cell21_1785424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_1785424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785424 prefixEnd_1785424 := by exact prefixLift 1785424
  have htrace : WordTrace (prefixWord ++ tailWord_1785424) baseStart_1785424 baseEnd_1785424 := by
    simpa [prefixWord, tailWord_1785424, baseEnd_1785424] using wordTrace_append hprefix tailTrace_1785424
  have hstable : (prefixWord ++ tailWord_1785424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785424).length < 2 ^ (prefixWord ++ tailWord_1785424).sum := by decide
  have hdescent : baseEnd_1785424 < baseStart_1785424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785458 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1785458 : Nat := 118140960795 + 1785458 * 2 ^ 59
def prefixEnd_1785458 : Nat := 4983230072969 + 3 ^ 40 * 1785458 * 2
def baseEnd_1785458 : Nat := 407465841073502498250593

theorem tailTrace_1785458 : CollatzResearch.WordTrace tailWord_1785458 prefixEnd_1785458 407465841073502498250593 := by
  unfold tailWord_1785458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280250791399518198659257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43414002110398715196424685 16280250791399518198659257)
  ·
    refine ⟨12210188093549638648994443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16280250791399518198659257 12210188093549638648994443)
    ·
      refine ⟨18315282140324457973491665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210188093549638648994443 18315282140324457973491665)
      ·
        refine ⟨13736461605243343480118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18315282140324457973491665 13736461605243343480118749)
        ·
          refine ⟨5151173101966253805044531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13736461605243343480118749 5151173101966253805044531)
          ·
            refine ⟨7726759652949380707566797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151173101966253805044531 7726759652949380707566797)
            ·
              refine ⟨2897534869856017765337549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7726759652949380707566797 2897534869856017765337549)
              ·
                refine ⟨1086575576196006662001581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897534869856017765337549 1086575576196006662001581)
                ·
                  refine ⟨407465841073502498250593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086575576196006662001581 407465841073502498250593)
                  ·
                    rfl

theorem cell21_1785458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1785458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785458 prefixEnd_1785458 := by exact prefixLift 1785458
  have htrace : WordTrace (prefixWord ++ tailWord_1785458) baseStart_1785458 baseEnd_1785458 := by
    simpa [prefixWord, tailWord_1785458, baseEnd_1785458] using wordTrace_append hprefix tailTrace_1785458
  have hstable : (prefixWord ++ tailWord_1785458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785458).length < 2 ^ (prefixWord ++ tailWord_1785458).sum := by decide
  have hdescent : baseEnd_1785458 < baseStart_1785458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785469 : List Nat := [1, 4, 1, 1, 4, 1, 9]
def baseStart_1785469 : Nat := 118140960795 + 1785469 * 2 ^ 59
def prefixEnd_1785469 : Nat := 4983230072969 + 3 ^ 40 * 1785469 * 2
def baseEnd_1785469 : Nat := 45274261269263213729693

theorem tailTrace_1785469 : CollatzResearch.WordTrace tailWord_1785469 prefixEnd_1785469 45274261269263213729693 := by
  unfold tailWord_1785469
  simp only [CollatzResearch.WordTrace]
  refine ⟨65121404368558221673287461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43414269579038814448858307 65121404368558221673287461)
  ·
    refine ⟨12210263319104666563741399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65121404368558221673287461 12210263319104666563741399)
    ·
      refine ⟨18315394978656999845612099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210263319104666563741399 18315394978656999845612099)
      ·
        refine ⟨27473092467985499768418149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18315394978656999845612099 27473092467985499768418149)
        ·
          refine ⟨5151204837747281206578403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27473092467985499768418149 5151204837747281206578403)
          ·
            refine ⟨7726807256620921809867605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151204837747281206578403 7726807256620921809867605)
            ·
              refine ⟨45274261269263213729693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7726807256620921809867605 45274261269263213729693)
              ·
                rfl

theorem cell21_1785469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 9].length) (baseStart_1785469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785469 prefixEnd_1785469 := by exact prefixLift 1785469
  have htrace : WordTrace (prefixWord ++ tailWord_1785469) baseStart_1785469 baseEnd_1785469 := by
    simpa [prefixWord, tailWord_1785469, baseEnd_1785469] using wordTrace_append hprefix tailTrace_1785469
  have hstable : (prefixWord ++ tailWord_1785469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785469).length < 2 ^ (prefixWord ++ tailWord_1785469).sum := by decide
  have hdescent : baseEnd_1785469 < baseStart_1785469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785486 : List Nat := [4, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1785486 : Nat := 118140960795 + 1785486 * 2 ^ 59
def prefixEnd_1785486 : Nat := 4983230072969 + 3 ^ 40 * 1785486 * 2
def baseEnd_1785486 : Nat := 135824077018326890594623

theorem tailTrace_1785486 : CollatzResearch.WordTrace tailWord_1785486 prefixEnd_1785486 135824077018326890594623 := by
  unfold tailWord_1785486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140253051187079197082039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43414682939664422384437541 8140253051187079197082039)
  ·
    refine ⟨12210379576780618795623059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140253051187079197082039 12210379576780618795623059)
    ·
      refine ⟨18315569365170928193434589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210379576780618795623059 18315569365170928193434589)
      ·
        refine ⟨6868338511939098072537971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18315569365170928193434589 6868338511939098072537971)
        ·
          refine ⟨10302507767908647108806957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868338511939098072537971 10302507767908647108806957)
          ·
            refine ⟨3863440412965742665802609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10302507767908647108806957 3863440412965742665802609)
            ·
              refine ⟨2897580309724306999351957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863440412965742665802609 2897580309724306999351957)
              ·
                refine ⟨135824077018326890594623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2897580309724306999351957 135824077018326890594623)
                ·
                  rfl

theorem cell21_1785486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1785486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785486 prefixEnd_1785486 := by exact prefixLift 1785486
  have htrace : WordTrace (prefixWord ++ tailWord_1785486) baseStart_1785486 baseEnd_1785486 := by
    simpa [prefixWord, tailWord_1785486, baseEnd_1785486] using wordTrace_append hprefix tailTrace_1785486
  have hstable : (prefixWord ++ tailWord_1785486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785486).length < 2 ^ (prefixWord ++ tailWord_1785486).sum := by decide
  have hdescent : baseEnd_1785486 < baseStart_1785486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785534 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1785534 : Nat := 118140960795 + 1785534 * 2 ^ 59
def prefixEnd_1785534 : Nat := 4983230072969 + 3 ^ 40 * 1785534 * 2
def baseEnd_1785534 : Nat := 407483185308943254983771

theorem tailTrace_1785534 : CollatzResearch.WordTrace tailWord_1785534 prefixEnd_1785534 407483185308943254983771 := by
  unfold tailWord_1785534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140471889165342221800457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43415850075548491849602437 8140471889165342221800457)
  ·
    refine ⟨6105353916874006666350343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140471889165342221800457 6105353916874006666350343)
    ·
      refine ⟨9158030875311009999525515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105353916874006666350343 9158030875311009999525515)
      ·
        refine ⟨13737046312966514999288273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158030875311009999525515 13737046312966514999288273)
        ·
          refine ⟨10302784734724886249466205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13737046312966514999288273 10302784734724886249466205)
          ·
            refine ⟨3863544275521832343549827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10302784734724886249466205 3863544275521832343549827)
            ·
              refine ⟨5795316413282748515324741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863544275521832343549827 5795316413282748515324741)
              ·
                refine ⟨1086621827490515346623389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5795316413282748515324741 1086621827490515346623389)
                ·
                  refine ⟨407483185308943254983771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086621827490515346623389 407483185308943254983771)
                  ·
                    rfl

theorem cell21_1785534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1785534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785534 prefixEnd_1785534 := by exact prefixLift 1785534
  have htrace : WordTrace (prefixWord ++ tailWord_1785534) baseStart_1785534 baseEnd_1785534 := by
    simpa [prefixWord, tailWord_1785534, baseEnd_1785534] using wordTrace_append hprefix tailTrace_1785534
  have hstable : (prefixWord ++ tailWord_1785534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785534).length < 2 ^ (prefixWord ++ tailWord_1785534).sum := by decide
  have hdescent : baseEnd_1785534 < baseStart_1785534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785562 : List Nat := [3, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1785562 : Nat := 118140960795 + 1785562 * 2 ^ 59
def prefixEnd_1785562 : Nat := 4983230072969 + 3 ^ 40 * 1785562 * 2
def baseEnd_1785562 : Nat := 135829858430140476172349

theorem tailTrace_1785562 : CollatzResearch.WordTrace tailWord_1785562 prefixEnd_1785562 135829858430140476172349 := by
  unfold tailWord_1785562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281199089305324639105735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43416530904814199037615293 16281199089305324639105735)
  ·
    refine ⟨24421798633957986958658603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281199089305324639105735 24421798633957986958658603)
    ·
      refine ⟨36632697950936980437987905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24421798633957986958658603 36632697950936980437987905)
      ·
        refine ⟨27474523463202735328490929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36632697950936980437987905 27474523463202735328490929)
        ·
          refine ⟨20605892597402051496368197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27474523463202735328490929 20605892597402051496368197)
          ·
            refine ⟨3863604862012884655569037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20605892597402051496368197 3863604862012884655569037)
            ·
              refine ⟨1448851823254831745838389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3863604862012884655569037 1448851823254831745838389)
              ·
                refine ⟨135829858430140476172349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1448851823254831745838389 135829858430140476172349)
                ·
                  rfl

theorem cell21_1785562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1785562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785562 prefixEnd_1785562 := by exact prefixLift 1785562
  have htrace : WordTrace (prefixWord ++ tailWord_1785562) baseStart_1785562 baseEnd_1785562 := by
    simpa [prefixWord, tailWord_1785562, baseEnd_1785562] using wordTrace_append hprefix tailTrace_1785562
  have hstable : (prefixWord ++ tailWord_1785562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785562).length < 2 ^ (prefixWord ++ tailWord_1785562).sum := by decide
  have hdescent : baseEnd_1785562 < baseStart_1785562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785613 : List Nat := [1, 7, 2, 1, 1, 1, 1, 7]
def baseStart_1785613 : Nat := 118140960795 + 1785613 * 2 ^ 59
def prefixEnd_1785613 : Nat := 4983230072969 + 3 ^ 40 * 1785613 * 2
def baseEnd_1785613 : Nat := 135833738061752224388981

theorem tailTrace_1785613 : CollatzResearch.WordTrace tailWord_1785613 prefixEnd_1785613 135833738061752224388981 := by
  unfold tailWord_1785613
  simp only [CollatzResearch.WordTrace]
  refine ⟨65126656480036534266529493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43417770986691022844352995 65126656480036534266529493)
  ·
    refine ⟨1526406011250856271871785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 65126656480036534266529493 1526406011250856271871785)
    ·
      refine ⟨1144804508438142203903839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526406011250856271871785 1144804508438142203903839)
      ·
        refine ⟨1717206762657213305855759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144804508438142203903839 1717206762657213305855759)
        ·
          refine ⟨2575810143985819958783639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717206762657213305855759 2575810143985819958783639)
          ·
            refine ⟨3863715215978729938175459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575810143985819958783639 3863715215978729938175459)
            ·
              refine ⟨5795572823968094907263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863715215978729938175459 5795572823968094907263189)
              ·
                refine ⟨135833738061752224388981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5795572823968094907263189 135833738061752224388981)
                ·
                  rfl

theorem cell21_1785613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].length) (baseStart_1785613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785613 prefixEnd_1785613 := by exact prefixLift 1785613
  have htrace : WordTrace (prefixWord ++ tailWord_1785613) baseStart_1785613 baseEnd_1785613 := by
    simpa [prefixWord, tailWord_1785613, baseEnd_1785613] using wordTrace_append hprefix tailTrace_1785613
  have hstable : (prefixWord ++ tailWord_1785613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785613).length < 2 ^ (prefixWord ++ tailWord_1785613).sum := by decide
  have hdescent : baseEnd_1785613 < baseStart_1785613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785621 : List Nat := [1, 3, 2, 1, 2, 4, 1, 7]
def baseStart_1785621 : Nat := 118140960795 + 1785621 * 2 ^ 59
def prefixEnd_1785621 : Nat := 4983230072969 + 3 ^ 40 * 1785621 * 2
def baseEnd_1785621 : Nat := 135834346631416812344531

theorem tailTrace_1785621 : CollatzResearch.WordTrace tailWord_1785621 prefixEnd_1785621 135834346631416812344531 := by
  unfold tailWord_1785621
  simp only [CollatzResearch.WordTrace]
  refine ⟨65126948264007551632820717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43417965509338367755213811 65126948264007551632820717)
  ·
    refine ⟨24422605599002831862307769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65126948264007551632820717 24422605599002831862307769)
    ·
      refine ⟨18316954199252123896730827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24422605599002831862307769 18316954199252123896730827)
      ·
        refine ⟨27475431298878185845096241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316954199252123896730827 27475431298878185845096241)
        ·
          refine ⟨20606573474158639383822181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27475431298878185845096241 20606573474158639383822181)
          ·
            refine ⟨3863732526404744884466659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20606573474158639383822181 3863732526404744884466659)
            ·
              refine ⟨5795598789607117326699989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863732526404744884466659 5795598789607117326699989)
              ·
                refine ⟨135834346631416812344531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5795598789607117326699989 135834346631416812344531)
                ·
                  rfl

theorem cell21_1785621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_1785621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785621 prefixEnd_1785621 := by exact prefixLift 1785621
  have htrace : WordTrace (prefixWord ++ tailWord_1785621) baseStart_1785621 baseEnd_1785621 := by
    simpa [prefixWord, tailWord_1785621, baseEnd_1785621] using wordTrace_append hprefix tailTrace_1785621
  have hstable : (prefixWord ++ tailWord_1785621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785621).length < 2 ^ (prefixWord ++ tailWord_1785621).sum := by decide
  have hdescent : baseEnd_1785621 < baseStart_1785621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785635 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_1785635 : Nat := 118140960795 + 1785635 * 2 ^ 59
def prefixEnd_1785635 : Nat := 4983230072969 + 3 ^ 40 * 1785635 * 2
def baseEnd_1785635 : Nat := 407506234884989523800231

theorem tailTrace_1785635 : CollatzResearch.WordTrace tailWord_1785635 prefixEnd_1785635 407506234884989523800231 := by
  unfold tailWord_1785635
  simp only [CollatzResearch.WordTrace]
  refine ⟨65127458885956832023830359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43418305923971221349220239 65127458885956832023830359)
  ·
    refine ⟨97691188328935248035745539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65127458885956832023830359 97691188328935248035745539)
    ·
      refine ⟨146536782493402872053618309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97691188328935248035745539 146536782493402872053618309)
      ·
        refine ⟨27475646717513038510053433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146536782493402872053618309 27475646717513038510053433)
        ·
          refine ⟨20606735038134778882540075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27475646717513038510053433 20606735038134778882540075)
          ·
            refine ⟨30910102557202168323810113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606735038134778882540075 30910102557202168323810113)
            ·
              refine ⟨23182576917901626242857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30910102557202168323810113 23182576917901626242857585)
              ·
                refine ⟨17386932688426219682143189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23182576917901626242857585 17386932688426219682143189)
                ·
                  refine ⟨407506234884989523800231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17386932688426219682143189 407506234884989523800231)
                  ·
                    rfl

theorem cell21_1785635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_1785635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785635 prefixEnd_1785635 := by exact prefixLift 1785635
  have htrace : WordTrace (prefixWord ++ tailWord_1785635) baseStart_1785635 baseEnd_1785635 := by
    simpa [prefixWord, tailWord_1785635, baseEnd_1785635] using wordTrace_append hprefix tailTrace_1785635
  have hstable : (prefixWord ++ tailWord_1785635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785635).length < 2 ^ (prefixWord ++ tailWord_1785635).sum := by decide
  have hdescent : baseEnd_1785635 < baseStart_1785635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785700 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_1785700 : Nat := 118140960795 + 1785700 * 2 ^ 59
def prefixEnd_1785700 : Nat := 4983230072969 + 3 ^ 40 * 1785700 * 2
def baseEnd_1785700 : Nat := 407521068770563855216765

theorem tailTrace_1785700 : CollatzResearch.WordTrace tailWord_1785700 prefixEnd_1785700 407521068770563855216765 := by
  unfold tailWord_1785700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32564914815360674062473277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43419886420480898749964369 32564914815360674062473277)
  ·
    refine ⟨12211843055760252773427479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32564914815360674062473277 12211843055760252773427479)
    ·
      refine ⟨18317764583640379160141219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211843055760252773427479 18317764583640379160141219)
      ·
        refine ⟨27476646875460568740211829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317764583640379160141219 27476646875460568740211829)
        ·
          refine ⟨2575935644574428319394859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27476646875460568740211829 2575935644574428319394859)
          ·
            refine ⟨3863903466861642479092289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575935644574428319394859 3863903466861642479092289)
            ·
              refine ⟨2897927600146231859319217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863903466861642479092289 2897927600146231859319217)
              ·
                refine ⟨2173445700109673894489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897927600146231859319217 2173445700109673894489413)
                ·
                  refine ⟨407521068770563855216765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173445700109673894489413 407521068770563855216765)
                  ·
                    rfl

theorem cell21_1785700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_1785700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785700 prefixEnd_1785700 := by exact prefixLift 1785700
  have htrace : WordTrace (prefixWord ++ tailWord_1785700) baseStart_1785700 baseEnd_1785700 := by
    simpa [prefixWord, tailWord_1785700, baseEnd_1785700] using wordTrace_append hprefix tailTrace_1785700
  have hstable : (prefixWord ++ tailWord_1785700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785700).length < 2 ^ (prefixWord ++ tailWord_1785700).sum := by decide
  have hdescent : baseEnd_1785700 < baseStart_1785700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785759 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_1785759 : Nat := 118140960795 + 1785759 * 2 ^ 59
def prefixEnd_1785759 : Nat := 4983230072969 + 3 ^ 40 * 1785759 * 2
def baseEnd_1785759 : Nat := 407534533374392863733311

theorem tailTrace_1785759 : CollatzResearch.WordTrace tailWord_1785759 prefixEnd_1785759 407534533374392863733311 := by
  unfold tailWord_1785759
  simp only [CollatzResearch.WordTrace]
  refine ⟨65131981537507601201344331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43421321025005067467562887 65131981537507601201344331)
  ·
    refine ⟨97697972306261401802016497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65131981537507601201344331 97697972306261401802016497)
    ·
      refine ⟨73273479229696051351512373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97697972306261401802016497 73273479229696051351512373)
      ·
        refine ⟨6869388677784004814204285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73273479229696051351512373 6869388677784004814204285)
        ·
          refine ⟨2576020754169001805326607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6869388677784004814204285 2576020754169001805326607)
          ·
            refine ⟨3864031131253502707989911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576020754169001805326607 3864031131253502707989911)
            ·
              refine ⟨5796046696880254061984867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864031131253502707989911 5796046696880254061984867)
              ·
                refine ⟨8694070045320381092977301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796046696880254061984867 8694070045320381092977301)
                ·
                  refine ⟨407534533374392863733311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8694070045320381092977301 407534533374392863733311)
                  ·
                    rfl

theorem cell21_1785759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_1785759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785759 prefixEnd_1785759 := by exact prefixLift 1785759
  have htrace : WordTrace (prefixWord ++ tailWord_1785759) baseStart_1785759 baseEnd_1785759 := by
    simpa [prefixWord, tailWord_1785759, baseEnd_1785759] using wordTrace_append hprefix tailTrace_1785759
  have hstable : (prefixWord ++ tailWord_1785759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785759).length < 2 ^ (prefixWord ++ tailWord_1785759).sum := by decide
  have hdescent : baseEnd_1785759 < baseStart_1785759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785790 : List Nat := [4, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1785790 : Nat := 118140960795 + 1785790 * 2 ^ 59
def prefixEnd_1785790 : Nat := 4983230072969 + 3 ^ 40 * 1785790 * 2
def baseEnd_1785790 : Nat := 135847202665581232905527

theorem tailTrace_1785790 : CollatzResearch.WordTrace tailWord_1785790 prefixEnd_1785790 135847202665581232905527 := by
  unfold tailWord_1785790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141639025049411686965353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43422074800263528997148549 8141639025049411686965353)
  ·
    refine ⟨6106229268787058765224015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8141639025049411686965353 6106229268787058765224015)
    ·
      refine ⟨9159343903180588147836023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106229268787058765224015 9159343903180588147836023)
      ·
        refine ⟨13739015854770882221754035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159343903180588147836023 13739015854770882221754035)
        ·
          refine ⟨20608523782156323332631053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739015854770882221754035 20608523782156323332631053)
          ·
            refine ⟨7728196418308621249736645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20608523782156323332631053 7728196418308621249736645)
            ·
              refine ⟨1449036828432866484325621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7728196418308621249736645 1449036828432866484325621)
              ·
                refine ⟨135847202665581232905527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1449036828432866484325621 135847202665581232905527)
                ·
                  rfl

theorem cell21_1785790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1785790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785790 prefixEnd_1785790 := by exact prefixLift 1785790
  have htrace : WordTrace (prefixWord ++ tailWord_1785790) baseStart_1785790 baseEnd_1785790 := by
    simpa [prefixWord, tailWord_1785790, baseEnd_1785790] using wordTrace_append hprefix tailTrace_1785790
  have hstable : (prefixWord ++ tailWord_1785790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785790).length < 2 ^ (prefixWord ++ tailWord_1785790).sum := by decide
  have hdescent : baseEnd_1785790 < baseStart_1785790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785970 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1785970 : Nat := 118140960795 + 1785970 * 2 ^ 59
def prefixEnd_1785970 : Nat := 4983230072969 + 3 ^ 40 * 1785970 * 2
def baseEnd_1785970 : Nat := 407582686449103385716213

theorem tailTrace_1785970 : CollatzResearch.WordTrace tailWord_1785970 prefixEnd_1785970 407582686449103385716213 := by
  unfold tailWord_1785970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284919334935796059318841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43426451559828789491516909 16284919334935796059318841)
  ·
    refine ⟨12213689501201847044489131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16284919334935796059318841 12213689501201847044489131)
    ·
      refine ⟨18320534251802770566733697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213689501201847044489131 18320534251802770566733697)
      ·
        refine ⟨13740400688852077925050273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18320534251802770566733697 13740400688852077925050273)
        ·
          refine ⟨10305300516639058443787705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13740400688852077925050273 10305300516639058443787705)
          ·
            refine ⟨7728975387479293832840779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305300516639058443787705 7728975387479293832840779)
            ·
              refine ⟨11593463081218940749261169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728975387479293832840779 11593463081218940749261169)
              ·
                refine ⟨8695097310914205561945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593463081218940749261169 8695097310914205561945877)
                ·
                  refine ⟨407582686449103385716213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8695097310914205561945877 407582686449103385716213)
                  ·
                    rfl

theorem cell21_1785970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1785970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1785970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1785970 prefixEnd_1785970 := by exact prefixLift 1785970
  have htrace : WordTrace (prefixWord ++ tailWord_1785970) baseStart_1785970 baseEnd_1785970 := by
    simpa [prefixWord, tailWord_1785970, baseEnd_1785970] using wordTrace_append hprefix tailTrace_1785970
  have hstable : (prefixWord ++ tailWord_1785970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785970).length < 2 ^ (prefixWord ++ tailWord_1785970).sum := by decide
  have hdescent : baseEnd_1785970 < baseStart_1785970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786108 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_1786108 : Nat := 118140960795 + 1786108 * 2 ^ 59
def prefixEnd_1786108 : Nat := 4983230072969 + 3 ^ 40 * 1786108 * 2
def baseEnd_1786108 : Nat := 407614179929245812415931

theorem tailTrace_1786108 : CollatzResearch.WordTrace tailWord_1786108 prefixEnd_1786108 407614179929245812415931 := by
  unfold tailWord_1786108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572355306621616902899489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43429807075495489203865985 32572355306621616902899489)
  ·
    refine ⟨24429266479966212677174617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32572355306621616902899489 24429266479966212677174617)
    ·
      refine ⟨18321949859974659507880963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24429266479966212677174617 18321949859974659507880963)
      ·
        refine ⟨27482924789961989261821445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321949859974659507880963 27482924789961989261821445)
        ·
          refine ⟨5153048398117872986591521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27482924789961989261821445 5153048398117872986591521)
          ·
            refine ⟨3864786298588404739943641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5153048398117872986591521 3864786298588404739943641)
            ·
              refine ⟨2898589723941303554957731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864786298588404739943641 2898589723941303554957731)
              ·
                refine ⟨4347884585911955332436597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898589723941303554957731 4347884585911955332436597)
                ·
                  refine ⟨407614179929245812415931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4347884585911955332436597 407614179929245812415931)
                  ·
                    rfl

theorem cell21_1786108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_1786108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786108 prefixEnd_1786108 := by exact prefixLift 1786108
  have htrace : WordTrace (prefixWord ++ tailWord_1786108) baseStart_1786108 baseEnd_1786108 := by
    simpa [prefixWord, tailWord_1786108, baseEnd_1786108] using wordTrace_append hprefix tailTrace_1786108
  have hstable : (prefixWord ++ tailWord_1786108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786108).length < 2 ^ (prefixWord ++ tailWord_1786108).sum := by decide
  have hdescent : baseEnd_1786108 < baseStart_1786108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786122 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1786122 : Nat := 118140960795 + 1786122 * 2 ^ 59
def prefixEnd_1786122 : Nat := 4983230072969 + 3 ^ 40 * 1786122 * 2
def baseEnd_1786122 : Nat := 407617374919984899182569

theorem tailTrace_1786122 : CollatzResearch.WordTrace tailWord_1786122 prefixEnd_1786122 407617374919984899182569 := by
  unfold tailWord_1786122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286305308798128549202155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43430147490128342797872413 16286305308798128549202155)
  ·
    refine ⟨24429457963197192823803233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16286305308798128549202155 24429457963197192823803233)
    ·
      refine ⟨18322093472397894617852425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24429457963197192823803233 18322093472397894617852425)
      ·
        refine ⟨13741570104298420963389319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18322093472397894617852425 13741570104298420963389319)
        ·
          refine ⟨20612355156447631445083979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13741570104298420963389319 20612355156447631445083979)
          ·
            refine ⟨30918532734671447167625969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20612355156447631445083979 30918532734671447167625969)
            ·
              refine ⟨23188899551003585375719477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30918532734671447167625969 23188899551003585375719477)
              ·
                refine ⟨2173959332906586128973701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23188899551003585375719477 2173959332906586128973701)
                ·
                  refine ⟨407617374919984899182569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173959332906586128973701 407617374919984899182569)
                  ·
                    rfl

theorem cell21_1786122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1786122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786122 prefixEnd_1786122 := by exact prefixLift 1786122
  have htrace : WordTrace (prefixWord ++ tailWord_1786122) baseStart_1786122 baseEnd_1786122 := by
    simpa [prefixWord, tailWord_1786122, baseEnd_1786122] using wordTrace_append hprefix tailTrace_1786122
  have hstable : (prefixWord ++ tailWord_1786122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786122).length < 2 ^ (prefixWord ++ tailWord_1786122).sum := by decide
  have hdescent : baseEnd_1786122 < baseStart_1786122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786136 : List Nat := [2, 1, 2, 3, 1, 2, 3, 7]
def baseStart_1786136 : Nat := 118140960795 + 1786136 * 2 ^ 59
def prefixEnd_1786136 : Nat := 4983230072969 + 3 ^ 40 * 1786136 * 2
def baseEnd_1786136 : Nat := 135873523303574661983069

theorem tailTrace_1786136 : CollatzResearch.WordTrace tailWord_1786136 prefixEnd_1786136 135873523303574661983069 := by
  unfold tailWord_1786136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572865928570897293909131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43430487904761196391878841 32572865928570897293909131)
  ·
    refine ⟨48859298892856345940863697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32572865928570897293909131 48859298892856345940863697)
    ·
      refine ⟨36644474169642259455647773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48859298892856345940863697 36644474169642259455647773)
      ·
        refine ⟨13741677813615847295867915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36644474169642259455647773 13741677813615847295867915)
        ·
          refine ⟨20612516720423770943801873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13741677813615847295867915 20612516720423770943801873)
          ·
            refine ⟨15459387540317828207851405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20612516720423770943801873 15459387540317828207851405)
            ·
              refine ⟨5797270327619185577944277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15459387540317828207851405 5797270327619185577944277)
              ·
                refine ⟨135873523303574661983069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5797270327619185577944277 135873523303574661983069)
                ·
                  rfl

theorem cell21_1786136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_1786136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786136 prefixEnd_1786136 := by exact prefixLift 1786136
  have htrace : WordTrace (prefixWord ++ tailWord_1786136) baseStart_1786136 baseEnd_1786136 := by
    simpa [prefixWord, tailWord_1786136, baseEnd_1786136] using wordTrace_append hprefix tailTrace_1786136
  have hstable : (prefixWord ++ tailWord_1786136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786136).length < 2 ^ (prefixWord ++ tailWord_1786136).sum := by decide
  have hdescent : baseEnd_1786136 < baseStart_1786136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786215 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_1786215 : Nat := 118140960795 + 1786215 * 2 ^ 59
def prefixEnd_1786215 : Nat := 4983230072969 + 3 ^ 40 * 1786215 * 2
def baseEnd_1786215 : Nat := 407638598787037404132379

theorem tailTrace_1786215 : CollatzResearch.WordTrace tailWord_1786215 prefixEnd_1786215 407638598787037404132379 := by
  unfold tailWord_1786215
  simp only [CollatzResearch.WordTrace]
  refine ⟨65148613223855591079944099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43432408815903727386629399 65148613223855591079944099)
  ·
    refine ⟨97722919835783386619916149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65148613223855591079944099 97722919835783386619916149)
    ·
      refine ⟨9161523734604692495617139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97722919835783386619916149 9161523734604692495617139)
      ·
        refine ⟨13742285601907038743425709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161523734604692495617139 13742285601907038743425709)
        ·
          refine ⟨5153357100715139528784641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13742285601907038743425709 5153357100715139528784641)
          ·
            refine ⟨3865017825536354646588481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5153357100715139528784641 3865017825536354646588481)
            ·
              refine ⟨2898763369152265984941361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865017825536354646588481 2898763369152265984941361)
              ·
                refine ⟨2174072526864199488706021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898763369152265984941361 2174072526864199488706021)
                ·
                  refine ⟨407638598787037404132379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174072526864199488706021 407638598787037404132379)
                  ·
                    rfl

theorem cell21_1786215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_1786215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786215 prefixEnd_1786215 := by exact prefixLift 1786215
  have htrace : WordTrace (prefixWord ++ tailWord_1786215) baseStart_1786215 baseEnd_1786215 := by
    simpa [prefixWord, tailWord_1786215, baseEnd_1786215] using wordTrace_append hprefix tailTrace_1786215
  have hstable : (prefixWord ++ tailWord_1786215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786215).length < 2 ^ (prefixWord ++ tailWord_1786215).sum := by decide
  have hdescent : baseEnd_1786215 < baseStart_1786215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786218 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_1786218 : Nat := 118140960795 + 1786218 * 2 ^ 59
def prefixEnd_1786218 : Nat := 4983230072969 + 3 ^ 40 * 1786218 * 2
def baseEnd_1786218 : Nat := 407639283427910065582373

theorem tailTrace_1786218 : CollatzResearch.WordTrace tailWord_1786218 prefixEnd_1786218 407639283427910065582373 := by
  unfold tailWord_1786218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287180660711180648075827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43432481761896481728202205 16287180660711180648075827)
  ·
    refine ⟨24430770991066770972113741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287180660711180648075827 24430770991066770972113741)
    ·
      refine ⟨9161539121650039114542653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24430770991066770972113741 9161539121650039114542653)
      ·
        refine ⟨3435577170618764667953495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9161539121650039114542653 3435577170618764667953495)
        ·
          refine ⟨5153365755928147001930243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435577170618764667953495 5153365755928147001930243)
          ·
            refine ⟨7730048633892220502895365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153365755928147001930243 7730048633892220502895365)
            ·
              refine ⟨1449384118854791344292881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7730048633892220502895365 1449384118854791344292881)
              ·
                refine ⟨1087038089141093508219661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449384118854791344292881 1087038089141093508219661)
                ·
                  refine ⟨407639283427910065582373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087038089141093508219661 407639283427910065582373)
                  ·
                    rfl

theorem cell21_1786218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_1786218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786218 prefixEnd_1786218 := by exact prefixLift 1786218
  have htrace : WordTrace (prefixWord ++ tailWord_1786218) baseStart_1786218 baseEnd_1786218 := by
    simpa [prefixWord, tailWord_1786218, baseEnd_1786218] using wordTrace_append hprefix tailTrace_1786218
  have hstable : (prefixWord ++ tailWord_1786218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786218).length < 2 ^ (prefixWord ++ tailWord_1786218).sum := by decide
  have hdescent : baseEnd_1786218 < baseStart_1786218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786229 : List Nat := [1, 3, 4, 1, 2, 1, 3, 6]
def baseStart_1786229 : Nat := 118140960795 + 1786229 * 2 ^ 59
def prefixEnd_1786229 : Nat := 4983230072969 + 3 ^ 40 * 1786229 * 2
def baseEnd_1786229 : Nat := 135880597925925496966339

theorem tailTrace_1786229 : CollatzResearch.WordTrace tailWord_1786229 prefixEnd_1786229 135880597925925496966339 := by
  unfold tailWord_1786229
  simp only [CollatzResearch.WordTrace]
  refine ⟨65149123845804871470953741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43432749230536580980635827 65149123845804871470953741)
  ·
    refine ⟨24430921442176826801607653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65149123845804871470953741 24430921442176826801607653)
    ·
      refine ⟨4580797770408155025301435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24430921442176826801607653 4580797770408155025301435)
      ·
        refine ⟨6871196655612232537952153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4580797770408155025301435 6871196655612232537952153)
        ·
          refine ⟨5153397491709174403464115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6871196655612232537952153 5153397491709174403464115)
          ·
            refine ⟨7730096237563761605196173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153397491709174403464115 7730096237563761605196173)
            ·
              refine ⟨2898786089086410601948565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7730096237563761605196173 2898786089086410601948565)
              ·
                refine ⟨135880597925925496966339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2898786089086410601948565 135880597925925496966339)
                ·
                  rfl

theorem cell21_1786229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_1786229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786229 prefixEnd_1786229 := by exact prefixLift 1786229
  have htrace : WordTrace (prefixWord ++ tailWord_1786229) baseStart_1786229 baseEnd_1786229 := by
    simpa [prefixWord, tailWord_1786229, baseEnd_1786229] using wordTrace_append hprefix tailTrace_1786229
  have hstable : (prefixWord ++ tailWord_1786229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786229).length < 2 ^ (prefixWord ++ tailWord_1786229).sum := by decide
  have hdescent : baseEnd_1786229 < baseStart_1786229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786274 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1786274 : Nat := 118140960795 + 1786274 * 2 ^ 59
def prefixEnd_1786274 : Nat := 4983230072969 + 3 ^ 40 * 1786274 * 2
def baseEnd_1786274 : Nat := 407652063390866412648925

theorem tailTrace_1786274 : CollatzResearch.WordTrace tailWord_1786274 prefixEnd_1786274 407652063390866412648925 := by
  unfold tailWord_1786274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287691282660461039085469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43433843420427896104227917 16287691282660461039085469)
  ·
    refine ⟨6107884230997672889657051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16287691282660461039085469 6107884230997672889657051)
    ·
      refine ⟨9161826346496509334485577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6107884230997672889657051 9161826346496509334485577)
      ·
        refine ⟨6871369759872382000864183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9161826346496509334485577 6871369759872382000864183)
        ·
          refine ⟨10307054639808573001296275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871369759872382000864183 10307054639808573001296275)
          ·
            refine ⟨15460581959712859501944413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307054639808573001296275 15460581959712859501944413)
            ·
              refine ⟨5797718234892322313229155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15460581959712859501944413 5797718234892322313229155)
              ·
                refine ⟨8696577352338483469843733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797718234892322313229155 8696577352338483469843733)
                ·
                  refine ⟨407652063390866412648925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8696577352338483469843733 407652063390866412648925)
                  ·
                    rfl

theorem cell21_1786274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1786274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786274 prefixEnd_1786274 := by exact prefixLift 1786274
  have htrace : WordTrace (prefixWord ++ tailWord_1786274) baseStart_1786274 baseEnd_1786274 := by
    simpa [prefixWord, tailWord_1786274, baseEnd_1786274] using wordTrace_append hprefix tailTrace_1786274
  have hstable : (prefixWord ++ tailWord_1786274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786274).length < 2 ^ (prefixWord ++ tailWord_1786274).sum := by decide
  have hdescent : baseEnd_1786274 < baseStart_1786274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786322 : List Nat := [3, 2, 2, 4, 1, 2, 7]
def baseStart_1786322 : Nat := 118140960795 + 1786322 * 2 ^ 59
def prefixEnd_1786322 : Nat := 4983230072969 + 3 ^ 40 * 1786322 * 2
def baseEnd_1786322 : Nat := 45295890849425443983203

theorem tailTrace_1786322 : CollatzResearch.WordTrace tailWord_1786322 prefixEnd_1786322 45295890849425443983203 := by
  unfold tailWord_1786322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288128958616987088522305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43435010556311965569392813 16288128958616987088522305)
  ·
    refine ⟨12216096718962740316391729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16288128958616987088522305 12216096718962740316391729)
    ·
      refine ⟨9162072539222055237293797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12216096718962740316391729 9162072539222055237293797)
      ·
        refine ⟨1717888601104135356992587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9162072539222055237293797 1717888601104135356992587)
        ·
          refine ⟨2576832901656203035488881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717888601104135356992587 2576832901656203035488881)
          ·
            refine ⟨1932624676242152276616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576832901656203035488881 1932624676242152276616661)
            ·
              refine ⟨45295890849425443983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1932624676242152276616661 45295890849425443983203)
              ·
                rfl

theorem cell21_1786322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 7].length) (baseStart_1786322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786322 prefixEnd_1786322 := by exact prefixLift 1786322
  have htrace : WordTrace (prefixWord ++ tailWord_1786322) baseStart_1786322 baseEnd_1786322 := by
    simpa [prefixWord, tailWord_1786322, baseEnd_1786322] using wordTrace_append hprefix tailTrace_1786322
  have hstable : (prefixWord ++ tailWord_1786322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786322).length < 2 ^ (prefixWord ++ tailWord_1786322).sum := by decide
  have hdescent : baseEnd_1786322 < baseStart_1786322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786429 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 3]
def baseStart_1786429 : Nat := 118140960795 + 1786429 * 2 ^ 59
def prefixEnd_1786429 : Nat := 4983230072969 + 3 ^ 40 * 1786429 * 2
def baseEnd_1786429 : Nat := 407687436502620587565275

theorem tailTrace_1786429 : CollatzResearch.WordTrace tailWord_1786429 prefixEnd_1786429 407687436502620587565275 := by
  unfold tailWord_1786429
  simp only [CollatzResearch.WordTrace]
  refine ⟨65156418445080305628234341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43437612296720203752156227 65156418445080305628234341)
  ·
    refine ⟨12216828458452557305293939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65156418445080305628234341 12216828458452557305293939)
    ·
      refine ⟨18325242687678835957940909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12216828458452557305293939 18325242687678835957940909)
      ·
        refine ⟨6871966007879563484227841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18325242687678835957940909 6871966007879563484227841)
        ·
          refine ⟨5153974505909672613170881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6871966007879563484227841 5153974505909672613170881)
          ·
            refine ⟨3865480879432254459878161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5153974505909672613170881 3865480879432254459878161)
            ·
              refine ⟨2899110659574190844908621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865480879432254459878161 2899110659574190844908621)
              ·
                refine ⟨1087166497340321566840733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899110659574190844908621 1087166497340321566840733)
                ·
                  refine ⟨407687436502620587565275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087166497340321566840733 407687436502620587565275)
                  ·
                    rfl

theorem cell21_1786429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_1786429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786429 prefixEnd_1786429 := by exact prefixLift 1786429
  have htrace : WordTrace (prefixWord ++ tailWord_1786429) baseStart_1786429 baseEnd_1786429 := by
    simpa [prefixWord, tailWord_1786429, baseEnd_1786429] using wordTrace_append hprefix tailTrace_1786429
  have hstable : (prefixWord ++ tailWord_1786429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786429).length < 2 ^ (prefixWord ++ tailWord_1786429).sum := by decide
  have hdescent : baseEnd_1786429 < baseStart_1786429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786460 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_1786460 : Nat := 118140960795 + 1786460 * 2 ^ 59
def prefixEnd_1786460 : Nat := 4983230072969 + 3 ^ 40 * 1786460 * 2
def baseEnd_1786460 : Nat := 407694511124971422548545

theorem tailTrace_1786460 : CollatzResearch.WordTrace tailWord_1786460 prefixEnd_1786460 407694511124971422548545 := by
  unfold tailWord_1786460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578774553983998961306417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43438366071978665281741889 32578774553983998961306417)
  ·
    refine ⟨24434080915487999220979813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32578774553983998961306417 24434080915487999220979813)
    ·
      refine ⟨4581390171653999853933715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24434080915487999220979813 4581390171653999853933715)
      ·
        refine ⟨6872085257480999780900573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581390171653999853933715 6872085257480999780900573)
        ·
          refine ⟨2577031971555374917837715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6872085257480999780900573 2577031971555374917837715)
          ·
            refine ⟨3865547957333062376756573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577031971555374917837715 3865547957333062376756573)
            ·
              refine ⟨1449580483999898391283715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865547957333062376756573 1449580483999898391283715)
              ·
                refine ⟨2174370725999847586925573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449580483999898391283715 2174370725999847586925573)
                ·
                  refine ⟨407694511124971422548545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174370725999847586925573 407694511124971422548545)
                  ·
                    rfl

theorem cell21_1786460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_1786460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786460 prefixEnd_1786460 := by exact prefixLift 1786460
  have htrace : WordTrace (prefixWord ++ tailWord_1786460) baseStart_1786460 baseEnd_1786460 := by
    simpa [prefixWord, tailWord_1786460, baseEnd_1786460] using wordTrace_append hprefix tailTrace_1786460
  have hstable : (prefixWord ++ tailWord_1786460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786460).length < 2 ^ (prefixWord ++ tailWord_1786460).sum := by decide
  have hdescent : baseEnd_1786460 < baseStart_1786460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786499 : List Nat := [1, 1, 1, 3, 3, 1, 11]
def baseStart_1786499 : Nat := 118140960795 + 1786499 * 2 ^ 59
def prefixEnd_1786499 : Nat := 4983230072969 + 3 ^ 40 * 1786499 * 2
def baseEnd_1786499 : Nat := 45300379050701780155385

theorem tailTrace_1786499 : CollatzResearch.WordTrace tailWord_1786499 prefixEnd_1786499 45300379050701780155385 := by
  unfold tailWord_1786499
  simp only [CollatzResearch.WordTrace]
  refine ⟨65158971554826707583282551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43439314369884471722188367 65158971554826707583282551)
  ·
    refine ⟨97738457332240061374923827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65158971554826707583282551 97738457332240061374923827)
    ·
      refine ⟨146607685998360092062385741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97738457332240061374923827 146607685998360092062385741)
      ·
        refine ⟨54977882249385034523394653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146607685998360092062385741 54977882249385034523394653)
        ·
          refine ⟨20616705843519387946272995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54977882249385034523394653 20616705843519387946272995)
          ·
            refine ⟨30925058765279081919409493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20616705843519387946272995 30925058765279081919409493)
            ·
              refine ⟨45300379050701780155385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30925058765279081919409493 45300379050701780155385)
              ·
                rfl

theorem cell21_1786499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_1786499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786499 prefixEnd_1786499 := by exact prefixLift 1786499
  have htrace : WordTrace (prefixWord ++ tailWord_1786499) baseStart_1786499 baseEnd_1786499 := by
    simpa [prefixWord, tailWord_1786499, baseEnd_1786499] using wordTrace_append hprefix tailTrace_1786499
  have hstable : (prefixWord ++ tailWord_1786499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786499).length < 2 ^ (prefixWord ++ tailWord_1786499).sum := by decide
  have hdescent : baseEnd_1786499 < baseStart_1786499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786550 : List Nat := [5, 1, 3, 1, 3, 8]
def baseStart_1786550 : Nat := 118140960795 + 1786550 * 2 ^ 59
def prefixEnd_1786550 : Nat := 4983230072969 + 3 ^ 40 * 1786550 * 2
def baseEnd_1786550 : Nat := 15100557420413009853643

theorem tailTrace_1786550 : CollatzResearch.WordTrace tailWord_1786550 prefixEnd_1786550 15100557420413009853643 := by
  unfold tailWord_1786550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072551979852621455836819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43440554451761295528926069 4072551979852621455836819)
  ·
    refine ⟨6108827969778932183755229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072551979852621455836819 6108827969778932183755229)
    ·
      refine ⟨2290810488667099568908211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6108827969778932183755229 2290810488667099568908211)
      ·
        refine ⟨3436215733000649353362317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290810488667099568908211 3436215733000649353362317)
        ·
          refine ⟨1288580899875243507510869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3436215733000649353362317 1288580899875243507510869)
          ·
            refine ⟨15100557420413009853643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1288580899875243507510869 15100557420413009853643)
            ·
              rfl

theorem cell21_1786550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 8].length) (baseStart_1786550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786550 prefixEnd_1786550 := by exact prefixLift 1786550
  have htrace : WordTrace (prefixWord ++ tailWord_1786550) baseStart_1786550 baseEnd_1786550 := by
    simpa [prefixWord, tailWord_1786550, baseEnd_1786550] using wordTrace_append hprefix tailTrace_1786550
  have hstable : (prefixWord ++ tailWord_1786550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786550).length < 2 ^ (prefixWord ++ tailWord_1786550).sum := by decide
  have hdescent : baseEnd_1786550 < baseStart_1786550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786612 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1786612 : Nat := 118140960795 + 1786612 * 2 ^ 59
def prefixEnd_1786612 : Nat := 4983230072969 + 3 ^ 40 * 1786612 * 2
def baseEnd_1786612 : Nat := 407729199595852936014901

theorem tailTrace_1786612 : CollatzResearch.WordTrace tailWord_1786612 prefixEnd_1786612 407729199595852936014901 := by
  unfold tailWord_1786612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32581546501708663941073045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43442062002278218588097393 32581546501708663941073045)
  ·
    refine ⟨1527259992267593622237799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32581546501708663941073045 1527259992267593622237799)
    ·
      refine ⟨2290889988401390433356699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527259992267593622237799 2290889988401390433356699)
      ·
        refine ⟨3436334982602085650035049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290889988401390433356699 3436334982602085650035049)
        ·
          refine ⟨2577251236951564237526287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436334982602085650035049 2577251236951564237526287)
          ·
            refine ⟨3865876855427346356289431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577251236951564237526287 3865876855427346356289431)
            ·
              refine ⟨5798815283141019534434147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865876855427346356289431 5798815283141019534434147)
              ·
                refine ⟨8698222924711529301651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798815283141019534434147 8698222924711529301651221)
                ·
                  refine ⟨407729199595852936014901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8698222924711529301651221 407729199595852936014901)
                  ·
                    rfl

theorem cell21_1786612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1786612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786612 prefixEnd_1786612 := by exact prefixLift 1786612
  have htrace : WordTrace (prefixWord ++ tailWord_1786612) baseStart_1786612 baseEnd_1786612 := by
    simpa [prefixWord, tailWord_1786612, baseEnd_1786612] using wordTrace_append hprefix tailTrace_1786612
  have hstable : (prefixWord ++ tailWord_1786612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786612).length < 2 ^ (prefixWord ++ tailWord_1786612).sum := by decide
  have hdescent : baseEnd_1786612 < baseStart_1786612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786685 : List Nat := [1, 4, 1, 4, 2, 1, 2, 6]
def baseStart_1786685 : Nat := 118140960795 + 1786685 * 2 ^ 59
def prefixEnd_1786685 : Nat := 4983230072969 + 3 ^ 40 * 1786685 * 2
def baseEnd_1786685 : Nat := 135915286396807010432695

theorem tailTrace_1786685 : CollatzResearch.WordTrace tailWord_1786685 prefixEnd_1786685 135915286396807010432695 := by
  unfold tailWord_1786685
  simp only [CollatzResearch.WordTrace]
  refine ⟨65165755532152861349553509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43443837021435240899702339 65165755532152861349553509)
  ·
    refine ⟨12218579162278661503041283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65165755532152861349553509 12218579162278661503041283)
    ·
      refine ⟨18327868743417992254561925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218579162278661503041283 18327868743417992254561925)
      ·
        refine ⟨3436475389390873547730361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18327868743417992254561925 3436475389390873547730361)
        ·
          refine ⟨2577356542043155160797771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436475389390873547730361 2577356542043155160797771)
          ·
            refine ⟨3866034813064732741196657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577356542043155160797771 3866034813064732741196657)
            ·
              refine ⟨2899526109798549555897493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866034813064732741196657 2899526109798549555897493)
              ·
                refine ⟨135915286396807010432695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2899526109798549555897493 135915286396807010432695)
                ·
                  rfl

theorem cell21_1786685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_1786685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786685 prefixEnd_1786685 := by exact prefixLift 1786685
  have htrace : WordTrace (prefixWord ++ tailWord_1786685) baseStart_1786685 baseEnd_1786685 := by
    simpa [prefixWord, tailWord_1786685, baseEnd_1786685] using wordTrace_append hprefix tailTrace_1786685
  have hstable : (prefixWord ++ tailWord_1786685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786685).length < 2 ^ (prefixWord ++ tailWord_1786685).sum := by decide
  have hdescent : baseEnd_1786685 < baseStart_1786685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786727 : List Nat := [1, 1, 5, 1, 2, 11]
def baseStart_1786727 : Nat := 118140960795 + 1786727 * 2 ^ 59
def prefixEnd_1786727 : Nat := 4983230072969 + 3 ^ 40 * 1786727 * 2
def baseEnd_1786727 : Nat := 15102053487505121911037

theorem tailTrace_1786727 : CollatzResearch.WordTrace tailWord_1786727 prefixEnd_1786727 15102053487505121911037 := by
  unfold tailWord_1786727
  simp only [CollatzResearch.WordTrace]
  refine ⟨65167287398000702522582435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43444858265333801681721623 65167287398000702522582435)
  ·
    refine ⟨97750931097001053783873653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65167287398000702522582435 97750931097001053783873653)
    ·
      refine ⟨9164149790343848792238155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97750931097001053783873653 9164149790343848792238155)
      ·
        refine ⟨13746224685515773188357233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9164149790343848792238155 13746224685515773188357233)
        ·
          refine ⟨10309668514136829891267925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13746224685515773188357233 10309668514136829891267925)
          ·
            refine ⟨15102053487505121911037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10309668514136829891267925 15102053487505121911037)
            ·
              rfl

theorem cell21_1786727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 11].length) (baseStart_1786727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786727 prefixEnd_1786727 := by exact prefixLift 1786727
  have htrace : WordTrace (prefixWord ++ tailWord_1786727) baseStart_1786727 baseEnd_1786727 := by
    simpa [prefixWord, tailWord_1786727, baseEnd_1786727] using wordTrace_append hprefix tailTrace_1786727
  have hstable : (prefixWord ++ tailWord_1786727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786727).length < 2 ^ (prefixWord ++ tailWord_1786727).sum := by decide
  have hdescent : baseEnd_1786727 < baseStart_1786727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786837 : List Nat := [1, 3, 2, 3, 4, 1, 7]
def baseStart_1786837 : Nat := 118140960795 + 1786837 * 2 ^ 59
def prefixEnd_1786837 : Nat := 4983230072969 + 3 ^ 40 * 1786837 * 2
def baseEnd_1786837 : Nat := 45308949740144727196049

theorem tailTrace_1786837 : CollatzResearch.WordTrace tailWord_1786837 prefixEnd_1786837 45308949740144727196049 := by
  unfold tailWord_1786837
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171299427602191309086765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43447532951734794206057843 65171299427602191309086765)
  ·
    refine ⟨24439237285350821740907537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65171299427602191309086765 24439237285350821740907537)
    ·
      refine ⟨18329427964013116305680653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24439237285350821740907537 18329427964013116305680653)
      ·
        refine ⟨6873535486504918614630245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18329427964013116305680653 6873535486504918614630245)
        ·
          refine ⟨1288787903719672240243171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6873535486504918614630245 1288787903719672240243171)
          ·
            refine ⟨1933181855579508360364757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288787903719672240243171 1933181855579508360364757)
            ·
              refine ⟨45308949740144727196049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1933181855579508360364757 45308949740144727196049)
              ·
                rfl

theorem cell21_1786837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 7].length) (baseStart_1786837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786837 prefixEnd_1786837 := by exact prefixLift 1786837
  have htrace : WordTrace (prefixWord ++ tailWord_1786837) baseStart_1786837 baseEnd_1786837 := by
    simpa [prefixWord, tailWord_1786837, baseEnd_1786837] using wordTrace_append hprefix tailTrace_1786837
  have hstable : (prefixWord ++ tailWord_1786837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786837).length < 2 ^ (prefixWord ++ tailWord_1786837).sum := by decide
  have hdescent : baseEnd_1786837 < baseStart_1786837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786989 : List Nat := [1, 5, 1, 1, 2, 4, 2, 5]
def baseStart_1786989 : Nat := 118140960795 + 1786989 * 2 ^ 59
def prefixEnd_1786989 : Nat := 4983230072969 + 3 ^ 40 * 1786989 * 2
def baseEnd_1786989 : Nat := 135938412044061352743599

theorem tailTrace_1786989 : CollatzResearch.WordTrace tailWord_1786989 prefixEnd_1786989 135938412044061352743599 := by
  unfold tailWord_1786989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65176843323051521268620021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43451228882034347512413347 65176843323051521268620021)
  ·
    refine ⟨6110329061536080118933127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65176843323051521268620021 6110329061536080118933127)
    ·
      refine ⟨9165493592304120178399691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110329061536080118933127 9165493592304120178399691)
      ·
        refine ⟨13748240388456180267599537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165493592304120178399691 13748240388456180267599537)
        ·
          refine ⟨10311180291342135200699653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13748240388456180267599537 10311180291342135200699653)
          ·
            refine ⟨1933346304626650350131185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10311180291342135200699653 1933346304626650350131185)
            ·
              refine ⟨1450009728469987762598389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933346304626650350131185 1450009728469987762598389)
              ·
                refine ⟨135938412044061352743599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450009728469987762598389 135938412044061352743599)
                ·
                  rfl

theorem cell21_1786989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].length) (baseStart_1786989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1786989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1786989 prefixEnd_1786989 := by exact prefixLift 1786989
  have htrace : WordTrace (prefixWord ++ tailWord_1786989) baseStart_1786989 baseEnd_1786989 := by
    simpa [prefixWord, tailWord_1786989, baseEnd_1786989] using wordTrace_append hprefix tailTrace_1786989
  have hstable : (prefixWord ++ tailWord_1786989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786989).length < 2 ^ (prefixWord ++ tailWord_1786989).sum := by decide
  have hdescent : baseEnd_1786989 < baseStart_1786989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787000 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_1787000 : Nat := 118140960795 + 1787000 * 2 ^ 59
def prefixEnd_1787000 : Nat := 4983230072969 + 3 ^ 40 * 1787000 * 2
def baseEnd_1787000 : Nat := 407817746482050483547441

theorem tailTrace_1787000 : CollatzResearch.WordTrace tailWord_1787000 prefixEnd_1787000 407817746482050483547441 := by
  unfold tailWord_1787000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588622263005835073635227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43451496350674446764846969 32588622263005835073635227)
  ·
    refine ⟨48882933394508752610452841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32588622263005835073635227 48882933394508752610452841)
    ·
      refine ⟨36662200045881564457839631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48882933394508752610452841 36662200045881564457839631)
      ·
        refine ⟨54993300068822346686759447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36662200045881564457839631 54993300068822346686759447)
        ·
          refine ⟨82489950103233520030139171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54993300068822346686759447 82489950103233520030139171)
          ·
            refine ⟨123734925154850280045208757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82489950103233520030139171 123734925154850280045208757)
            ·
              refine ⟨11600149233267213754238321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123734925154850280045208757 11600149233267213754238321)
              ·
                refine ⟨8700111924950410315678741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600149233267213754238321 8700111924950410315678741)
                ·
                  refine ⟨407817746482050483547441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700111924950410315678741 407817746482050483547441)
                  ·
                    rfl

theorem cell21_1787000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_1787000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787000 prefixEnd_1787000 := by exact prefixLift 1787000
  have htrace : WordTrace (prefixWord ++ tailWord_1787000) baseStart_1787000 baseEnd_1787000 := by
    simpa [prefixWord, tailWord_1787000, baseEnd_1787000] using wordTrace_append hprefix tailTrace_1787000
  have hstable : (prefixWord ++ tailWord_1787000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787000).length < 2 ^ (prefixWord ++ tailWord_1787000).sum := by decide
  have hdescent : baseEnd_1787000 < baseStart_1787000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787031 : List Nat := [1, 1, 3, 3, 3, 1, 1, 8]
def baseStart_1787031 : Nat := 118140960795 + 1787031 * 2 ^ 59
def prefixEnd_1787031 : Nat := 4983230072969 + 3 ^ 40 * 1787031 * 2
def baseEnd_1787031 : Nat := 135941607034800439510237

theorem tailTrace_1787031 : CollatzResearch.WordTrace tailWord_1787031 prefixEnd_1787031 135941607034800439510237 := by
  unfold tailWord_1787031
  simp only [CollatzResearch.WordTrace]
  refine ⟨65178375188899362441648947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43452250125932908294432631 65178375188899362441648947)
  ·
    refine ⟨97767562783349043662473421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65178375188899362441648947 97767562783349043662473421)
    ·
      refine ⟨36662836043755891373427533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97767562783349043662473421 36662836043755891373427533)
      ·
        refine ⟨13748563516408459265035325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36662836043755891373427533 13748563516408459265035325)
        ·
          refine ⟨5155711318653172224388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13748563516408459265035325 5155711318653172224388247)
          ·
            refine ⟨7733566977979758336582371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155711318653172224388247 7733566977979758336582371)
            ·
              refine ⟨11600350466969637504873557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733566977979758336582371 11600350466969637504873557)
              ·
                refine ⟨135941607034800439510237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11600350466969637504873557 135941607034800439510237)
                ·
                  rfl

theorem cell21_1787031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_1787031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787031 prefixEnd_1787031 := by exact prefixLift 1787031
  have htrace : WordTrace (prefixWord ++ tailWord_1787031) baseStart_1787031 baseEnd_1787031 := by
    simpa [prefixWord, tailWord_1787031, baseEnd_1787031] using wordTrace_append hprefix tailTrace_1787031
  have hstable : (prefixWord ++ tailWord_1787031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787031).length < 2 ^ (prefixWord ++ tailWord_1787031).sum := by decide
  have hdescent : baseEnd_1787031 < baseStart_1787031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787034 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1787034 : Nat := 118140960795 + 1787034 * 2 ^ 59
def prefixEnd_1787034 : Nat := 4983230072969 + 3 ^ 40 * 1787034 * 2
def baseEnd_1787034 : Nat := 407825505745273979980705

theorem tailTrace_1787034 : CollatzResearch.WordTrace tailWord_1787034 prefixEnd_1787034 407825505745273979980705 := by
  unfold tailWord_1787034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294621151972123488502039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43452323071925662636005437 16294621151972123488502039)
  ·
    refine ⟨24441931727958185232753059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16294621151972123488502039 24441931727958185232753059)
    ·
      refine ⟨36662897591937277849129589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24441931727958185232753059 36662897591937277849129589)
      ·
        refine ⟨3437146649244119798355899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36662897591937277849129589 3437146649244119798355899)
        ·
          refine ⟨5155719973866179697533849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437146649244119798355899 5155719973866179697533849)
          ·
            refine ⟨3866789980399634773150387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155719973866179697533849 3866789980399634773150387)
            ·
              refine ⟨5800184970599452159725581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866789980399634773150387 5800184970599452159725581)
              ·
                refine ⟨2175069363974794559897093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800184970599452159725581 2175069363974794559897093)
                ·
                  refine ⟨407825505745273979980705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2175069363974794559897093 407825505745273979980705)
                  ·
                    rfl

theorem cell21_1787034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1787034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787034 prefixEnd_1787034 := by exact prefixLift 1787034
  have htrace : WordTrace (prefixWord ++ tailWord_1787034) baseStart_1787034 baseEnd_1787034 := by
    simpa [prefixWord, tailWord_1787034, baseEnd_1787034] using wordTrace_append hprefix tailTrace_1787034
  have hstable : (prefixWord ++ tailWord_1787034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787034).length < 2 ^ (prefixWord ++ tailWord_1787034).sum := by decide
  have hdescent : baseEnd_1787034 < baseStart_1787034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787121 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1787121 : Nat := 118140960795 + 1787121 * 2 ^ 59
def prefixEnd_1787121 : Nat := 4983230072969 + 3 ^ 40 * 1787121 * 2
def baseEnd_1787121 : Nat := 407845360330581162030527

theorem tailTrace_1787121 : CollatzResearch.WordTrace tailWord_1787121 prefixEnd_1787121 407845360330581162030527 := by
  unfold tailWord_1787121
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181657758573307812425217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43454438505715538541616811 65181657758573307812425217)
  ·
    refine ⟨48886243318929980859318913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65181657758573307812425217 48886243318929980859318913)
    ·
      refine ⟨36664682489197485644489185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48886243318929980859318913 36664682489197485644489185)
      ·
        refine ⟨27498511866898114233366889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36664682489197485644489185 27498511866898114233366889)
        ·
          refine ⟨20623883900173585675025167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27498511866898114233366889 20623883900173585675025167)
          ·
            refine ⟨30935825850260378512537751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623883900173585675025167 30935825850260378512537751)
            ·
              refine ⟨46403738775390567768806627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30935825850260378512537751 46403738775390567768806627)
              ·
                refine ⟨69605608163085851653209941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46403738775390567768806627 69605608163085851653209941)
                ·
                  refine ⟨407845360330581162030527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69605608163085851653209941 407845360330581162030527)
                  ·
                    rfl

theorem cell21_1787121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1787121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787121 prefixEnd_1787121 := by exact prefixLift 1787121
  have htrace : WordTrace (prefixWord ++ tailWord_1787121) baseStart_1787121 baseEnd_1787121 := by
    simpa [prefixWord, tailWord_1787121, baseEnd_1787121] using wordTrace_append hprefix tailTrace_1787121
  have hstable : (prefixWord ++ tailWord_1787121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787121).length < 2 ^ (prefixWord ++ tailWord_1787121).sum := by decide
  have hdescent : baseEnd_1787121 < baseStart_1787121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787245 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1787245 : Nat := 118140960795 + 1787245 * 2 ^ 59
def prefixEnd_1787245 : Nat := 4983230072969 + 3 ^ 40 * 1787245 * 2
def baseEnd_1787245 : Nat := 407873658819984501963607

theorem tailTrace_1787245 : CollatzResearch.WordTrace tailWord_1787245 prefixEnd_1787245 407873658819984501963607 := by
  unfold tailWord_1787245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65186180410124076989939189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43457453606749384659959459 65186180410124076989939189)
  ·
    refine ⟨6111204413449132217806799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65186180410124076989939189 6111204413449132217806799)
    ·
      refine ⟨9166806620173698326710199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6111204413449132217806799 9166806620173698326710199)
      ·
        refine ⟨13750209930260547490065299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9166806620173698326710199 13750209930260547490065299)
        ·
          refine ⟨20625314895390821235097949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750209930260547490065299 20625314895390821235097949)
          ·
            refine ⟨7734493085771557963161731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20625314895390821235097949 7734493085771557963161731)
            ·
              refine ⟨11601739628657336944742597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734493085771557963161731 11601739628657336944742597)
              ·
                refine ⟨2175326180373250677139237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11601739628657336944742597 2175326180373250677139237)
                ·
                  refine ⟨407873658819984501963607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2175326180373250677139237 407873658819984501963607)
                  ·
                    rfl

theorem cell21_1787245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1787245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787245 prefixEnd_1787245 := by exact prefixLift 1787245
  have htrace : WordTrace (prefixWord ++ tailWord_1787245) baseStart_1787245 baseEnd_1787245 := by
    simpa [prefixWord, tailWord_1787245, baseEnd_1787245] using wordTrace_append hprefix tailTrace_1787245
  have hstable : (prefixWord ++ tailWord_1787245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787245).length < 2 ^ (prefixWord ++ tailWord_1787245).sum := by decide
  have hdescent : baseEnd_1787245 < baseStart_1787245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787504 : List Nat := [2, 1, 1, 1, 6, 3, 2, 5]
def baseStart_1787504 : Nat := 118140960795 + 1787504 * 2 ^ 59
def prefixEnd_1787504 : Nat := 4983230072969 + 3 ^ 40 * 1787504 * 2
def baseEnd_1787504 : Nat := 135977588716219202382137

theorem tailTrace_1787504 : CollatzResearch.WordTrace tailWord_1787504 prefixEnd_1787504 135977588716219202382137 := by
  unfold tailWord_1787504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32597813458092882111808783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43463751277457176149078377 32597813458092882111808783)
  ·
    refine ⟨48896720187139323167713175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32597813458092882111808783 48896720187139323167713175)
    ·
      refine ⟨73345080280708984751569763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48896720187139323167713175 73345080280708984751569763)
      ·
        refine ⟨110017620421063477127354645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73345080280708984751569763 110017620421063477127354645)
        ·
          refine ⟨5157075957237350490344749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110017620421063477127354645 5157075957237350490344749)
          ·
            refine ⟨1933903483964006433879281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5157075957237350490344749 1933903483964006433879281)
            ·
              refine ⟨1450427612973004825409461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933903483964006433879281 1450427612973004825409461)
              ·
                refine ⟨135977588716219202382137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450427612973004825409461 135977588716219202382137)
                ·
                  rfl

theorem cell21_1787504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_1787504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787504 prefixEnd_1787504 := by exact prefixLift 1787504
  have htrace : WordTrace (prefixWord ++ tailWord_1787504) baseStart_1787504 baseEnd_1787504 := by
    simpa [prefixWord, tailWord_1787504, baseEnd_1787504] using wordTrace_append hprefix tailTrace_1787504
  have hstable : (prefixWord ++ tailWord_1787504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787504).length < 2 ^ (prefixWord ++ tailWord_1787504).sum := by decide
  have hdescent : baseEnd_1787504 < baseStart_1787504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787515 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_1787515 : Nat := 118140960795 + 1787515 * 2 ^ 59
def prefixEnd_1787515 : Nat := 4983230072969 + 3 ^ 40 * 1787515 * 2
def baseEnd_1787515 : Nat := 407935276498524032463055

theorem tailTrace_1787515 : CollatzResearch.WordTrace tailWord_1787515 prefixEnd_1787515 407935276498524032463055 := by
  unfold tailWord_1787515
  simp only [CollatzResearch.WordTrace]
  refine ⟨65196028119145913102267999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43464018746097275401511999 65196028119145913102267999)
  ·
    refine ⟨97794042178718869653401999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65196028119145913102267999 97794042178718869653401999)
    ·
      refine ⟨146691063268078304480102999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97794042178718869653401999 146691063268078304480102999)
      ·
        refine ⟨220036594902117456720154499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146691063268078304480102999 220036594902117456720154499)
        ·
          refine ⟨330054892353176185080231749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220036594902117456720154499 330054892353176185080231749)
          ·
            refine ⟨61885292316220534702543453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330054892353176185080231749 61885292316220534702543453)
            ·
              refine ⟨23206984618582700513453795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61885292316220534702543453 23206984618582700513453795)
              ·
                refine ⟨34810476927874050770180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23206984618582700513453795 34810476927874050770180693)
                ·
                  refine ⟨407935276498524032463055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34810476927874050770180693 407935276498524032463055)
                  ·
                    rfl

theorem cell21_1787515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_1787515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787515 prefixEnd_1787515 := by exact prefixLift 1787515
  have htrace : WordTrace (prefixWord ++ tailWord_1787515) baseStart_1787515 baseEnd_1787515 := by
    simpa [prefixWord, tailWord_1787515, baseEnd_1787515] using wordTrace_append hprefix tailTrace_1787515
  have hstable : (prefixWord ++ tailWord_1787515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787515).length < 2 ^ (prefixWord ++ tailWord_1787515).sum := by decide
  have hdescent : baseEnd_1787515 < baseStart_1787515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787532 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1787532 : Nat := 118140960795 + 1787532 * 2 ^ 59
def prefixEnd_1787532 : Nat := 4983230072969 + 3 ^ 40 * 1787532 * 2
def baseEnd_1787532 : Nat := 407939156130135780679687

theorem tailTrace_1787532 : CollatzResearch.WordTrace tailWord_1787532 prefixEnd_1787532 407939156130135780679687 := by
  unfold tailWord_1787532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32598324080042162502818425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43464432106722883337091233 32598324080042162502818425)
  ·
    refine ⟨24448743060031621877113819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32598324080042162502818425 24448743060031621877113819)
    ·
      refine ⟨36673114590047432815670729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24448743060031621877113819 36673114590047432815670729)
      ·
        refine ⟨27504835942535574611753047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36673114590047432815670729 27504835942535574611753047)
        ·
          refine ⟨41257253913803361917629571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27504835942535574611753047 41257253913803361917629571)
          ·
            refine ⟨61885880870705042876444357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41257253913803361917629571 61885880870705042876444357)
            ·
              refine ⟨11603602663257195539333317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61885880870705042876444357 11603602663257195539333317)
              ·
                refine ⟨2175675499360724163624997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11603602663257195539333317 2175675499360724163624997)
                ·
                  refine ⟨407939156130135780679687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2175675499360724163624997 407939156130135780679687)
                  ·
                    rfl

theorem cell21_1787532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1787532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787532 prefixEnd_1787532 := by exact prefixLift 1787532
  have htrace : WordTrace (prefixWord ++ tailWord_1787532) baseStart_1787532 baseEnd_1787532 := by
    simpa [prefixWord, tailWord_1787532, baseEnd_1787532] using wordTrace_append hprefix tailTrace_1787532
  have hstable : (prefixWord ++ tailWord_1787532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787532).length < 2 ^ (prefixWord ++ tailWord_1787532).sum := by decide
  have hdescent : baseEnd_1787532 < baseStart_1787532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787586 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1787586 : Nat := 118140960795 + 1787586 * 2 ^ 59
def prefixEnd_1787586 : Nat := 4983230072969 + 3 ^ 40 * 1787586 * 2
def baseEnd_1787586 : Nat := 407951479665843686779577

theorem tailTrace_1787586 : CollatzResearch.WordTrace tailWord_1787586 prefixEnd_1787586 407951479665843686779577 := by
  unfold tailWord_1787586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299654425472173057025653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43465745134592461485401741 16299654425472173057025653)
  ·
    refine ⟨1528092602388016224096155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16299654425472173057025653 1528092602388016224096155)
    ·
      refine ⟨2292138903582024336144233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528092602388016224096155 2292138903582024336144233)
      ·
        refine ⟨1719104177686518252108175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2292138903582024336144233 1719104177686518252108175)
        ·
          refine ⟨2578656266529777378162263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719104177686518252108175 2578656266529777378162263)
          ·
            refine ⟨3867984399794666067243395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578656266529777378162263 3867984399794666067243395)
            ·
              refine ⟨5801976599691999100865093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867984399794666067243395 5801976599691999100865093)
              ·
                refine ⟨1087870612442249831412205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5801976599691999100865093 1087870612442249831412205)
                ·
                  refine ⟨407951479665843686779577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087870612442249831412205 407951479665843686779577)
                  ·
                    rfl

theorem cell21_1787586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1787586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787586 prefixEnd_1787586 := by exact prefixLift 1787586
  have htrace : WordTrace (prefixWord ++ tailWord_1787586) baseStart_1787586 baseEnd_1787586 := by
    simpa [prefixWord, tailWord_1787586, baseEnd_1787586] using wordTrace_append hprefix tailTrace_1787586
  have hstable : (prefixWord ++ tailWord_1787586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787586).length < 2 ^ (prefixWord ++ tailWord_1787586).sum := by decide
  have hdescent : baseEnd_1787586 < baseStart_1787586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787597 : List Nat := [1, 6, 2, 1, 1, 3, 1, 6]
def baseStart_1787597 : Nat := 118140960795 + 1787597 * 2 ^ 59
def prefixEnd_1787597 : Nat := 4983230072969 + 3 ^ 40 * 1787597 * 2
def baseEnd_1787597 : Nat := 135984663338570037365407

theorem tailTrace_1787597 : CollatzResearch.WordTrace tailWord_1787597 prefixEnd_1787597 135984663338570037365407 := by
  unfold tailWord_1787597
  simp only [CollatzResearch.WordTrace]
  refine ⟨65199018904848841106753045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43466012603232560737835363 65199018904848841106753045)
  ·
    refine ⟨3056204011164789426879049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65199018904848841106753045 3056204011164789426879049)
    ·
      refine ⟨2292153008373592070159287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3056204011164789426879049 2292153008373592070159287)
      ·
        refine ⟨3438229512560388105238931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292153008373592070159287 3438229512560388105238931)
        ·
          refine ⟨5157344268840582157858397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438229512560388105238931 5157344268840582157858397)
          ·
            refine ⟨1934004100815218309196899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5157344268840582157858397 1934004100815218309196899)
            ·
              refine ⟨2901006151222827463795349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934004100815218309196899 2901006151222827463795349)
              ·
                refine ⟨135984663338570037365407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2901006151222827463795349 135984663338570037365407)
                ·
                  rfl

theorem cell21_1787597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_1787597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787597 prefixEnd_1787597 := by exact prefixLift 1787597
  have htrace : WordTrace (prefixWord ++ tailWord_1787597) baseStart_1787597 baseEnd_1787597 := by
    simpa [prefixWord, tailWord_1787597, baseEnd_1787597] using wordTrace_append hprefix tailTrace_1787597
  have hstable : (prefixWord ++ tailWord_1787597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787597).length < 2 ^ (prefixWord ++ tailWord_1787597).sum := by decide
  have hdescent : baseEnd_1787597 < baseStart_1787597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787608 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_1787608 : Nat := 118140960795 + 1787608 * 2 ^ 59
def prefixEnd_1787608 : Nat := 4983230072969 + 3 ^ 40 * 1787608 * 2
def baseEnd_1787608 : Nat := 407956500365576537412865

theorem tailTrace_1787608 : CollatzResearch.WordTrace tailWord_1787608 prefixEnd_1787608 407956500365576537412865 := by
  unfold tailWord_1787608
  simp only [CollatzResearch.WordTrace]
  refine ⟨32599710053904494992701739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43466280071872659990268985 32599710053904494992701739)
  ·
    refine ⟨48899565080856742489052609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32599710053904494992701739 48899565080856742489052609)
    ·
      refine ⟨36674673810642556866789457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48899565080856742489052609 36674673810642556866789457)
      ·
        refine ⟨27506005357981917650092093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36674673810642556866789457 27506005357981917650092093)
        ·
          refine ⟨10314752009243219118784535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27506005357981917650092093 10314752009243219118784535)
          ·
            refine ⟨15472128013864828678176803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314752009243219118784535 15472128013864828678176803)
            ·
              refine ⟨23208192020797243017265205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472128013864828678176803 23208192020797243017265205)
              ·
                refine ⟨2175768001949741532868613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23208192020797243017265205 2175768001949741532868613)
                ·
                  refine ⟨407956500365576537412865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2175768001949741532868613 407956500365576537412865)
                  ·
                    rfl

theorem cell21_1787608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_1787608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787608 prefixEnd_1787608 := by exact prefixLift 1787608
  have htrace : WordTrace (prefixWord ++ tailWord_1787608) baseStart_1787608 baseEnd_1787608 := by
    simpa [prefixWord, tailWord_1787608, baseEnd_1787608] using wordTrace_append hprefix tailTrace_1787608
  have hstable : (prefixWord ++ tailWord_1787608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787608).length < 2 ^ (prefixWord ++ tailWord_1787608).sum := by decide
  have hdescent : baseEnd_1787608 < baseStart_1787608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787684 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1787684 : Nat := 118140960795 + 1787684 * 2 ^ 59
def prefixEnd_1787684 : Nat := 4983230072969 + 3 ^ 40 * 1787684 * 2
def baseEnd_1787684 : Nat := 407973844601017294146043

theorem tailTrace_1787684 : CollatzResearch.WordTrace tailWord_1787684 prefixEnd_1787684 407973844601017294146043 := by
  unfold tailWord_1787684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601096027766827482585053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43468128037022436643446737 32601096027766827482585053)
  ·
    refine ⟨12225411010412560305969395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32601096027766827482585053 12225411010412560305969395)
    ·
      refine ⟨18338116515618840458954093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225411010412560305969395 18338116515618840458954093)
      ·
        refine ⟨6876793693357065172107785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18338116515618840458954093 6876793693357065172107785)
        ·
          refine ⟨5157595270017798879080839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6876793693357065172107785 5157595270017798879080839)
          ·
            refine ⟨7736392905026698318621259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157595270017798879080839 7736392905026698318621259)
            ·
              refine ⟨11604589357540047477931889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736392905026698318621259 11604589357540047477931889)
              ·
                refine ⟨8703442018155035608448917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604589357540047477931889 8703442018155035608448917)
                ·
                  refine ⟨407973844601017294146043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8703442018155035608448917 407973844601017294146043)
                  ·
                    rfl

theorem cell21_1787684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1787684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787684 prefixEnd_1787684 := by exact prefixLift 1787684
  have htrace : WordTrace (prefixWord ++ tailWord_1787684) baseStart_1787684 baseEnd_1787684 := by
    simpa [prefixWord, tailWord_1787684, baseEnd_1787684] using wordTrace_append hprefix tailTrace_1787684
  have hstable : (prefixWord ++ tailWord_1787684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787684).length < 2 ^ (prefixWord ++ tailWord_1787684).sum := by decide
  have hdescent : baseEnd_1787684 < baseStart_1787684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787698 : List Nat := [3, 2, 1, 1, 3, 2, 9]
def baseStart_1787698 : Nat := 118140960795 + 1787698 * 2 ^ 59
def prefixEnd_1787698 : Nat := 4983230072969 + 3 ^ 40 * 1787698 * 2
def baseEnd_1787698 : Nat := 45330782176861820101409

theorem tailTrace_1787698 : CollatzResearch.WordTrace tailWord_1787698 prefixEnd_1787698 45330782176861820101409 := by
  unfold tailWord_1787698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300675669370733839044937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43468468451655290237453165 16300675669370733839044937)
  ·
    refine ⟨12225506752028050379283703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16300675669370733839044937 12225506752028050379283703)
    ·
      refine ⟨18338260128042075568925555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225506752028050379283703 18338260128042075568925555)
      ·
        refine ⟨27507390192063113353388333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18338260128042075568925555 27507390192063113353388333)
        ·
          refine ⟨10315271322023667507520625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27507390192063113353388333 10315271322023667507520625)
          ·
            refine ⟨7736453491517750630640469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10315271322023667507520625 7736453491517750630640469)
            ·
              refine ⟨45330782176861820101409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7736453491517750630640469 45330782176861820101409)
              ·
                rfl

theorem cell21_1787698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 9].length) (baseStart_1787698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787698 prefixEnd_1787698 := by exact prefixLift 1787698
  have htrace : WordTrace (prefixWord ++ tailWord_1787698) baseStart_1787698 baseEnd_1787698 := by
    simpa [prefixWord, tailWord_1787698, baseEnd_1787698] using wordTrace_append hprefix tailTrace_1787698
  have hstable : (prefixWord ++ tailWord_1787698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787698).length < 2 ^ (prefixWord ++ tailWord_1787698).sum := by decide
  have hdescent : baseEnd_1787698 < baseStart_1787698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787932 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_1787932 : Nat := 118140960795 + 1787932 * 2 ^ 59
def prefixEnd_1787932 : Nat := 4983230072969 + 3 ^ 40 * 1787932 * 2
def baseEnd_1787932 : Nat := 408030441579823974012203

theorem tailTrace_1787932 : CollatzResearch.WordTrace tailWord_1787932 prefixEnd_1787932 408030441579823974012203 := by
  unfold tailWord_1787932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32605618679317596660099025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43474158239090128880132033 32605618679317596660099025)
  ·
    refine ⟨24454214009488197495074269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32605618679317596660099025 24454214009488197495074269)
    ·
      refine ⟨9170330253558074060652851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24454214009488197495074269 9170330253558074060652851)
      ·
        refine ⟨13755495380337111090979277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170330253558074060652851 13755495380337111090979277)
        ·
          refine ⟨5158310767626416659117229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13755495380337111090979277 5158310767626416659117229)
          ·
            refine ⟨1934366537859906247168961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5158310767626416659117229 1934366537859906247168961)
            ·
              refine ⟨1450774903394929685376721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934366537859906247168961 1450774903394929685376721)
              ·
                refine ⟨1088081177546197264032541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450774903394929685376721 1088081177546197264032541)
                ·
                  refine ⟨408030441579823974012203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088081177546197264032541 408030441579823974012203)
                  ·
                    rfl

theorem cell21_1787932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_1787932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787932 prefixEnd_1787932 := by exact prefixLift 1787932
  have htrace : WordTrace (prefixWord ++ tailWord_1787932) baseStart_1787932 baseEnd_1787932 := by
    simpa [prefixWord, tailWord_1787932, baseEnd_1787932] using wordTrace_append hprefix tailTrace_1787932
  have hstable : (prefixWord ++ tailWord_1787932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787932).length < 2 ^ (prefixWord ++ tailWord_1787932).sum := by decide
  have hdescent : baseEnd_1787932 < baseStart_1787932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787974 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1787974 : Nat := 118140960795 + 1787974 * 2 ^ 59
def prefixEnd_1787974 : Nat := 4983230072969 + 3 ^ 40 * 1787974 * 2
def baseEnd_1787974 : Nat := 408040026552041234312117

theorem tailTrace_1787974 : CollatzResearch.WordTrace tailWord_1787974 prefixEnd_1787974 408040026552041234312117 := by
  unfold tailWord_1787974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037899038265094827913343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43475179482988689662151317 2037899038265094827913343)
  ·
    refine ⟨3056848557397642241870015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037899038265094827913343 3056848557397642241870015)
    ·
      refine ⟨4585272836096463362805023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056848557397642241870015 4585272836096463362805023)
      ·
        refine ⟨6877909254144695044207535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585272836096463362805023 6877909254144695044207535)
        ·
          refine ⟨10316863881217042566311303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877909254144695044207535 10316863881217042566311303)
          ·
            refine ⟨15475295821825563849466955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316863881217042566311303 15475295821825563849466955)
            ·
              refine ⟨23212943732738345774200433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475295821825563849466955 23212943732738345774200433)
              ·
                refine ⟨17409707799553759330650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23212943732738345774200433 17409707799553759330650325)
                ·
                  refine ⟨408040026552041234312117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17409707799553759330650325 408040026552041234312117)
                  ·
                    rfl

theorem cell21_1787974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1787974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1787974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1787974 prefixEnd_1787974 := by exact prefixLift 1787974
  have htrace : WordTrace (prefixWord ++ tailWord_1787974) baseStart_1787974 baseEnd_1787974 := by
    simpa [prefixWord, tailWord_1787974, baseEnd_1787974] using wordTrace_append hprefix tailTrace_1787974
  have hstable : (prefixWord ++ tailWord_1787974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787974).length < 2 ^ (prefixWord ++ tailWord_1787974).sum := by decide
  have hdescent : baseEnd_1787974 < baseStart_1787974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788005 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1788005 : Nat := 118140960795 + 1788005 * 2 ^ 59
def prefixEnd_1788005 : Nat := 4983230072969 + 3 ^ 40 * 1788005 * 2
def baseEnd_1788005 : Nat := 408047101174392069295387

theorem tailTrace_1788005 : CollatzResearch.WordTrace tailWord_1788005 prefixEnd_1788005 408047101174392069295387 := by
  unfold tailWord_1788005
  simp only [CollatzResearch.WordTrace]
  refine ⟨65213899887370726787605469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43475933258247151191736979 65213899887370726787605469)
  ·
    refine ⟨24455212457764022545352051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65213899887370726787605469 24455212457764022545352051)
    ·
      refine ⟨36682818686646033818028077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24455212457764022545352051 36682818686646033818028077)
      ·
        refine ⟨13756057007492262681760529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36682818686646033818028077 13756057007492262681760529)
        ·
          refine ⟨10317042755619197011320397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13756057007492262681760529 10317042755619197011320397)
          ·
            refine ⟨3868891033357198879245149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10317042755619197011320397 3868891033357198879245149)
            ·
              refine ⟨1450834137508949579716931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3868891033357198879245149 1450834137508949579716931)
              ·
                refine ⟨2176251206263424369575397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450834137508949579716931 2176251206263424369575397)
                ·
                  refine ⟨408047101174392069295387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176251206263424369575397 408047101174392069295387)
                  ·
                    rfl

theorem cell21_1788005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1788005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788005 prefixEnd_1788005 := by exact prefixLift 1788005
  have htrace : WordTrace (prefixWord ++ tailWord_1788005) baseStart_1788005 baseEnd_1788005 := by
    simpa [prefixWord, tailWord_1788005, baseEnd_1788005] using wordTrace_append hprefix tailTrace_1788005
  have hstable : (prefixWord ++ tailWord_1788005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788005).length < 2 ^ (prefixWord ++ tailWord_1788005).sum := by decide
  have hdescent : baseEnd_1788005 < baseStart_1788005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788064 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_1788064 : Nat := 118140960795 + 1788064 * 2 ^ 59
def prefixEnd_1788064 : Nat := 4983230072969 + 3 ^ 40 * 1788064 * 2
def baseEnd_1788064 : Nat := 408060565778221077811933

theorem tailTrace_1788064 : CollatzResearch.WordTrace tailWord_1788064 prefixEnd_1788064 408060565778221077811933 := by
  unfold tailWord_1788064
  simp only [CollatzResearch.WordTrace]
  refine ⟨32608025897078489932001623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43477367862771319909335497 32608025897078489932001623)
  ·
    refine ⟨48912038845617734898002435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32608025897078489932001623 48912038845617734898002435)
    ·
      refine ⟨73368058268426602347003653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48912038845617734898002435 73368058268426602347003653)
      ·
        refine ⟨13756510925329987940063185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73368058268426602347003653 13756510925329987940063185)
        ·
          refine ⟨10317383193997490955047389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13756510925329987940063185 10317383193997490955047389)
          ·
            refine ⟨3869018697749059108142771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10317383193997490955047389 3869018697749059108142771)
            ·
              refine ⟨5803528046623588662214157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869018697749059108142771 5803528046623588662214157)
              ·
                refine ⟨2176323017483845748330309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5803528046623588662214157 2176323017483845748330309)
                ·
                  refine ⟨408060565778221077811933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176323017483845748330309 408060565778221077811933)
                  ·
                    rfl

theorem cell21_1788064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_1788064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788064 prefixEnd_1788064 := by exact prefixLift 1788064
  have htrace : WordTrace (prefixWord ++ tailWord_1788064) baseStart_1788064 baseEnd_1788064 := by
    simpa [prefixWord, tailWord_1788064, baseEnd_1788064] using wordTrace_append hprefix tailTrace_1788064
  have hstable : (prefixWord ++ tailWord_1788064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788064).length < 2 ^ (prefixWord ++ tailWord_1788064).sum := by decide
  have hdescent : baseEnd_1788064 < baseStart_1788064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788098 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1788098 : Nat := 118140960795 + 1788098 * 2 ^ 59
def prefixEnd_1788098 : Nat := 4983230072969 + 3 ^ 40 * 1788098 * 2
def baseEnd_1788098 : Nat := 408068325041444574245197

theorem tailTrace_1788098 : CollatzResearch.WordTrace tailWord_1788098 prefixEnd_1788098 408068325041444574245197 := by
  unfold tailWord_1788098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304322969008450917685237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43478194584022535780493965 16304322969008450917685237)
  ·
    refine ⟨1528530278344542273532991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16304322969008450917685237 1528530278344542273532991)
    ·
      refine ⟨2292795417516813410299487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528530278344542273532991 2292795417516813410299487)
      ·
        refine ⟨3439193126275220115449231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292795417516813410299487 3439193126275220115449231)
        ·
          refine ⟨5158789689412830173173847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439193126275220115449231 5158789689412830173173847)
          ·
            refine ⟨7738184534119245259760771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158789689412830173173847 7738184534119245259760771)
            ·
              refine ⟨11607276801178867889641157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738184534119245259760771 11607276801178867889641157)
              ·
                refine ⟨2176364400221037729307717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11607276801178867889641157 2176364400221037729307717)
                ·
                  refine ⟨408068325041444574245197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176364400221037729307717 408068325041444574245197)
                  ·
                    rfl

theorem cell21_1788098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1788098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788098 prefixEnd_1788098 := by exact prefixLift 1788098
  have htrace : WordTrace (prefixWord ++ tailWord_1788098) baseStart_1788098 baseEnd_1788098 := by
    simpa [prefixWord, tailWord_1788098, baseEnd_1788098] using wordTrace_append hprefix tailTrace_1788098
  have hstable : (prefixWord ++ tailWord_1788098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788098).length < 2 ^ (prefixWord ++ tailWord_1788098).sum := by decide
  have hdescent : baseEnd_1788098 < baseStart_1788098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788337 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_1788337 : Nat := 118140960795 + 1788337 * 2 ^ 59
def prefixEnd_1788337 : Nat := 4983230072969 + 3 ^ 40 * 1788337 * 2
def baseEnd_1788337 : Nat := 408122868097633269761375

theorem tailTrace_1788337 : CollatzResearch.WordTrace tailWord_1788337 prefixEnd_1788337 408122868097633269761375 := by
  unfold tailWord_1788337
  simp only [CollatzResearch.WordTrace]
  refine ⟨65226008922167947488691265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43484005948111964992460843 65226008922167947488691265)
  ·
    refine ⟨48919506691625960616518449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65226008922167947488691265 48919506691625960616518449)
    ·
      refine ⟨36689630018719470462388837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48919506691625960616518449 36689630018719470462388837)
      ·
        refine ⟨6879305628509900711697907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36689630018719470462388837 6879305628509900711697907)
        ·
          refine ⟨10318958442764851067546861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879305628509900711697907 10318958442764851067546861)
          ·
            refine ⟨3869609416036819150330073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10318958442764851067546861 3869609416036819150330073)
            ·
              refine ⟨2902207062027614362747555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869609416036819150330073 2902207062027614362747555)
              ·
                refine ⟨4353310593041421544121333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902207062027614362747555 4353310593041421544121333)
                ·
                  refine ⟨408122868097633269761375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4353310593041421544121333 408122868097633269761375)
                  ·
                    rfl

theorem cell21_1788337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_1788337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788337 prefixEnd_1788337 := by exact prefixLift 1788337
  have htrace : WordTrace (prefixWord ++ tailWord_1788337) baseStart_1788337 baseEnd_1788337 := by
    simpa [prefixWord, tailWord_1788337, baseEnd_1788337] using wordTrace_append hprefix tailTrace_1788337
  have hstable : (prefixWord ++ tailWord_1788337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788337).length < 2 ^ (prefixWord ++ tailWord_1788337).sum := by decide
  have hdescent : baseEnd_1788337 < baseStart_1788337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788402 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1788402 : Nat := 118140960795 + 1788402 * 2 ^ 59
def prefixEnd_1788402 : Nat := 4983230072969 + 3 ^ 40 * 1788402 * 2
def baseEnd_1788402 : Nat := 408137701983207601177909

theorem tailTrace_1788402 : CollatzResearch.WordTrace tailWord_1788402 prefixEnd_1788402 408137701983207601177909 := by
  unfold tailWord_1788402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307094916733115897451865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43485586444621642393204973 16307094916733115897451865)
  ·
    refine ⟨12230321187549836923088899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16307094916733115897451865 12230321187549836923088899)
    ·
      refine ⟨18345481781324755384633349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12230321187549836923088899 18345481781324755384633349)
      ·
        refine ⟨3439777833998391634618753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18345481781324755384633349 3439777833998391634618753)
        ·
          refine ⟨2579833375498793725964065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439777833998391634618753 2579833375498793725964065)
          ·
            refine ⟨1934875031624095294473049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579833375498793725964065 1934875031624095294473049)
            ·
              refine ⟨1451156273718071470854787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934875031624095294473049 1451156273718071470854787)
              ·
                refine ⟨2176734410577107206282181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451156273718071470854787 2176734410577107206282181)
                ·
                  refine ⟨408137701983207601177909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176734410577107206282181 408137701983207601177909)
                  ·
                    rfl

theorem cell21_1788402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1788402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788402 prefixEnd_1788402 := by exact prefixLift 1788402
  have htrace : WordTrace (prefixWord ++ tailWord_1788402) baseStart_1788402 baseEnd_1788402 := by
    simpa [prefixWord, tailWord_1788402, baseEnd_1788402] using wordTrace_append hprefix tailTrace_1788402
  have hstable : (prefixWord ++ tailWord_1788402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788402).length < 2 ^ (prefixWord ++ tailWord_1788402).sum := by decide
  have hdescent : baseEnd_1788402 < baseStart_1788402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788410 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_1788410 : Nat := 118140960795 + 1788410 * 2 ^ 59
def prefixEnd_1788410 : Nat := 4983230072969 + 3 ^ 40 * 1788410 * 2
def baseEnd_1788410 : Nat := 408139527692201365044559

theorem tailTrace_1788410 : CollatzResearch.WordTrace tailWord_1788410 prefixEnd_1788410 408139527692201365044559 := by
  unfold tailWord_1788410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307167862725870239024671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43485780967268987304065789 16307167862725870239024671)
  ·
    refine ⟨24460751794088805358537007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16307167862725870239024671 24460751794088805358537007)
    ·
      refine ⟨36691127691133208037805511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24460751794088805358537007 36691127691133208037805511)
      ·
        refine ⟨55036691536699812056708267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36691127691133208037805511 55036691536699812056708267)
        ·
          refine ⟨82555037305049718085062401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55036691536699812056708267 82555037305049718085062401)
          ·
            refine ⟨61916277978787288563796801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82555037305049718085062401 61916277978787288563796801)
            ·
              refine ⟨46437208484090466422847601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61916277978787288563796801 46437208484090466422847601)
              ·
                refine ⟨34827906363067849817135701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46437208484090466422847601 34827906363067849817135701)
                ·
                  refine ⟨408139527692201365044559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34827906363067849817135701 408139527692201365044559)
                  ·
                    rfl

theorem cell21_1788410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_1788410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788410 prefixEnd_1788410 := by exact prefixLift 1788410
  have htrace : WordTrace (prefixWord ++ tailWord_1788410) baseStart_1788410 baseEnd_1788410 := by
    simpa [prefixWord, tailWord_1788410, baseEnd_1788410] using wordTrace_append hprefix tailTrace_1788410
  have hstable : (prefixWord ++ tailWord_1788410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788410).length < 2 ^ (prefixWord ++ tailWord_1788410).sum := by decide
  have hdescent : baseEnd_1788410 < baseStart_1788410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788444 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_1788444 : Nat := 118140960795 + 1788444 * 2 ^ 59
def prefixEnd_1788444 : Nat := 4983230072969 + 3 ^ 40 * 1788444 * 2
def baseEnd_1788444 : Nat := 408147286955424861477823

theorem tailTrace_1788444 : CollatzResearch.WordTrace tailWord_1788444 prefixEnd_1788444 408147286955424861477823 := by
  unfold tailWord_1788444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32614955766390152381418193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43486607688520203175224257 32614955766390152381418193)
  ·
    refine ⟨24461216824792614286063645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32614955766390152381418193 24461216824792614286063645)
    ·
      refine ⟨9172956309297230357273867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24461216824792614286063645 9172956309297230357273867)
      ·
        refine ⟨13759434463945845535910801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172956309297230357273867 13759434463945845535910801)
        ·
          refine ⟨10319575847959384151933101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13759434463945845535910801 10319575847959384151933101)
          ·
            refine ⟨3869840942984769056974913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10319575847959384151933101 3869840942984769056974913)
            ·
              refine ⟨2902380707238576792731185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869840942984769056974913 2902380707238576792731185)
              ·
                refine ⟨2176785530428932594548389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902380707238576792731185 2176785530428932594548389)
                ·
                  refine ⟨408147286955424861477823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176785530428932594548389 408147286955424861477823)
                  ·
                    rfl

theorem cell21_1788444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_1788444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788444 prefixEnd_1788444 := by exact prefixLift 1788444
  have htrace : WordTrace (prefixWord ++ tailWord_1788444) baseStart_1788444 baseEnd_1788444 := by
    simpa [prefixWord, tailWord_1788444, baseEnd_1788444] using wordTrace_append hprefix tailTrace_1788444
  have hstable : (prefixWord ++ tailWord_1788444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788444).length < 2 ^ (prefixWord ++ tailWord_1788444).sum := by decide
  have hdescent : baseEnd_1788444 < baseStart_1788444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788458 : List Nat := [3, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1788458 : Nat := 118140960795 + 1788458 * 2 ^ 59
def prefixEnd_1788458 : Nat := 4983230072969 + 3 ^ 40 * 1788458 * 2
def baseEnd_1788458 : Nat := 136050160648721316081487

theorem tailTrace_1788458 : CollatzResearch.WordTrace tailWord_1788458 prefixEnd_1788458 136050160648721316081487 := by
  unfold tailWord_1788458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307605538682396288461507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43486948103153056769230685 16307605538682396288461507)
  ·
    refine ⟨24461408308023594432692261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16307605538682396288461507 24461408308023594432692261)
    ·
      refine ⟨4586514057754423956129799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24461408308023594432692261 4586514057754423956129799)
      ·
        refine ⟨6879771086631635934194699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586514057754423956129799 6879771086631635934194699)
        ·
          refine ⟨10319656629947453901292049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879771086631635934194699 10319656629947453901292049)
          ·
            refine ⟨7739742472460590425969037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10319656629947453901292049 7739742472460590425969037)
            ·
              refine ⟨2902403427172721409738389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7739742472460590425969037 2902403427172721409738389)
              ·
                refine ⟨136050160648721316081487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2902403427172721409738389 136050160648721316081487)
                ·
                  rfl

theorem cell21_1788458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1788458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788458 prefixEnd_1788458 := by exact prefixLift 1788458
  have htrace : WordTrace (prefixWord ++ tailWord_1788458) baseStart_1788458 baseEnd_1788458 := by
    simpa [prefixWord, tailWord_1788458, baseEnd_1788458] using wordTrace_append hprefix tailTrace_1788458
  have hstable : (prefixWord ++ tailWord_1788458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788458).length < 2 ^ (prefixWord ++ tailWord_1788458).sum := by decide
  have hdescent : baseEnd_1788458 < baseStart_1788458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788472 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_1788472 : Nat := 118140960795 + 1788472 * 2 ^ 59
def prefixEnd_1788472 : Nat := 4983230072969 + 3 ^ 40 * 1788472 * 2
def baseEnd_1788472 : Nat := 408153676936903035011099

theorem tailTrace_1788472 : CollatzResearch.WordTrace tailWord_1788472 prefixEnd_1788472 408153676936903035011099 := by
  unfold tailWord_1788472
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615466388339432772427835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43487288517785910363237113 32615466388339432772427835)
  ·
    refine ⟨48923199582509149158641753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32615466388339432772427835 48923199582509149158641753)
    ·
      refine ⟨36692399686881861868981315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48923199582509149158641753 36692399686881861868981315)
      ·
        refine ⟨55038599530322792803471973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36692399686881861868981315 55038599530322792803471973)
        ·
          refine ⟨10319737411935523650650995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55038599530322792803471973 10319737411935523650650995)
          ·
            refine ⟨15479606117903285475976493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319737411935523650650995 15479606117903285475976493)
            ·
              refine ⟨5804852294213732053491185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15479606117903285475976493 5804852294213732053491185)
              ·
                refine ⟨4353639220660299040118389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5804852294213732053491185 4353639220660299040118389)
                ·
                  refine ⟨408153676936903035011099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4353639220660299040118389 408153676936903035011099)
                  ·
                    rfl

theorem cell21_1788472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_1788472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788472 prefixEnd_1788472 := by exact prefixLift 1788472
  have htrace : WordTrace (prefixWord ++ tailWord_1788472) baseStart_1788472 baseEnd_1788472 := by
    simpa [prefixWord, tailWord_1788472, baseEnd_1788472] using wordTrace_append hprefix tailTrace_1788472
  have hstable : (prefixWord ++ tailWord_1788472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788472).length < 2 ^ (prefixWord ++ tailWord_1788472).sum := by decide
  have hdescent : baseEnd_1788472 < baseStart_1788472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788531 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_1788531 : Nat := 118140960795 + 1788531 * 2 ^ 59
def prefixEnd_1788531 : Nat := 4983230072969 + 3 ^ 40 * 1788531 * 2
def baseEnd_1788531 : Nat := 408167141540732043527645

theorem tailTrace_1788531 : CollatzResearch.WordTrace tailWord_1788531 prefixEnd_1788531 408167141540732043527645 := by
  unfold tailWord_1788531
  simp only [CollatzResearch.WordTrace]
  refine ⟨65233084683465118621253447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43488723122310079080835631 65233084683465118621253447)
  ·
    refine ⟨97849627025197677931880171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65233084683465118621253447 97849627025197677931880171)
    ·
      refine ⟨146774440537796516897820257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97849627025197677931880171 146774440537796516897820257)
      ·
        refine ⟨110080830403347387673365193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146774440537796516897820257 110080830403347387673365193)
        ·
          refine ⟨82560622802510540755023895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110080830403347387673365193 82560622802510540755023895)
          ·
            refine ⟨123840934203765811132535843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82560622802510540755023895 123840934203765811132535843)
            ·
              refine ⟨185761401305648716698803765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123840934203765811132535843 185761401305648716698803765)
              ·
                refine ⟨17415131372404567190512853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185761401305648716698803765 17415131372404567190512853)
                ·
                  refine ⟨408167141540732043527645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17415131372404567190512853 408167141540732043527645)
                  ·
                    rfl

theorem cell21_1788531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_1788531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788531 prefixEnd_1788531 := by exact prefixLift 1788531
  have htrace : WordTrace (prefixWord ++ tailWord_1788531) baseStart_1788531 baseEnd_1788531 := by
    simpa [prefixWord, tailWord_1788531, baseEnd_1788531] using wordTrace_append hprefix tailTrace_1788531
  have hstable : (prefixWord ++ tailWord_1788531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788531).length < 2 ^ (prefixWord ++ tailWord_1788531).sum := by decide
  have hdescent : baseEnd_1788531 < baseStart_1788531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788610 : List Nat := [3, 5, 1, 12]
def baseStart_1788610 : Nat := 118140960795 + 1788610 * 2 ^ 59
def prefixEnd_1788610 : Nat := 4983230072969 + 3 ^ 40 * 1788610 * 2
def baseEnd_1788610 : Nat := 1679774363856154163419

theorem tailTrace_1788610 : CollatzResearch.WordTrace tailWord_1788610 prefixEnd_1788610 1679774363856154163419 := by
  unfold tailWord_1788610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308991512544728778344821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43490644033452610075586189 16308991512544728778344821)
  ·
    refine ⟨1528967954301068322969827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16308991512544728778344821 1528967954301068322969827)
    ·
      refine ⟨2293451931451602484454741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528967954301068322969827 2293451931451602484454741)
      ·
        refine ⟨1679774363856154163419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2293451931451602484454741 1679774363856154163419)
        ·
          rfl

theorem cell21_1788610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 12].length) (baseStart_1788610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788610 prefixEnd_1788610 := by exact prefixLift 1788610
  have htrace : WordTrace (prefixWord ++ tailWord_1788610) baseStart_1788610 baseEnd_1788610 := by
    simpa [prefixWord, tailWord_1788610, baseEnd_1788610] using wordTrace_append hprefix tailTrace_1788610
  have hstable : (prefixWord ++ tailWord_1788610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788610).length < 2 ^ (prefixWord ++ tailWord_1788610).sum := by decide
  have hdescent : baseEnd_1788610 < baseStart_1788610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788658 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1788658 : Nat := 118140960795 + 1788658 * 2 ^ 59
def prefixEnd_1788658 : Nat := 4983230072969 + 3 ^ 40 * 1788658 * 2
def baseEnd_1788658 : Nat := 408196124671008044910719

theorem tailTrace_1788658 : CollatzResearch.WordTrace tailWord_1788658 prefixEnd_1788658 408196124671008044910719 := by
  unfold tailWord_1788658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309429188501254827781657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43491811169336679540751085 16309429188501254827781657)
  ·
    refine ⟨12232071891375941120836243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16309429188501254827781657 12232071891375941120836243)
    ·
      refine ⟨18348107837063911681254365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12232071891375941120836243 18348107837063911681254365)
      ·
        refine ⟨6880540438898966880470387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18348107837063911681254365 6880540438898966880470387)
        ·
          refine ⟨10320810658348450320705581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880540438898966880470387 10320810658348450320705581)
          ·
            refine ⟨3870303996880668870264593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10320810658348450320705581 3870303996880668870264593)
            ·
              refine ⟨2902727997660501652698445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870303996880668870264593 2902727997660501652698445)
              ·
                refine ⟨1088522999122688119761917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2902727997660501652698445 1088522999122688119761917)
                ·
                  refine ⟨408196124671008044910719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088522999122688119761917 408196124671008044910719)
                  ·
                    rfl

theorem cell21_1788658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1788658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788658 prefixEnd_1788658 := by exact prefixLift 1788658
  have htrace : WordTrace (prefixWord ++ tailWord_1788658) baseStart_1788658 baseEnd_1788658 := by
    simpa [prefixWord, tailWord_1788658, baseEnd_1788658] using wordTrace_append hprefix tailTrace_1788658
  have hstable : (prefixWord ++ tailWord_1788658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788658).length < 2 ^ (prefixWord ++ tailWord_1788658).sum := by decide
  have hdescent : baseEnd_1788658 < baseStart_1788658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788700 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1788700 : Nat := 118140960795 + 1788700 * 2 ^ 59
def prefixEnd_1788700 : Nat := 4983230072969 + 3 ^ 40 * 1788700 * 2
def baseEnd_1788700 : Nat := 408205709643225305210633

theorem tailTrace_1788700 : CollatzResearch.WordTrace tailWord_1788700 prefixEnd_1788700 408205709643225305210633 := by
  unfold tailWord_1788700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619624309926430242077777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43492832413235240322770369 32619624309926430242077777)
  ·
    refine ⟨24464718232444822681558333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32619624309926430242077777 24464718232444822681558333)
    ·
      refine ⟨9174269337166808505584375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24464718232444822681558333 9174269337166808505584375)
      ·
        refine ⟨13761404005750212758376563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174269337166808505584375 13761404005750212758376563)
        ·
          refine ⟨20642106008625319137564845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761404005750212758376563 20642106008625319137564845)
          ·
            refine ⟨7740789753234494676586817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20642106008625319137564845 7740789753234494676586817)
            ·
              refine ⟨5805592314925871007440113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740789753234494676586817 5805592314925871007440113)
              ·
                refine ⟨4354194236194403255580085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805592314925871007440113 4354194236194403255580085)
                ·
                  refine ⟨408205709643225305210633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4354194236194403255580085 408205709643225305210633)
                  ·
                    rfl

theorem cell21_1788700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1788700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788700 prefixEnd_1788700 := by exact prefixLift 1788700
  have htrace : WordTrace (prefixWord ++ tailWord_1788700) baseStart_1788700 baseEnd_1788700 := by
    simpa [prefixWord, tailWord_1788700, baseEnd_1788700] using wordTrace_append hprefix tailTrace_1788700
  have hstable : (prefixWord ++ tailWord_1788700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788700).length < 2 ^ (prefixWord ++ tailWord_1788700).sum := by decide
  have hdescent : baseEnd_1788700 < baseStart_1788700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788734 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1788734 : Nat := 118140960795 + 1788734 * 2 ^ 59
def prefixEnd_1788734 : Nat := 4983230072969 + 3 ^ 40 * 1788734 * 2
def baseEnd_1788734 : Nat := 408213468906448801643897

theorem tailTrace_1788734 : CollatzResearch.WordTrace tailWord_1788734 prefixEnd_1788734 408213468906448801643897 := by
  unfold tailWord_1788734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155061087716210536361657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43493659134486456193928837 8155061087716210536361657)
  ·
    refine ⟨6116295815787157902271243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8155061087716210536361657 6116295815787157902271243)
    ·
      refine ⟨9174443723680736853406865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116295815787157902271243 9174443723680736853406865)
      ·
        refine ⟨6880832792760552640055149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9174443723680736853406865 6880832792760552640055149)
        ·
          refine ⟨2580312297285207240020681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6880832792760552640055149 2580312297285207240020681)
          ·
            refine ⟨1935234222963905430015511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580312297285207240020681 1935234222963905430015511)
            ·
              refine ⟨2902851334445858145023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935234222963905430015511 2902851334445858145023267)
              ·
                refine ⟨4354277001668787217534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902851334445858145023267 4354277001668787217534901)
                ·
                  refine ⟨408213468906448801643897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4354277001668787217534901 408213468906448801643897)
                  ·
                    rfl

theorem cell21_1788734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1788734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788734 prefixEnd_1788734 := by exact prefixLift 1788734
  have htrace : WordTrace (prefixWord ++ tailWord_1788734) baseStart_1788734 baseEnd_1788734 := by
    simpa [prefixWord, tailWord_1788734, baseEnd_1788734] using wordTrace_append hprefix tailTrace_1788734
  have hstable : (prefixWord ++ tailWord_1788734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788734).length < 2 ^ (prefixWord ++ tailWord_1788734).sum := by decide
  have hdescent : baseEnd_1788734 < baseStart_1788734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788745 : List Nat := [1, 2, 1, 1, 2, 6, 2, 6]
def baseStart_1788745 : Nat := 118140960795 + 1788745 * 2 ^ 59
def prefixEnd_1788745 : Nat := 4983230072969 + 3 ^ 40 * 1788745 * 2
def baseEnd_1788745 : Nat := 136071993085438408986847

theorem tailTrace_1788745 : CollatzResearch.WordTrace tailWord_1788745 prefixEnd_1788745 136071993085438408986847 := by
  unfold tailWord_1788745
  simp only [CollatzResearch.WordTrace]
  refine ⟨65240889904689833169543689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43493926603126555446362459 65240889904689833169543689)
  ·
    refine ⟨48930667428517374877157767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65240889904689833169543689 48930667428517374877157767)
    ·
      refine ⟨73396001142776062315736651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48930667428517374877157767 73396001142776062315736651)
      ·
        refine ⟨110094001714164093473604977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73396001142776062315736651 110094001714164093473604977)
        ·
          refine ⟨82570501285623070105203733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110094001714164093473604977 82570501285623070105203733)
          ·
            refine ⟨3870492247763581411181425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82570501285623070105203733 3870492247763581411181425)
            ·
              refine ⟨2902869185822686058386069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870492247763581411181425 2902869185822686058386069)
              ·
                refine ⟨136071993085438408986847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2902869185822686058386069 136071993085438408986847)
                ·
                  rfl

theorem cell21_1788745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_1788745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788745 prefixEnd_1788745 := by exact prefixLift 1788745
  have htrace : WordTrace (prefixWord ++ tailWord_1788745) baseStart_1788745 baseEnd_1788745 := by
    simpa [prefixWord, tailWord_1788745, baseEnd_1788745] using wordTrace_append hprefix tailTrace_1788745
  have hstable : (prefixWord ++ tailWord_1788745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788745).length < 2 ^ (prefixWord ++ tailWord_1788745).sum := by decide
  have hdescent : baseEnd_1788745 < baseStart_1788745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788748 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_1788748 : Nat := 118140960795 + 1788748 * 2 ^ 59
def prefixEnd_1788748 : Nat := 4983230072969 + 3 ^ 40 * 1788748 * 2
def baseEnd_1788748 : Nat := 408216663897187888410535

theorem tailTrace_1788748 : CollatzResearch.WordTrace tailWord_1788748 prefixEnd_1788748 408216663897187888410535 := by
  unfold tailWord_1788748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32620499661839482340951449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43493999549119309787935265 32620499661839482340951449)
  ·
    refine ⟨24465374746379611755713587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32620499661839482340951449 24465374746379611755713587)
    ·
      refine ⟨36698062119569417633570381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24465374746379611755713587 36698062119569417633570381)
      ·
        refine ⟨13761773294838531612588893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36698062119569417633570381 13761773294838531612588893)
        ·
          refine ⟨5160664985564449354720835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13761773294838531612588893 5160664985564449354720835)
          ·
            refine ⟨7740997478346674032081253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160664985564449354720835 7740997478346674032081253)
            ·
              refine ⟨1451437027190001381015235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7740997478346674032081253 1451437027190001381015235)
              ·
                refine ⟨2177155540785002071522853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451437027190001381015235 2177155540785002071522853)
                ·
                  refine ⟨408216663897187888410535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177155540785002071522853 408216663897187888410535)
                  ·
                    rfl

theorem cell21_1788748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_1788748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788748 prefixEnd_1788748 := by exact prefixLift 1788748
  have htrace : WordTrace (prefixWord ++ tailWord_1788748) baseStart_1788748 baseEnd_1788748 := by
    simpa [prefixWord, tailWord_1788748, baseEnd_1788748] using wordTrace_append hprefix tailTrace_1788748
  have hstable : (prefixWord ++ tailWord_1788748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788748).length < 2 ^ (prefixWord ++ tailWord_1788748).sum := by decide
  have hdescent : baseEnd_1788748 < baseStart_1788748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788793 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 3]
def baseStart_1788793 : Nat := 118140960795 + 1788793 * 2 ^ 59
def prefixEnd_1788793 : Nat := 4983230072969 + 3 ^ 40 * 1788793 * 2
def baseEnd_1788793 : Nat := 408226933510277810160443

theorem tailTrace_1788793 : CollatzResearch.WordTrace tailWord_1788793 prefixEnd_1788793 408226933510277810160443 := by
  unfold tailWord_1788793
  simp only [CollatzResearch.WordTrace]
  refine ⟨65242640608515937367291033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43495093739010624911527355 65242640608515937367291033)
  ·
    refine ⟨48931980456386953025468275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65242640608515937367291033 48931980456386953025468275)
    ·
      refine ⟨73397970684580429538202413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48931980456386953025468275 73397970684580429538202413)
      ·
        refine ⟨27524239006717661076825905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73397970684580429538202413 27524239006717661076825905)
        ·
          refine ⟨20643179255038245807619429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27524239006717661076825905 20643179255038245807619429)
          ·
            refine ⟨3870596110319671088928643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20643179255038245807619429 3870596110319671088928643)
            ·
              refine ⟨5805894165479506633392965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870596110319671088928643 5805894165479506633392965)
              ·
                refine ⟨1088605156027407493761181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5805894165479506633392965 1088605156027407493761181)
                ·
                  refine ⟨408226933510277810160443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088605156027407493761181 408226933510277810160443)
                  ·
                    rfl

theorem cell21_1788793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_1788793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788793 prefixEnd_1788793 := by exact prefixLift 1788793
  have htrace : WordTrace (prefixWord ++ tailWord_1788793) baseStart_1788793 baseEnd_1788793 := by
    simpa [prefixWord, tailWord_1788793, baseEnd_1788793] using wordTrace_append hprefix tailTrace_1788793
  have hstable : (prefixWord ++ tailWord_1788793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788793).length < 2 ^ (prefixWord ++ tailWord_1788793).sum := by decide
  have hdescent : baseEnd_1788793 < baseStart_1788793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788807 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_1788807 : Nat := 118140960795 + 1788807 * 2 ^ 59
def prefixEnd_1788807 : Nat := 4983230072969 + 3 ^ 40 * 1788807 * 2
def baseEnd_1788807 : Nat := 408230128501016896927081

theorem tailTrace_1788807 : CollatzResearch.WordTrace tailWord_1788807 prefixEnd_1788807 408230128501016896927081 := by
  unfold tailWord_1788807
  simp only [CollatzResearch.WordTrace]
  refine ⟨65243151230465217758300675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43495434153643478505533783 65243151230465217758300675)
  ·
    refine ⟨97864726845697826637451013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65243151230465217758300675 97864726845697826637451013)
    ·
      refine ⟨18349636283568342494522065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97864726845697826637451013 18349636283568342494522065)
      ·
        refine ⟨13762227212676256870891549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18349636283568342494522065 13762227212676256870891549)
        ·
          refine ⟨5160835204753596326584331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13762227212676256870891549 5160835204753596326584331)
          ·
            refine ⟨7741252807130394489876497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160835204753596326584331 7741252807130394489876497)
            ·
              refine ⟨5805939605347795867407373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741252807130394489876497 5805939605347795867407373)
              ·
                refine ⟨2177227352005423450277765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5805939605347795867407373 2177227352005423450277765)
                ·
                  refine ⟨408230128501016896927081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177227352005423450277765 408230128501016896927081)
                  ·
                    rfl

theorem cell21_1788807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_1788807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788807 prefixEnd_1788807 := by exact prefixLift 1788807
  have htrace : WordTrace (prefixWord ++ tailWord_1788807) baseStart_1788807 baseEnd_1788807 := by
    simpa [prefixWord, tailWord_1788807, baseEnd_1788807] using wordTrace_append hprefix tailTrace_1788807
  have hstable : (prefixWord ++ tailWord_1788807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788807).length < 2 ^ (prefixWord ++ tailWord_1788807).sum := by decide
  have hdescent : baseEnd_1788807 < baseStart_1788807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788917 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1788917 : Nat := 118140960795 + 1788917 * 2 ^ 59
def prefixEnd_1788917 : Nat := 4983230072969 + 3 ^ 40 * 1788917 * 2
def baseEnd_1788917 : Nat := 408255231999681150093523

theorem tailTrace_1788917 : CollatzResearch.WordTrace tailWord_1788917 prefixEnd_1788917 408255231999681150093523 := by
  unfold tailWord_1788917
  simp only [CollatzResearch.WordTrace]
  refine ⟨65247163260066706544805005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43498108840044471029870003 65247163260066706544805005)
  ·
    refine ⟨24467686222525014954301877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65247163260066706544805005 24467686222525014954301877)
    ·
      refine ⟨2293845583361720151965801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24467686222525014954301877 2293845583361720151965801)
      ·
        refine ⟨1720384187521290113974351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2293845583361720151965801 1720384187521290113974351)
        ·
          refine ⟨2580576281281935170961527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720384187521290113974351 2580576281281935170961527)
          ·
            refine ⟨3870864421922902756442291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580576281281935170961527 3870864421922902756442291)
            ·
              refine ⟨5806296632884354134663437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870864421922902756442291 5806296632884354134663437)
              ·
                refine ⟨2177361237331632800498789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806296632884354134663437 2177361237331632800498789)
                ·
                  refine ⟨408255231999681150093523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177361237331632800498789 408255231999681150093523)
                  ·
                    rfl

theorem cell21_1788917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1788917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788917 prefixEnd_1788917 := by exact prefixLift 1788917
  have htrace : WordTrace (prefixWord ++ tailWord_1788917) baseStart_1788917 baseEnd_1788917 := by
    simpa [prefixWord, tailWord_1788917, baseEnd_1788917] using wordTrace_append hprefix tailTrace_1788917
  have hstable : (prefixWord ++ tailWord_1788917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788917).length < 2 ^ (prefixWord ++ tailWord_1788917).sum := by decide
  have hdescent : baseEnd_1788917 < baseStart_1788917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788956 : List Nat := [2, 2, 3, 1, 13]
def baseStart_1788956 : Nat := 118140960795 + 1788956 * 2 ^ 59
def prefixEnd_1788956 : Nat := 4983230072969 + 3 ^ 40 * 1788956 * 2
def baseEnd_1788956 : Nat := 5040297930012663567203

theorem tailTrace_1788956 : CollatzResearch.WordTrace tailWord_1788956 prefixEnd_1788956 5040297930012663567203 := by
  unfold tailWord_1788956
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624292853462708102737361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43499057137950277470316481 32624292853462708102737361)
  ·
    refine ⟨24468219640097031077053021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32624292853462708102737361 24468219640097031077053021)
    ·
      refine ⟨9175582365036386653894883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24468219640097031077053021 9175582365036386653894883)
      ·
        refine ⟨13763373547554579980842325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175582365036386653894883 13763373547554579980842325)
        ·
          refine ⟨5040297930012663567203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13763373547554579980842325 5040297930012663567203)
          ·
            rfl

theorem cell21_1788956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 13].length) (baseStart_1788956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788956 prefixEnd_1788956 := by exact prefixLift 1788956
  have htrace : WordTrace (prefixWord ++ tailWord_1788956) baseStart_1788956 baseEnd_1788956 := by
    simpa [prefixWord, tailWord_1788956, baseEnd_1788956] using wordTrace_append hprefix tailTrace_1788956
  have hstable : (prefixWord ++ tailWord_1788956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788956).length < 2 ^ (prefixWord ++ tailWord_1788956).sum := by decide
  have hdescent : baseEnd_1788956 < baseStart_1788956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788959 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_1788959 : Nat := 118140960795 + 1788959 * 2 ^ 59
def prefixEnd_1788959 : Nat := 4983230072969 + 3 ^ 40 * 1788959 * 2
def baseEnd_1788959 : Nat := 408264816971898410393437

theorem tailTrace_1788959 : CollatzResearch.WordTrace tailWord_1788959 prefixEnd_1788959 408264816971898410393437 := by
  unfold tailWord_1788959
  simp only [CollatzResearch.WordTrace]
  refine ⟨65248695125914547717833931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43499130083943031811889287 65248695125914547717833931)
  ·
    refine ⟨97873042688871821576750897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65248695125914547717833931 97873042688871821576750897)
    ·
      refine ⟨73404782016653866182563173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97873042688871821576750897 73404782016653866182563173)
      ·
        refine ⟨13763396628122599909230595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73404782016653866182563173 13763396628122599909230595)
        ·
          refine ⟨20645094942183899863845893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13763396628122599909230595 20645094942183899863845893)
          ·
            refine ⟨3870955301659481224471105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20645094942183899863845893 3870955301659481224471105)
            ·
              refine ⟨2903216476244610918353329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870955301659481224471105 2903216476244610918353329)
              ·
                refine ⟨2177412357183458188764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903216476244610918353329 2177412357183458188764997)
                ·
                  refine ⟨408264816971898410393437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177412357183458188764997 408264816971898410393437)
                  ·
                    rfl

theorem cell21_1788959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_1788959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788959 prefixEnd_1788959 := by exact prefixLift 1788959
  have htrace : WordTrace (prefixWord ++ tailWord_1788959) baseStart_1788959 baseEnd_1788959 := by
    simpa [prefixWord, tailWord_1788959, baseEnd_1788959] using wordTrace_append hprefix tailTrace_1788959
  have hstable : (prefixWord ++ tailWord_1788959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788959).length < 2 ^ (prefixWord ++ tailWord_1788959).sum := by decide
  have hdescent : baseEnd_1788959 < baseStart_1788959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788962 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1788962 : Nat := 118140960795 + 1788962 * 2 ^ 59
def prefixEnd_1788962 : Nat := 4983230072969 + 3 ^ 40 * 1788962 * 2
def baseEnd_1788962 : Nat := 408265501612771071843431

theorem tailTrace_1788962 : CollatzResearch.WordTrace tailWord_1788962 prefixEnd_1788962 408265501612771071843431 := by
  unfold tailWord_1788962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312201136225919807548285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43499203029935786153462093 16312201136225919807548285)
  ·
    refine ⟨6117075426084719927830607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16312201136225919807548285 6117075426084719927830607)
    ·
      refine ⟨9175613139127079891745911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117075426084719927830607 9175613139127079891745911)
      ·
        refine ⟨13763419708690619837618867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175613139127079891745911 13763419708690619837618867)
        ·
          refine ⟨20645129563035929756428301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13763419708690619837618867 20645129563035929756428301)
          ·
            refine ⟨7741923586138473658660613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20645129563035929756428301 7741923586138473658660613)
            ·
              refine ⟨1451610672400963810998865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7741923586138473658660613 1451610672400963810998865)
              ·
                refine ⟨1088708004300722858249149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451610672400963810998865 1088708004300722858249149)
                ·
                  refine ⟨408265501612771071843431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088708004300722858249149 408265501612771071843431)
                  ·
                    rfl

theorem cell21_1788962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1788962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1788962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1788962 prefixEnd_1788962 := by exact prefixLift 1788962
  have htrace : WordTrace (prefixWord ++ tailWord_1788962) baseStart_1788962 baseEnd_1788962 := by
    simpa [prefixWord, tailWord_1788962, baseEnd_1788962] using wordTrace_append hprefix tailTrace_1788962
  have hstable : (prefixWord ++ tailWord_1788962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788962).length < 2 ^ (prefixWord ++ tailWord_1788962).sum := by decide
  have hdescent : baseEnd_1788962 < baseStart_1788962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789018 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1789018 : Nat := 118140960795 + 1789018 * 2 ^ 59
def prefixEnd_1789018 : Nat := 4983230072969 + 3 ^ 40 * 1789018 * 2
def baseEnd_1789018 : Nat := 408278281575727418909983

theorem tailTrace_1789018 : CollatzResearch.WordTrace tailWord_1789018 prefixEnd_1789018 408278281575727418909983 := by
  unfold tailWord_1789018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312711758175200198557927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43500564688467200529487805 16312711758175200198557927)
  ·
    refine ⟨24469067637262800297836891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16312711758175200198557927 24469067637262800297836891)
    ·
      refine ⟨36703601455894200446755337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24469067637262800297836891 36703601455894200446755337)
      ·
        refine ⟨27527701091920650335066503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36703601455894200446755337 27527701091920650335066503)
        ·
          refine ⟨41291551637880975502599755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527701091920650335066503 41291551637880975502599755)
          ·
            refine ⟨61937327456821463253899633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41291551637880975502599755 61937327456821463253899633)
            ·
              refine ⟨46452995592616097440424725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61937327456821463253899633 46452995592616097440424725)
              ·
                refine ⟨2177484168403879567519909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46452995592616097440424725 2177484168403879567519909)
                ·
                  refine ⟨408278281575727418909983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177484168403879567519909 408278281575727418909983)
                  ·
                    rfl

theorem cell21_1789018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1789018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789018 prefixEnd_1789018 := by exact prefixLift 1789018
  have htrace : WordTrace (prefixWord ++ tailWord_1789018) baseStart_1789018 baseEnd_1789018 := by
    simpa [prefixWord, tailWord_1789018, baseEnd_1789018] using wordTrace_append hprefix tailTrace_1789018
  have hstable : (prefixWord ++ tailWord_1789018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789018).length < 2 ^ (prefixWord ++ tailWord_1789018).sum := by decide
  have hdescent : baseEnd_1789018 < baseStart_1789018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789049 : List Nat := [1, 2, 1, 3, 5, 1, 1, 7]
def baseStart_1789049 : Nat := 118140960795 + 1789049 * 2 ^ 59
def prefixEnd_1789049 : Nat := 4983230072969 + 3 ^ 40 * 1789049 * 2
def baseEnd_1789049 : Nat := 136095118732692751297751

theorem tailTrace_1789049 : CollatzResearch.WordTrace tailWord_1789049 prefixEnd_1789049 136095118732692751297751 := by
  unfold tailWord_1789049
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251977695588493088610201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43501318463725662059073467 65251977695588493088610201)
  ·
    refine ⟨48938983271691369816457651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65251977695588493088610201 48938983271691369816457651)
    ·
      refine ⟨73408474907537054724686477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48938983271691369816457651 73408474907537054724686477)
      ·
        refine ⟨27528178090326395521757429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73408474907537054724686477 27528178090326395521757429)
        ·
          refine ⟨2580766695968099580164759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27528178090326395521757429 2580766695968099580164759)
          ·
            refine ⟨3871150043952149370247139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580766695968099580164759 3871150043952149370247139)
            ·
              refine ⟨5806725065928224055370709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871150043952149370247139 5806725065928224055370709)
              ·
                refine ⟨136095118732692751297751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5806725065928224055370709 136095118732692751297751)
                ·
                  rfl

theorem cell21_1789049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_1789049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789049 prefixEnd_1789049 := by exact prefixLift 1789049
  have htrace : WordTrace (prefixWord ++ tailWord_1789049) baseStart_1789049 baseEnd_1789049 := by
    simpa [prefixWord, tailWord_1789049, baseEnd_1789049] using wordTrace_append hprefix tailTrace_1789049
  have hstable : (prefixWord ++ tailWord_1789049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789049).length < 2 ^ (prefixWord ++ tailWord_1789049).sum := by decide
  have hdescent : baseEnd_1789049 < baseStart_1789049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789080 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_1789080 : Nat := 118140960795 + 1789080 * 2 ^ 59
def prefixEnd_1789080 : Nat := 4983230072969 + 3 ^ 40 * 1789080 * 2
def baseEnd_1789080 : Nat := 408292430820429088876523

theorem tailTrace_1789080 : CollatzResearch.WordTrace tailWord_1789080 prefixEnd_1789080 408292430820429088876523 := by
  unfold tailWord_1789080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626554179238092691494347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43502072238984123588659129 32626554179238092691494347)
  ·
    refine ⟨48939831268857139037241521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32626554179238092691494347 48939831268857139037241521)
    ·
      refine ⟨36704873451642854277931141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48939831268857139037241521 36704873451642854277931141)
      ·
        refine ⟨6882163772183035177112089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36704873451642854277931141 6882163772183035177112089)
        ·
          refine ⟨5161622829137276382834067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882163772183035177112089 5161622829137276382834067)
          ·
            refine ⟨7742434243705914574251101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161622829137276382834067 7742434243705914574251101)
            ·
              refine ⟨2903412841389717965344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7742434243705914574251101 2903412841389717965344163)
              ·
                refine ⟨4355119262084576948016245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903412841389717965344163 4355119262084576948016245)
                ·
                  refine ⟨408292430820429088876523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355119262084576948016245 408292430820429088876523)
                  ·
                    rfl

theorem cell21_1789080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_1789080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789080 prefixEnd_1789080 := by exact prefixLift 1789080
  have htrace : WordTrace (prefixWord ++ tailWord_1789080) baseStart_1789080 baseEnd_1789080 := by
    simpa [prefixWord, tailWord_1789080, baseEnd_1789080] using wordTrace_append hprefix tailTrace_1789080
  have hstable : (prefixWord ++ tailWord_1789080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789080).length < 2 ^ (prefixWord ++ tailWord_1789080).sum := by decide
  have hdescent : baseEnd_1789080 < baseStart_1789080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789187 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_1789187 : Nat := 118140960795 + 1789187 * 2 ^ 59
def prefixEnd_1789187 : Nat := 4983230072969 + 3 ^ 40 * 1789187 * 2
def baseEnd_1789187 : Nat := 408316849678220680592971

theorem tailTrace_1789187 : CollatzResearch.WordTrace tailWord_1789187 prefixEnd_1789187 408316849678220680592971 := by
  unfold tailWord_1789187
  simp only [CollatzResearch.WordTrace]
  refine ⟨65257010969088542657133815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43504673979392361771422543 65257010969088542657133815)
  ·
    refine ⟨97885516453632813985700723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65257010969088542657133815 97885516453632813985700723)
    ·
      refine ⟨146828274680449220978551085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97885516453632813985700723 146828274680449220978551085)
      ·
        refine ⟨55060603005168457866956657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146828274680449220978551085 55060603005168457866956657)
        ·
          refine ⟨41295452253876343400217493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55060603005168457866956657 41295452253876343400217493)
          ·
            refine ⟨1935724324400453596885195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41295452253876343400217493 1935724324400453596885195)
            ·
              refine ⟨2903586486600680395327793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935724324400453596885195 2903586486600680395327793)
              ·
                refine ⟨2177689864950510296495845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903586486600680395327793 2177689864950510296495845)
                ·
                  refine ⟨408316849678220680592971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177689864950510296495845 408316849678220680592971)
                  ·
                    rfl

theorem cell21_1789187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_1789187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789187 prefixEnd_1789187 := by exact prefixLift 1789187
  have htrace : WordTrace (prefixWord ++ tailWord_1789187) baseStart_1789187 baseEnd_1789187 := by
    simpa [prefixWord, tailWord_1789187, baseEnd_1789187] using wordTrace_append hprefix tailTrace_1789187
  have hstable : (prefixWord ++ tailWord_1789187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789187).length < 2 ^ (prefixWord ++ tailWord_1789187).sum := by decide
  have hdescent : baseEnd_1789187 < baseStart_1789187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789246 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1789246 : Nat := 118140960795 + 1789246 * 2 ^ 59
def prefixEnd_1789246 : Nat := 4983230072969 + 3 ^ 40 * 1789246 * 2
def baseEnd_1789246 : Nat := 408330314282049689109517

theorem tailTrace_1789246 : CollatzResearch.WordTrace tailWord_1789246 prefixEnd_1789246 408330314282049689109517 := by
  unfold tailWord_1789246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157395359484349466691449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43506108583916530489021061 8157395359484349466691449)
  ·
    refine ⟨6118046519613262100018587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8157395359484349466691449 6118046519613262100018587)
    ·
      refine ⟨9177069779419893150027881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118046519613262100018587 9177069779419893150027881)
      ·
        refine ⟨6882802334564919862520911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9177069779419893150027881 6882802334564919862520911)
        ·
          refine ⟨10324203501847379793781367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882802334564919862520911 10324203501847379793781367)
          ·
            refine ⟨15486305252771069690672051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324203501847379793781367 15486305252771069690672051)
            ·
              refine ⟨23229457879156604536008077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486305252771069690672051 23229457879156604536008077)
              ·
                refine ⟨8711046704683726701003029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23229457879156604536008077 8711046704683726701003029)
                ·
                  refine ⟨408330314282049689109517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8711046704683726701003029 408330314282049689109517)
                  ·
                    rfl

theorem cell21_1789246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1789246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789246 prefixEnd_1789246 := by exact prefixLift 1789246
  have htrace : WordTrace (prefixWord ++ tailWord_1789246) baseStart_1789246 baseEnd_1789246 := by
    simpa [prefixWord, tailWord_1789246, baseEnd_1789246] using wordTrace_append hprefix tailTrace_1789246
  have hstable : (prefixWord ++ tailWord_1789246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789246).length < 2 ^ (prefixWord ++ tailWord_1789246).sum := by decide
  have hdescent : baseEnd_1789246 < baseStart_1789246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789249 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_1789249 : Nat := 118140960795 + 1789249 * 2 ^ 59
def prefixEnd_1789249 : Nat := 4983230072969 + 3 ^ 40 * 1789249 * 2
def baseEnd_1789249 : Nat := 408330998922922350559511

theorem tailTrace_1789249 : CollatzResearch.WordTrace tailWord_1789249 prefixEnd_1789249 408330998922922350559511 := by
  unfold tailWord_1789249
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259272294863927245890801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43506181529909284830593867 65259272294863927245890801)
  ·
    refine ⟨48944454221147945434418101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65259272294863927245890801 48944454221147945434418101)
    ·
      refine ⟨4588542583232619884476697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48944454221147945434418101 4588542583232619884476697)
      ·
        refine ⟨3441406937424464913357523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4588542583232619884476697 3441406937424464913357523)
        ·
          refine ⟨5162110406136697370036285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441406937424464913357523 5162110406136697370036285)
          ·
            refine ⟨1935791402301261513763607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5162110406136697370036285 1935791402301261513763607)
            ·
              refine ⟨2903687103451892270645411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935791402301261513763607 2903687103451892270645411)
              ·
                refine ⟨4355530655177838405968117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903687103451892270645411 4355530655177838405968117)
                ·
                  refine ⟨408330998922922350559511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355530655177838405968117 408330998922922350559511)
                  ·
                    rfl

theorem cell21_1789249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_1789249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789249 prefixEnd_1789249 := by exact prefixLift 1789249
  have htrace : WordTrace (prefixWord ++ tailWord_1789249) baseStart_1789249 baseEnd_1789249 := by
    simpa [prefixWord, tailWord_1789249, baseEnd_1789249] using wordTrace_append hprefix tailTrace_1789249
  have hstable : (prefixWord ++ tailWord_1789249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789249).length < 2 ^ (prefixWord ++ tailWord_1789249).sum := by decide
  have hdescent : baseEnd_1789249 < baseStart_1789249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789260 : List Nat := [2, 2, 1, 3, 2, 2, 1, 8]
def baseStart_1789260 : Nat := 118140960795 + 1789260 * 2 ^ 59
def prefixEnd_1789260 : Nat := 4983230072969 + 3 ^ 40 * 1789260 * 2
def baseEnd_1789260 : Nat := 136111169757596258625385

theorem tailTrace_1789260 : CollatzResearch.WordTrace tailWord_1789260 prefixEnd_1789260 136111169757596258625385 := by
  unfold tailWord_1789260
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629836748912038062270617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43506448998549384083027489 32629836748912038062270617)
  ·
    refine ⟨24472377561684028546702963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32629836748912038062270617 24472377561684028546702963)
    ·
      refine ⟨36708566342526042820054445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24472377561684028546702963 36708566342526042820054445)
      ·
        refine ⟨13765712378447266057520417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36708566342526042820054445 13765712378447266057520417)
        ·
          refine ⟨10324284283835449543140313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13765712378447266057520417 10324284283835449543140313)
          ·
            refine ⟨7743213212876587157355235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10324284283835449543140313 7743213212876587157355235)
            ·
              refine ⟨11614819819314880736032853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743213212876587157355235 11614819819314880736032853)
              ·
                refine ⟨136111169757596258625385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11614819819314880736032853 136111169757596258625385)
                ·
                  rfl

theorem cell21_1789260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_1789260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789260 prefixEnd_1789260 := by exact prefixLift 1789260
  have htrace : WordTrace (prefixWord ++ tailWord_1789260) baseStart_1789260 baseEnd_1789260 := by
    simpa [prefixWord, tailWord_1789260, baseEnd_1789260] using wordTrace_append hprefix tailTrace_1789260
  have hstable : (prefixWord ++ tailWord_1789260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789260).length < 2 ^ (prefixWord ++ tailWord_1789260).sum := by decide
  have hdescent : baseEnd_1789260 < baseStart_1789260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789294 : List Nat := [4, 1, 2, 4, 2, 8]
def baseStart_1789294 : Nat := 118140960795 + 1789294 * 2 ^ 59
def prefixEnd_1789294 : Nat := 4983230072969 + 3 ^ 40 * 1789294 * 2
def baseEnd_1789294 : Nat := 15123750686518973048497

theorem tailTrace_1789294 : CollatzResearch.WordTrace tailWord_1789294 prefixEnd_1789294 15123750686518973048497 := by
  unfold tailWord_1789294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157614197462612491409867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43507275719800599954185957 8157614197462612491409867)
  ·
    refine ⟨12236421296193918737114801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157614197462612491409867 12236421296193918737114801)
    ·
      refine ⟨9177315972145439052836101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12236421296193918737114801 9177315972145439052836101)
      ·
        refine ⟨1720746744777269822406769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9177315972145439052836101 1720746744777269822406769)
        ·
          refine ⟨1290560058582952366805077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720746744777269822406769 1290560058582952366805077)
          ·
            refine ⟨15123750686518973048497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1290560058582952366805077 15123750686518973048497)
            ·
              rfl

theorem cell21_1789294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 8].length) (baseStart_1789294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789294 prefixEnd_1789294 := by exact prefixLift 1789294
  have htrace : WordTrace (prefixWord ++ tailWord_1789294) baseStart_1789294 baseEnd_1789294 := by
    simpa [prefixWord, tailWord_1789294, baseEnd_1789294] using wordTrace_append hprefix tailTrace_1789294
  have hstable : (prefixWord ++ tailWord_1789294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789294).length < 2 ^ (prefixWord ++ tailWord_1789294).sum := by decide
  have hdescent : baseEnd_1789294 < baseStart_1789294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789305 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_1789305 : Nat := 118140960795 + 1789305 * 2 ^ 59
def prefixEnd_1789305 : Nat := 4983230072969 + 3 ^ 40 * 1789305 * 2
def baseEnd_1789305 : Nat := 408343778885878697626063

theorem tailTrace_1789305 : CollatzResearch.WordTrace tailWord_1789305 prefixEnd_1789305 408343778885878697626063 := by
  unfold tailWord_1789305
  simp only [CollatzResearch.WordTrace]
  refine ⟨65261314782661048809929369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43507543188440699206619579 65261314782661048809929369)
  ·
    refine ⟨48945986086995786607447027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65261314782661048809929369 48945986086995786607447027)
    ·
      refine ⟨73418979130493679911170541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48945986086995786607447027 73418979130493679911170541)
      ·
        refine ⟨27532117173935129966688953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73418979130493679911170541 27532117173935129966688953)
        ·
          refine ⟨20649087880451347475016715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27532117173935129966688953 20649087880451347475016715)
          ·
            refine ⟨30973631820677021212525073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20649087880451347475016715 30973631820677021212525073)
            ·
              refine ⟨23230223865507765909393805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30973631820677021212525073 23230223865507765909393805)
              ·
                refine ⟨8711333949565412216022677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23230223865507765909393805 8711333949565412216022677)
                ·
                  refine ⟨408343778885878697626063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8711333949565412216022677 408343778885878697626063)
                  ·
                    rfl

theorem cell21_1789305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_1789305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789305 prefixEnd_1789305 := by exact prefixLift 1789305
  have htrace : WordTrace (prefixWord ++ tailWord_1789305) baseStart_1789305 baseEnd_1789305 := by
    simpa [prefixWord, tailWord_1789305, baseEnd_1789305] using wordTrace_append hprefix tailTrace_1789305
  have hstable : (prefixWord ++ tailWord_1789305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789305).length < 2 ^ (prefixWord ++ tailWord_1789305).sum := by decide
  have hdescent : baseEnd_1789305 < baseStart_1789305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789308 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_1789308 : Nat := 118140960795 + 1789308 * 2 ^ 59
def prefixEnd_1789308 : Nat := 4983230072969 + 3 ^ 40 * 1789308 * 2
def baseEnd_1789308 : Nat := 408344463526751359076057

theorem tailTrace_1789308 : CollatzResearch.WordTrace tailWord_1789308 prefixEnd_1789308 408344463526751359076057 := by
  unfold tailWord_1789308
  simp only [CollatzResearch.WordTrace]
  refine ⟨32630712100825090161144289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43507616134433453548192385 32630712100825090161144289)
  ·
    refine ⟨24473034075618817620858217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32630712100825090161144289 24473034075618817620858217)
    ·
      refine ⟨18354775556714113215643663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24473034075618817620858217 18354775556714113215643663)
      ·
        refine ⟨27532163335071169823465495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18354775556714113215643663 27532163335071169823465495)
        ·
          refine ⟨41298245002606754735198243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27532163335071169823465495 41298245002606754735198243)
          ·
            refine ⟨61947367503910132102797365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41298245002606754735198243 61947367503910132102797365)
            ·
              refine ⟨5807565703491574884637253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61947367503910132102797365 5807565703491574884637253)
              ·
                refine ⟨1088918569404670290869485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5807565703491574884637253 1088918569404670290869485)
                ·
                  refine ⟨408344463526751359076057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088918569404670290869485 408344463526751359076057)
                  ·
                    rfl

theorem cell21_1789308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_1789308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789308 prefixEnd_1789308 := by exact prefixLift 1789308
  have htrace : WordTrace (prefixWord ++ tailWord_1789308) baseStart_1789308 baseEnd_1789308 := by
    simpa [prefixWord, tailWord_1789308, baseEnd_1789308] using wordTrace_append hprefix tailTrace_1789308
  have hstable : (prefixWord ++ tailWord_1789308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789308).length < 2 ^ (prefixWord ++ tailWord_1789308).sum := by decide
  have hdescent : baseEnd_1789308 < baseStart_1789308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789367 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_1789367 : Nat := 118140960795 + 1789367 * 2 ^ 59
def prefixEnd_1789367 : Nat := 4983230072969 + 3 ^ 40 * 1789367 * 2
def baseEnd_1789367 : Nat := 408357928130580367592603

theorem tailTrace_1789367 : CollatzResearch.WordTrace tailWord_1789367 prefixEnd_1789367 408357928130580367592603 := by
  unfold tailWord_1789367
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263576108436433398686355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43509050738957622265790903 65263576108436433398686355)
  ·
    refine ⟨97895364162654650098029533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65263576108436433398686355 97895364162654650098029533)
    ·
      refine ⟨36710761560995493786761075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97895364162654650098029533 36710761560995493786761075)
      ·
        refine ⟨55066142341493240680141613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36710761560995493786761075 55066142341493240680141613)
        ·
          refine ⟨20649803378059965255053105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55066142341493240680141613 20649803378059965255053105)
          ·
            refine ⟨15487352533544973941289829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20649803378059965255053105 15487352533544973941289829)
            ·
              refine ⟨2903878600039682613991843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15487352533544973941289829 2903878600039682613991843)
              ·
                refine ⟨4355817900059523920987765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903878600039682613991843 4355817900059523920987765)
                ·
                  refine ⟨408357928130580367592603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355817900059523920987765 408357928130580367592603)
                  ·
                    rfl

theorem cell21_1789367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_1789367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789367 prefixEnd_1789367 := by exact prefixLift 1789367
  have htrace : WordTrace (prefixWord ++ tailWord_1789367) baseStart_1789367 baseEnd_1789367 := by
    simpa [prefixWord, tailWord_1789367, baseEnd_1789367] using wordTrace_append hprefix tailTrace_1789367
  have hstable : (prefixWord ++ tailWord_1789367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789367).length < 2 ^ (prefixWord ++ tailWord_1789367).sum := by decide
  have hdescent : baseEnd_1789367 < baseStart_1789367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789401 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 3]
def baseStart_1789401 : Nat := 118140960795 + 1789401 * 2 ^ 59
def prefixEnd_1789401 : Nat := 4983230072969 + 3 ^ 40 * 1789401 * 2
def baseEnd_1789401 : Nat := 408365687393803864025867

theorem tailTrace_1789401 : CollatzResearch.WordTrace tailWord_1789401 prefixEnd_1789401 408365687393803864025867 := by
  unfold tailWord_1789401
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264816190313257205424057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43509877460208838136949371 65264816190313257205424057)
  ·
    refine ⟨48948612142734942904068043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65264816190313257205424057 48948612142734942904068043)
    ·
      refine ⟨73422918214102414356102065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48948612142734942904068043 73422918214102414356102065)
      ·
        refine ⟨55067188660576810767076549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73422918214102414356102065 55067188660576810767076549)
        ·
          refine ⟨10325097873858152018826853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55067188660576810767076549 10325097873858152018826853)
          ·
            refine ⟨1935955851348403503530035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10325097873858152018826853 1935955851348403503530035)
            ·
              refine ⟨2903933777022605255295053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935955851348403503530035 2903933777022605255295053)
              ·
                refine ⟨1088975166383476970735645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2903933777022605255295053 1088975166383476970735645)
                ·
                  refine ⟨408365687393803864025867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088975166383476970735645 408365687393803864025867)
                  ·
                    rfl

theorem cell21_1789401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_1789401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789401 prefixEnd_1789401 := by exact prefixLift 1789401
  have htrace : WordTrace (prefixWord ++ tailWord_1789401) baseStart_1789401 baseEnd_1789401 := by
    simpa [prefixWord, tailWord_1789401, baseEnd_1789401] using wordTrace_append hprefix tailTrace_1789401
  have hstable : (prefixWord ++ tailWord_1789401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789401).length < 2 ^ (prefixWord ++ tailWord_1789401).sum := by decide
  have hdescent : baseEnd_1789401 < baseStart_1789401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789418 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_1789418 : Nat := 118140960795 + 1789418 * 2 ^ 59
def prefixEnd_1789418 : Nat := 4983230072969 + 3 ^ 40 * 1789418 * 2
def baseEnd_1789418 : Nat := 408369567025415612242499

theorem tailTrace_1789418 : CollatzResearch.WordTrace tailWord_1789418 prefixEnd_1789418 408369567025415612242499 := by
  unfold tailWord_1789418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316359057812917277198227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43510290820834446072528605 16316359057812917277198227)
  ·
    refine ⟨24474538586719375915797341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16316359057812917277198227 24474538586719375915797341)
    ·
      refine ⟨9177951970019765968424003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24474538586719375915797341 9177951970019765968424003)
      ·
        refine ⟨13766927955029648952636005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177951970019765968424003 13766927955029648952636005)
        ·
          refine ⟨2581298991568059178619251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13766927955029648952636005 2581298991568059178619251)
          ·
            refine ⟨3871948487352088767928877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581298991568059178619251 3871948487352088767928877)
            ·
              refine ⟨1451980682757033287973329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871948487352088767928877 1451980682757033287973329)
              ·
                refine ⟨1088985512067774965979997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451980682757033287973329 1088985512067774965979997)
                ·
                  refine ⟨408369567025415612242499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088985512067774965979997 408369567025415612242499)
                  ·
                    rfl

theorem cell21_1789418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_1789418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789418 prefixEnd_1789418 := by exact prefixLift 1789418
  have htrace : WordTrace (prefixWord ++ tailWord_1789418) baseStart_1789418 baseEnd_1789418 := by
    simpa [prefixWord, tailWord_1789418, baseEnd_1789418] using wordTrace_append hprefix tailTrace_1789418
  have hstable : (prefixWord ++ tailWord_1789418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789418).length < 2 ^ (prefixWord ++ tailWord_1789418).sum := by decide
  have hdescent : baseEnd_1789418 < baseStart_1789418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789429 : List Nat := [1, 3, 5, 1, 1, 1, 1, 8]
def baseStart_1789429 : Nat := 118140960795 + 1789429 * 2 ^ 59
def prefixEnd_1789429 : Nat := 4983230072969 + 3 ^ 40 * 1789429 * 2
def baseEnd_1789429 : Nat := 136124025791760679186381

theorem tailTrace_1789429 : CollatzResearch.WordTrace tailWord_1789429 prefixEnd_1789429 136124025791760679186381 := by
  unfold tailWord_1789429
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265837434211817987443341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43510558289474545324962227 65265837434211817987443341)
  ·
    refine ⟨24474689037829431745291253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65265837434211817987443341 24474689037829431745291253)
    ·
      refine ⟨2294502097296509226121055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24474689037829431745291253 2294502097296509226121055)
      ·
        refine ⟨3441753145944763839181583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294502097296509226121055 3441753145944763839181583)
        ·
          refine ⟨5162629718917145758772375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441753145944763839181583 5162629718917145758772375)
          ·
            refine ⟨7743944578375718638158563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162629718917145758772375 7743944578375718638158563)
            ·
              refine ⟨11615916867563577957237845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743944578375718638158563 11615916867563577957237845)
              ·
                refine ⟨136124025791760679186381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11615916867563577957237845 136124025791760679186381)
                ·
                  rfl

theorem cell21_1789429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_1789429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789429 prefixEnd_1789429 := by exact prefixLift 1789429
  have htrace : WordTrace (prefixWord ++ tailWord_1789429) baseStart_1789429 baseEnd_1789429 := by
    simpa [prefixWord, tailWord_1789429, baseEnd_1789429] using wordTrace_append hprefix tailTrace_1789429
  have hstable : (prefixWord ++ tailWord_1789429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789429).length < 2 ^ (prefixWord ++ tailWord_1789429).sum := by decide
  have hdescent : baseEnd_1789429 < baseStart_1789429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789474 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1789474 : Nat := 118140960795 + 1789474 * 2 ^ 59
def prefixEnd_1789474 : Nat := 4983230072969 + 3 ^ 40 * 1789474 * 2
def baseEnd_1789474 : Nat := 408382346988371959309051

theorem tailTrace_1789474 : CollatzResearch.WordTrace tailWord_1789474 prefixEnd_1789474 408382346988371959309051 := by
  unfold tailWord_1789474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316869679762197668207869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43511652479365860448554317 16316869679762197668207869)
  ·
    refine ⟨6118826129910824125577951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16316869679762197668207869 6118826129910824125577951)
    ·
      refine ⟨9178239194866236188366927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118826129910824125577951 9178239194866236188366927)
      ·
        refine ⟨13767358792299354282550391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178239194866236188366927 13767358792299354282550391)
        ·
          refine ⟨20651038188449031423825587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13767358792299354282550391 20651038188449031423825587)
          ·
            refine ⟨30976557282673547135738381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20651038188449031423825587 30976557282673547135738381)
            ·
              refine ⟨11616208981002580175901893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30976557282673547135738381 11616208981002580175901893)
              ·
                refine ⟨2178039183937983782981605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11616208981002580175901893 2178039183937983782981605)
                ·
                  refine ⟨408382346988371959309051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178039183937983782981605 408382346988371959309051)
                  ·
                    rfl

theorem cell21_1789474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1789474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789474 prefixEnd_1789474 := by exact prefixLift 1789474
  have htrace : WordTrace (prefixWord ++ tailWord_1789474) baseStart_1789474 baseEnd_1789474 := by
    simpa [prefixWord, tailWord_1789474, baseEnd_1789474] using wordTrace_append hprefix tailTrace_1789474
  have hstable : (prefixWord ++ tailWord_1789474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789474).length < 2 ^ (prefixWord ++ tailWord_1789474).sum := by decide
  have hdescent : baseEnd_1789474 < baseStart_1789474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789505 : List Nat := [1, 2, 5, 1, 1, 1, 5, 5]
def baseStart_1789505 : Nat := 118140960795 + 1789505 * 2 ^ 59
def prefixEnd_1789505 : Nat := 4983230072969 + 3 ^ 40 * 1789505 * 2
def baseEnd_1789505 : Nat := 136129807203574264764107

theorem tailTrace_1789505 : CollatzResearch.WordTrace tailWord_1789505 prefixEnd_1789505 136129807203574264764107 := by
  unfold tailWord_1789505
  simp only [CollatzResearch.WordTrace]
  refine ⟨65268609381936482967209969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43512406254624321978139979 65268609381936482967209969)
  ·
    refine ⟨48951457036452362225407477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65268609381936482967209969 48951457036452362225407477)
    ·
      refine ⟨4589199097167408958631951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48951457036452362225407477 4589199097167408958631951)
      ·
        refine ⟨6883798645751113437947927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589199097167408958631951 6883798645751113437947927)
        ·
          refine ⟨10325697968626670156921891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883798645751113437947927 10325697968626670156921891)
          ·
            refine ⟨15488546952940005235382837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325697968626670156921891 15488546952940005235382837)
            ·
              refine ⟨1452051276838125490817141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15488546952940005235382837 1452051276838125490817141)
              ·
                refine ⟨136129807203574264764107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452051276838125490817141 136129807203574264764107)
                ·
                  rfl

theorem cell21_1789505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].length) (baseStart_1789505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789505 prefixEnd_1789505 := by exact prefixLift 1789505
  have htrace : WordTrace (prefixWord ++ tailWord_1789505) baseStart_1789505 baseEnd_1789505 := by
    simpa [prefixWord, tailWord_1789505, baseEnd_1789505] using wordTrace_append hprefix tailTrace_1789505
  have hstable : (prefixWord ++ tailWord_1789505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789505).length < 2 ^ (prefixWord ++ tailWord_1789505).sum := by decide
  have hdescent : baseEnd_1789505 < baseStart_1789505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789719 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 4]
def baseStart_1789719 : Nat := 118140960795 + 1789719 * 2 ^ 59
def prefixEnd_1789719 : Nat := 4983230072969 + 3 ^ 40 * 1789719 * 2
def baseEnd_1789719 : Nat := 408438259326305977725217

theorem tailTrace_1789719 : CollatzResearch.WordTrace tailWord_1789719 prefixEnd_1789719 408438259326305977725217 := by
  unfold tailWord_1789719
  simp only [CollatzResearch.WordTrace]
  refine ⟨65276414603161197515500211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43517609735440798343666807 65276414603161197515500211)
  ·
    refine ⟨97914621904741796273250317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65276414603161197515500211 97914621904741796273250317)
    ·
      refine ⟨36717983214278173602468869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97914621904741796273250317 36717983214278173602468869)
      ·
        refine ⟨6884621852677157550462913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36717983214278173602468869 6884621852677157550462913)
        ·
          refine ⟨5163466389507868162847185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884621852677157550462913 5163466389507868162847185)
          ·
            refine ⟨3872599792130901122135389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163466389507868162847185 3872599792130901122135389)
            ·
              refine ⟨1452224922049087920800771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3872599792130901122135389 1452224922049087920800771)
              ·
                refine ⟨2178337383073631881201157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452224922049087920800771 2178337383073631881201157)
                ·
                  refine ⟨408438259326305977725217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178337383073631881201157 408438259326305977725217)
                  ·
                    rfl

theorem cell21_1789719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_1789719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789719 prefixEnd_1789719 := by exact prefixLift 1789719
  have htrace : WordTrace (prefixWord ++ tailWord_1789719) baseStart_1789719 baseEnd_1789719 := by
    simpa [prefixWord, tailWord_1789719, baseEnd_1789719] using wordTrace_append hprefix tailTrace_1789719
  have hstable : (prefixWord ++ tailWord_1789719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789719).length < 2 ^ (prefixWord ++ tailWord_1789719).sum := by decide
  have hdescent : baseEnd_1789719 < baseStart_1789719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789733 : List Nat := [1, 3, 1, 2, 3, 4, 2, 5]
def baseStart_1789733 : Nat := 118140960795 + 1789733 * 2 ^ 59
def prefixEnd_1789733 : Nat := 4983230072969 + 3 ^ 40 * 1789733 * 2
def baseEnd_1789733 : Nat := 136147151439015021497285

theorem tailTrace_1789733 : CollatzResearch.WordTrace tailWord_1789733 prefixEnd_1789733 136147151439015021497285 := by
  unfold tailWord_1789733
  simp only [CollatzResearch.WordTrace]
  refine ⟨65276925225110477906509853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43517950150073651937673235 65276925225110477906509853)
  ·
    refine ⟨24478846959416429214941195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65276925225110477906509853 24478846959416429214941195)
    ·
      refine ⟨36718270439124643822411793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478846959416429214941195 36718270439124643822411793)
      ·
        refine ⟨27538702829343482866808845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36718270439124643822411793 27538702829343482866808845)
        ·
          refine ⟨10327013561003806075053317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27538702829343482866808845 10327013561003806075053317)
          ·
            refine ⟨1936315042688213639072497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10327013561003806075053317 1936315042688213639072497)
            ·
              refine ⟨1452236282016160229304373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936315042688213639072497 1452236282016160229304373)
              ·
                refine ⟨136147151439015021497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452236282016160229304373 136147151439015021497285)
                ·
                  rfl

theorem cell21_1789733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].length) (baseStart_1789733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789733 prefixEnd_1789733 := by exact prefixLift 1789733
  have htrace : WordTrace (prefixWord ++ tailWord_1789733) baseStart_1789733 baseEnd_1789733 := by
    simpa [prefixWord, tailWord_1789733, baseEnd_1789733] using wordTrace_append hprefix tailTrace_1789733
  have hstable : (prefixWord ++ tailWord_1789733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789733).length < 2 ^ (prefixWord ++ tailWord_1789733).sum := by decide
  have hdescent : baseEnd_1789733 < baseStart_1789733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789778 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1789778 : Nat := 118140960795 + 1789778 * 2 ^ 59
def prefixEnd_1789778 : Nat := 4983230072969 + 3 ^ 40 * 1789778 * 2
def baseEnd_1789778 : Nat := 408451723930134986241763

theorem tailTrace_1789778 : CollatzResearch.WordTrace tailWord_1789778 prefixEnd_1789778 408451723930134986241763 := by
  unfold tailWord_1789778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319641627486862647974497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43519044339964967061265325 16319641627486862647974497)
  ·
    refine ⟨12239731220615146985980873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16319641627486862647974497 12239731220615146985980873)
    ·
      refine ⟨9179798415461360239485655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12239731220615146985980873 9179798415461360239485655)
      ·
        refine ⟨13769697623192040359228483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9179798415461360239485655 13769697623192040359228483)
        ·
          refine ⟨20654546434788060538842725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769697623192040359228483 20654546434788060538842725)
          ·
            refine ⟨3872727456522761351033011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20654546434788060538842725 3872727456522761351033011)
            ·
              refine ⟨5809091184784142026549517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872727456522761351033011 5809091184784142026549517)
              ·
                refine ⟨2178409194294053259956069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5809091184784142026549517 2178409194294053259956069)
                ·
                  refine ⟨408451723930134986241763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178409194294053259956069 408451723930134986241763)
                  ·
                    rfl

theorem cell21_1789778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1789778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789778 prefixEnd_1789778 := by exact prefixLift 1789778
  have htrace : WordTrace (prefixWord ++ tailWord_1789778) baseStart_1789778 baseEnd_1789778 := by
    simpa [prefixWord, tailWord_1789778, baseEnd_1789778] using wordTrace_append hprefix tailTrace_1789778
  have hstable : (prefixWord ++ tailWord_1789778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789778).length < 2 ^ (prefixWord ++ tailWord_1789778).sum := by decide
  have hdescent : baseEnd_1789778 < baseStart_1789778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789857 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 3]
def baseStart_1789857 : Nat := 118140960795 + 1789857 * 2 ^ 59
def prefixEnd_1789857 : Nat := 4983230072969 + 3 ^ 40 * 1789857 * 2
def baseEnd_1789857 : Nat := 408469752806448404424935

theorem tailTrace_1789857 : CollatzResearch.WordTrace tailWord_1789857 prefixEnd_1789857 408469752806448404424935 := by
  unfold tailWord_1789857
  simp only [CollatzResearch.WordTrace]
  refine ⟨65281447876661247084023825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43520965251107498056015883 65281447876661247084023825)
  ·
    refine ⟨48961085907495935313017869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65281447876661247084023825 48961085907495935313017869)
    ·
      refine ⟨18360407215310975742381701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48961085907495935313017869 18360407215310975742381701)
      ·
        refine ⟨3442576352870807951696569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18360407215310975742381701 3442576352870807951696569)
        ·
          refine ⟨2581932264653105963772427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442576352870807951696569 2581932264653105963772427)
          ·
            refine ⟨3872898396979658945658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581932264653105963772427 3872898396979658945658641)
            ·
              refine ⟨2904673797734744209243981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872898396979658945658641 2904673797734744209243981)
              ·
                refine ⟨1089252674150529078466493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904673797734744209243981 1089252674150529078466493)
                ·
                  refine ⟨408469752806448404424935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089252674150529078466493 408469752806448404424935)
                  ·
                    rfl

theorem cell21_1789857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_1789857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789857 prefixEnd_1789857 := by exact prefixLift 1789857
  have htrace : WordTrace (prefixWord ++ tailWord_1789857) baseStart_1789857 baseEnd_1789857 := by
    simpa [prefixWord, tailWord_1789857, baseEnd_1789857] using wordTrace_append hprefix tailTrace_1789857
  have hstable : (prefixWord ++ tailWord_1789857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789857).length < 2 ^ (prefixWord ++ tailWord_1789857).sum := by decide
  have hdescent : baseEnd_1789857 < baseStart_1789857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789933 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1789933 : Nat := 118140960795 + 1789933 * 2 ^ 59
def prefixEnd_1789933 : Nat := 4983230072969 + 3 ^ 40 * 1789933 * 2
def baseEnd_1789933 : Nat := 408487097041889161158113

theorem tailTrace_1789933 : CollatzResearch.WordTrace tailWord_1789933 prefixEnd_1789933 408487097041889161158113 := by
  unfold tailWord_1789933
  simp only [CollatzResearch.WordTrace]
  refine ⟨65284219824385912063790453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43522813216257274709193635 65284219824385912063790453)
  ·
    refine ⟨6120395608536179255980355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65284219824385912063790453 6120395608536179255980355)
    ·
      refine ⟨9180593412804268883970533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6120395608536179255980355 9180593412804268883970533)
      ·
        refine ⟨1721361264900800415744475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9180593412804268883970533 1721361264900800415744475)
        ·
          refine ⟨2582041897351200623616713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721361264900800415744475 2582041897351200623616713)
          ·
            refine ⟨1936531423013400467712535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582041897351200623616713 1936531423013400467712535)
            ·
              refine ⟨2904797134520100701568803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936531423013400467712535 2904797134520100701568803)
              ·
                refine ⟨4357195701780151052353205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904797134520100701568803 4357195701780151052353205)
                ·
                  refine ⟨408487097041889161158113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4357195701780151052353205 408487097041889161158113)
                  ·
                    rfl

theorem cell21_1789933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1789933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789933 prefixEnd_1789933 := by exact prefixLift 1789933
  have htrace : WordTrace (prefixWord ++ tailWord_1789933) baseStart_1789933 baseEnd_1789933 := by
    simpa [prefixWord, tailWord_1789933, baseEnd_1789933] using wordTrace_append hprefix tailTrace_1789933
  have hstable : (prefixWord ++ tailWord_1789933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789933).length < 2 ^ (prefixWord ++ tailWord_1789933).sum := by decide
  have hdescent : baseEnd_1789933 < baseStart_1789933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789989 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_1789989 : Nat := 118140960795 + 1789989 * 2 ^ 59
def prefixEnd_1789989 : Nat := 4983230072969 + 3 ^ 40 * 1789989 * 2
def baseEnd_1789989 : Nat := 408499877004845508224665

theorem tailTrace_1789989 : CollatzResearch.WordTrace tailWord_1789989 prefixEnd_1789989 408499877004845508224665 := by
  unfold tailWord_1789989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65286262312183033627829021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43524174874788689085219347 65286262312183033627829021)
  ·
    refine ⟨24482348367068637610435883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65286262312183033627829021 24482348367068637610435883)
    ·
      refine ⟨36723522550602956415653825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482348367068637610435883 36723522550602956415653825)
      ·
        refine ⟨27542641912952217311740369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36723522550602956415653825 27542641912952217311740369)
        ·
          refine ⟨20656981434714162983805277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542641912952217311740369 20656981434714162983805277)
          ·
            refine ⟨7746368038017811118926979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20656981434714162983805277 7746368038017811118926979)
            ·
              refine ⟨11619552057026716678390469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746368038017811118926979 11619552057026716678390469)
              ·
                refine ⟨2178666010692509377198213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11619552057026716678390469 2178666010692509377198213)
                ·
                  refine ⟨408499877004845508224665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178666010692509377198213 408499877004845508224665)
                  ·
                    rfl

theorem cell21_1789989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_1789989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1789989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1789989 prefixEnd_1789989 := by exact prefixLift 1789989
  have htrace : WordTrace (prefixWord ++ tailWord_1789989) baseStart_1789989 baseEnd_1789989 := by
    simpa [prefixWord, tailWord_1789989, baseEnd_1789989] using wordTrace_append hprefix tailTrace_1789989
  have hstable : (prefixWord ++ tailWord_1789989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789989).length < 2 ^ (prefixWord ++ tailWord_1789989).sum := by decide
  have hdescent : baseEnd_1789989 < baseStart_1789989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790003 : List Nat := [1, 1, 1, 2, 4, 1, 5, 6]
def baseStart_1790003 : Nat := 118140960795 + 1790003 * 2 ^ 59
def prefixEnd_1790003 : Nat := 4983230072969 + 3 ^ 40 * 1790003 * 2
def baseEnd_1790003 : Nat := 136167690665194864997101

theorem tailTrace_1790003 : CollatzResearch.WordTrace tailWord_1790003 prefixEnd_1790003 136167690665194864997101 := by
  unfold tailWord_1790003
  simp only [CollatzResearch.WordTrace]
  refine ⟨65286772934132314018838663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43524515289421542679225775 65286772934132314018838663)
  ·
    refine ⟨97930159401198471028257995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65286772934132314018838663 97930159401198471028257995)
    ·
      refine ⟨146895239101797706542386993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97930159401198471028257995 146895239101797706542386993)
      ·
        refine ⟨110171429326348279906790245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146895239101797706542386993 110171429326348279906790245)
        ·
          refine ⟨20657142998690302482523171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110171429326348279906790245 20657142998690302482523171)
          ·
            refine ⟨30985714498035453723784757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657142998690302482523171 30985714498035453723784757)
            ·
              refine ⟨2904910734190823786604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30985714498035453723784757 2904910734190823786604821)
              ·
                refine ⟨136167690665194864997101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2904910734190823786604821 136167690665194864997101)
                ·
                  rfl

theorem cell21_1790003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_1790003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790003 prefixEnd_1790003 := by exact prefixLift 1790003
  have htrace : WordTrace (prefixWord ++ tailWord_1790003) baseStart_1790003 baseEnd_1790003 := by
    simpa [prefixWord, tailWord_1790003, baseEnd_1790003] using wordTrace_append hprefix tailTrace_1790003
  have hstable : (prefixWord ++ tailWord_1790003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790003).length < 2 ^ (prefixWord ++ tailWord_1790003).sum := by decide
  have hdescent : baseEnd_1790003 < baseStart_1790003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790006 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1790006 : Nat := 118140960795 + 1790006 * 2 ^ 59
def prefixEnd_1790006 : Nat := 4983230072969 + 3 ^ 40 * 1790006 * 2
def baseEnd_1790006 : Nat := 408503756636457256441297

theorem tailTrace_1790006 : CollatzResearch.WordTrace tailWord_1790006 prefixEnd_1790006 408503756636457256441297 := by
  unfold tailWord_1790006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080430147070090345699867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43524588235414297020798581 4080430147070090345699867)
  ·
    refine ⟨6120645220605135518549801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4080430147070090345699867 6120645220605135518549801)
    ·
      refine ⟨4590483915453851638912351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6120645220605135518549801 4590483915453851638912351)
      ·
        refine ⟨6885725873180777458368527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590483915453851638912351 6885725873180777458368527)
        ·
          refine ⟨10328588809771166187552791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885725873180777458368527 10328588809771166187552791)
          ·
            refine ⟨15492883214656749281329187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328588809771166187552791 15492883214656749281329187)
            ·
              refine ⟨23239324821985123921993781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492883214656749281329187 23239324821985123921993781)
              ·
                refine ⟨2178686702061105367686917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23239324821985123921993781 2178686702061105367686917)
                ·
                  refine ⟨408503756636457256441297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178686702061105367686917 408503756636457256441297)
                  ·
                    rfl

theorem cell21_1790006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1790006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790006 prefixEnd_1790006 := by exact prefixLift 1790006
  have htrace : WordTrace (prefixWord ++ tailWord_1790006) baseStart_1790006 baseEnd_1790006 := by
    simpa [prefixWord, tailWord_1790006, baseEnd_1790006] using wordTrace_append hprefix tailTrace_1790006
  have hstable : (prefixWord ++ tailWord_1790006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790006).length < 2 ^ (prefixWord ++ tailWord_1790006).sum := by decide
  have hdescent : baseEnd_1790006 < baseStart_1790006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790051 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 3]
def baseStart_1790051 : Nat := 118140960795 + 1790051 * 2 ^ 59
def prefixEnd_1790051 : Nat := 4983230072969 + 3 ^ 40 * 1790051 * 2
def baseEnd_1790051 : Nat := 408514026249547178191205

theorem tailTrace_1790051 : CollatzResearch.WordTrace tailWord_1790051 prefixEnd_1790051 408514026249547178191205 := by
  unfold tailWord_1790051
  simp only [CollatzResearch.WordTrace]
  refine ⟨65288523637958418216586007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43525682425305612144390671 65288523637958418216586007)
  ·
    refine ⟨97932785456937627324879011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65288523637958418216586007 97932785456937627324879011)
    ·
      refine ⟨146899178185406440987318517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97932785456937627324879011 146899178185406440987318517)
      ·
        refine ⟨13771797954881853842561111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146899178185406440987318517 13771797954881853842561111)
        ·
          refine ⟨20657696932322780763841667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13771797954881853842561111 20657696932322780763841667)
          ·
            refine ⟨30986545398484171145762501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657696932322780763841667 30986545398484171145762501)
            ·
              refine ⟨5809977262215782089830469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30986545398484171145762501 5809977262215782089830469)
              ·
                refine ⟨1089370736665459141843213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5809977262215782089830469 1089370736665459141843213)
                ·
                  refine ⟨408514026249547178191205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089370736665459141843213 408514026249547178191205)
                  ·
                    rfl

theorem cell21_1790051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].length) (baseStart_1790051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790051 prefixEnd_1790051 := by exact prefixLift 1790051
  have htrace : WordTrace (prefixWord ++ tailWord_1790051) baseStart_1790051 baseEnd_1790051 := by
    simpa [prefixWord, tailWord_1790051, baseEnd_1790051] using wordTrace_append hprefix tailTrace_1790051
  have hstable : (prefixWord ++ tailWord_1790051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790051).length < 2 ^ (prefixWord ++ tailWord_1790051).sum := by decide
  have hdescent : baseEnd_1790051 < baseStart_1790051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790116 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1790116 : Nat := 118140960795 + 1790116 * 2 ^ 59
def prefixEnd_1790116 : Nat := 4983230072969 + 3 ^ 40 * 1790116 * 2
def baseEnd_1790116 : Nat := 408528860135121509607739

theorem tailTrace_1790116 : CollatzResearch.WordTrace tailWord_1790116 prefixEnd_1790116 408528860135121509607739 := by
  unfold tailWord_1790116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32645447191361467158851101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43527262921815289545134801 32645447191361467158851101)
  ·
    refine ⟨12242042696760550184569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32645447191361467158851101 12242042696760550184569163)
    ·
      refine ⟨18363064045140825276853745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12242042696760550184569163 18363064045140825276853745)
      ·
        refine ⟨13772298033855618957640309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18363064045140825276853745 13772298033855618957640309)
        ·
          refine ⟨1291152940673964277278779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13772298033855618957640309 1291152940673964277278779)
          ·
            refine ⟨1936729411010946415918169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291152940673964277278779 1936729411010946415918169)
            ·
              refine ⟨1452547058258209811938627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936729411010946415918169 1452547058258209811938627)
              ·
                refine ⟨2178820587387314717907941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452547058258209811938627 2178820587387314717907941)
                ·
                  refine ⟨408528860135121509607739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178820587387314717907941 408528860135121509607739)
                  ·
                    rfl

theorem cell21_1790116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1790116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790116 prefixEnd_1790116 := by exact prefixLift 1790116
  have htrace : WordTrace (prefixWord ++ tailWord_1790116) baseStart_1790116 baseEnd_1790116 := by
    simpa [prefixWord, tailWord_1790116, baseEnd_1790116] using wordTrace_append hprefix tailTrace_1790116
  have hstable : (prefixWord ++ tailWord_1790116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790116).length < 2 ^ (prefixWord ++ tailWord_1790116).sum := by decide
  have hdescent : baseEnd_1790116 < baseStart_1790116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790158 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1790158 : Nat := 118140960795 + 1790158 * 2 ^ 59
def prefixEnd_1790158 : Nat := 4983230072969 + 3 ^ 40 * 1790158 * 2
def baseEnd_1790158 : Nat := 408538445107338769907653

theorem tailTrace_1790158 : CollatzResearch.WordTrace tailWord_1790158 prefixEnd_1790158 408538445107338769907653 := by
  unfold tailWord_1790158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161553281071346936341391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43528284165713850327154085 8161553281071346936341391)
  ·
    refine ⟨12242329921607020404512087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161553281071346936341391 12242329921607020404512087)
    ·
      refine ⟨18363494882410530606768131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12242329921607020404512087 18363494882410530606768131)
      ·
        refine ⟨27545242323615795910152197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18363494882410530606768131 27545242323615795910152197)
        ·
          refine ⟨5164732935677961733153537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27545242323615795910152197 5164732935677961733153537)
          ·
            refine ⟨3873549701758471299865153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5164732935677961733153537 3873549701758471299865153)
            ·
              refine ⟨2905162276318853474898865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873549701758471299865153 2905162276318853474898865)
              ·
                refine ⟨2178871707239140106174149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905162276318853474898865 2178871707239140106174149)
                ·
                  refine ⟨408538445107338769907653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178871707239140106174149 408538445107338769907653)
                  ·
                    rfl

theorem cell21_1790158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1790158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790158 prefixEnd_1790158 := by exact prefixLift 1790158
  have htrace : WordTrace (prefixWord ++ tailWord_1790158) baseStart_1790158 baseEnd_1790158 := by
    simpa [prefixWord, tailWord_1790158, baseEnd_1790158] using wordTrace_append hprefix tailTrace_1790158
  have hstable : (prefixWord ++ tailWord_1790158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790158).length < 2 ^ (prefixWord ++ tailWord_1790158).sum := by decide
  have hdescent : baseEnd_1790158 < baseStart_1790158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790186 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1790186 : Nat := 118140960795 + 1790186 * 2 ^ 59
def prefixEnd_1790186 : Nat := 4983230072969 + 3 ^ 40 * 1790186 * 2
def baseEnd_1790186 : Nat := 408544835088816943440929

theorem tailTrace_1790186 : CollatzResearch.WordTrace tailWord_1790186 prefixEnd_1790186 408544835088816943440929 := by
  unfold tailWord_1790186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323361873117334068187603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43528964994979557515166941 16323361873117334068187603)
  ·
    refine ⟨24485042809676001102281405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16323361873117334068187603 24485042809676001102281405)
    ·
      refine ⟨9181891053628500413355527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24485042809676001102281405 9181891053628500413355527)
      ·
        refine ⟨13772836580442750620033291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9181891053628500413355527 13772836580442750620033291)
        ·
          refine ⟨20659254870664125930049937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13772836580442750620033291 20659254870664125930049937)
          ·
            refine ⟨15494441152998094447537453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20659254870664125930049937 15494441152998094447537453)
            ·
              refine ⟨5810415432374285417826545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15494441152998094447537453 5810415432374285417826545)
              ·
                refine ⟨4357811574280714063369909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810415432374285417826545 4357811574280714063369909)
                ·
                  refine ⟨408544835088816943440929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4357811574280714063369909 408544835088816943440929)
                  ·
                    rfl

theorem cell21_1790186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1790186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790186 prefixEnd_1790186 := by exact prefixLift 1790186
  have htrace : WordTrace (prefixWord ++ tailWord_1790186) baseStart_1790186 baseEnd_1790186 := by
    simpa [prefixWord, tailWord_1790186, baseEnd_1790186] using wordTrace_append hprefix tailTrace_1790186
  have hstable : (prefixWord ++ tailWord_1790186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790186).length < 2 ^ (prefixWord ++ tailWord_1790186).sum := by decide
  have hdescent : baseEnd_1790186 < baseStart_1790186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790189 : List Nat := [1, 5, 1, 2, 3, 1, 3, 5]
def baseStart_1790189 : Nat := 118140960795 + 1790189 * 2 ^ 59
def prefixEnd_1790189 : Nat := 4983230072969 + 3 ^ 40 * 1790189 * 2
def baseEnd_1790189 : Nat := 136181839909896534963641

theorem tailTrace_1790189 : CollatzResearch.WordTrace tailWord_1790189 prefixEnd_1790189 136181839909896534963641 := by
  unfold tailWord_1790189
  simp only [CollatzResearch.WordTrace]
  refine ⟨65293556911458467785109621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43529037940972311856739747 65293556911458467785109621)
  ·
    refine ⟨6121270960449231354854027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65293556911458467785109621 6121270960449231354854027)
    ·
      refine ⟨9181906440673847032281041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121270960449231354854027 9181906440673847032281041)
      ·
        refine ⟨6886429830505385274210781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9181906440673847032281041 6886429830505385274210781)
        ·
          refine ⟨2582411186439519477829043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6886429830505385274210781 2582411186439519477829043)
          ·
            refine ⟨3873616779659279216743565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582411186439519477829043 3873616779659279216743565)
            ·
              refine ⟨1452606292372229706278837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3873616779659279216743565 1452606292372229706278837)
              ·
                refine ⟨136181839909896534963641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452606292372229706278837 136181839909896534963641)
                ·
                  rfl

theorem cell21_1790189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].length) (baseStart_1790189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790189 prefixEnd_1790189 := by exact prefixLift 1790189
  have htrace : WordTrace (prefixWord ++ tailWord_1790189) baseStart_1790189 baseEnd_1790189 := by
    simpa [prefixWord, tailWord_1790189, baseEnd_1790189] using wordTrace_append hprefix tailTrace_1790189
  have hstable : (prefixWord ++ tailWord_1790189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790189).length < 2 ^ (prefixWord ++ tailWord_1790189).sum := by decide
  have hdescent : baseEnd_1790189 < baseStart_1790189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790217 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_1790217 : Nat := 118140960795 + 1790217 * 2 ^ 59
def prefixEnd_1790217 : Nat := 4983230072969 + 3 ^ 40 * 1790217 * 2
def baseEnd_1790217 : Nat := 408551909711167778424199

theorem tailTrace_1790217 : CollatzResearch.WordTrace tailWord_1790217 prefixEnd_1790217 408551909711167778424199 := by
  unfold tailWord_1790217
  simp only [CollatzResearch.WordTrace]
  refine ⟨65294578155357028567128905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43529718770238019044752603 65294578155357028567128905)
  ·
    refine ⟨48970933616517771425346679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65294578155357028567128905 48970933616517771425346679)
    ·
      refine ⟨73456400424776657138020019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48970933616517771425346679 73456400424776657138020019)
      ·
        refine ⟨110184600637164985707030029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73456400424776657138020019 110184600637164985707030029)
        ·
          refine ⟨41319225238936869640136261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110184600637164985707030029 41319225238936869640136261)
          ·
            refine ⟨7747354732300663057525549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41319225238936869640136261 7747354732300663057525549)
            ·
              refine ⟨2905258024612748646572081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7747354732300663057525549 2905258024612748646572081)
              ·
                refine ⟨2178943518459561484929061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905258024612748646572081 2178943518459561484929061)
                ·
                  refine ⟨408551909711167778424199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178943518459561484929061 408551909711167778424199)
                  ·
                    rfl

theorem cell21_1790217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_1790217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790217 prefixEnd_1790217 := by exact prefixLift 1790217
  have htrace : WordTrace (prefixWord ++ tailWord_1790217) baseStart_1790217 baseEnd_1790217 := by
    simpa [prefixWord, tailWord_1790217, baseEnd_1790217] using wordTrace_append hprefix tailTrace_1790217
  have hstable : (prefixWord ++ tailWord_1790217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790217).length < 2 ^ (prefixWord ++ tailWord_1790217).sum := by decide
  have hdescent : baseEnd_1790217 < baseStart_1790217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790248 : List Nat := [2, 1, 5, 1, 3, 1, 1, 7]
def baseStart_1790248 : Nat := 118140960795 + 1790248 * 2 ^ 59
def prefixEnd_1790248 : Nat := 4983230072969 + 3 ^ 40 * 1790248 * 2
def baseEnd_1790248 : Nat := 136186328111172871135823

theorem tailTrace_1790248 : CollatzResearch.WordTrace tailWord_1790248 prefixEnd_1790248 136186328111172871135823 := by
  unfold tailWord_1790248
  simp only [CollatzResearch.WordTrace]
  refine ⟨32647854409122360430753699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43530472545496480574338265 32647854409122360430753699)
  ·
    refine ⟨48971781613683540646130549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32647854409122360430753699 48971781613683540646130549)
    ·
      refine ⟨4591104526282831935574739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48971781613683540646130549 4591104526282831935574739)
      ·
        refine ⟨6886656789424247903362109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591104526282831935574739 6886656789424247903362109)
        ·
          refine ⟨2582496296034092963760791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6886656789424247903362109 2582496296034092963760791)
          ·
            refine ⟨3873744444051139445641187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582496296034092963760791 3873744444051139445641187)
            ·
              refine ⟨5810616666076709168461781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873744444051139445641187 5810616666076709168461781)
              ·
                refine ⟨136186328111172871135823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5810616666076709168461781 136186328111172871135823)
                ·
                  rfl

theorem cell21_1790248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_1790248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790248 prefixEnd_1790248 := by exact prefixLift 1790248
  have htrace : WordTrace (prefixWord ++ tailWord_1790248) baseStart_1790248 baseEnd_1790248 := by
    simpa [prefixWord, tailWord_1790248, baseEnd_1790248] using wordTrace_append hprefix tailTrace_1790248
  have hstable : (prefixWord ++ tailWord_1790248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790248).length < 2 ^ (prefixWord ++ tailWord_1790248).sum := by decide
  have hdescent : baseEnd_1790248 < baseStart_1790248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790254 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1790254 : Nat := 118140960795 + 1790254 * 2 ^ 59
def prefixEnd_1790254 : Nat := 4983230072969 + 3 ^ 40 * 1790254 * 2
def baseEnd_1790254 : Nat := 408560353615263936307457

theorem tailTrace_1790254 : CollatzResearch.WordTrace tailWord_1790254 prefixEnd_1790254 408560353615263936307457 := by
  unfold tailWord_1790254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161990957027872985778227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43530618437481989257483877 8161990957027872985778227)
  ·
    refine ⟨12242986435541809478667341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161990957027872985778227 12242986435541809478667341)
    ·
      refine ⟨4591119913328178554500253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12242986435541809478667341 4591119913328178554500253)
      ·
        refine ⟨1721669967498066957937595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4591119913328178554500253 1721669967498066957937595)
        ·
          refine ⟨2582504951247100436906393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721669967498066957937595 2582504951247100436906393)
          ·
            refine ⟨1936878713435325327679795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582504951247100436906393 1936878713435325327679795)
            ·
              refine ⟨2905318070152987991519693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936878713435325327679795 2905318070152987991519693)
              ·
                refine ⟨1089494276307370496819885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905318070152987991519693 1089494276307370496819885)
                ·
                  refine ⟨408560353615263936307457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089494276307370496819885 408560353615263936307457)
                  ·
                    rfl

theorem cell21_1790254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1790254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790254 prefixEnd_1790254 := by exact prefixLift 1790254
  have htrace : WordTrace (prefixWord ++ tailWord_1790254) baseStart_1790254 baseEnd_1790254 := by
    simpa [prefixWord, tailWord_1790254, baseEnd_1790254] using wordTrace_append hprefix tailTrace_1790254
  have hstable : (prefixWord ++ tailWord_1790254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790254).length < 2 ^ (prefixWord ++ tailWord_1790254).sum := by decide
  have hdescent : baseEnd_1790254 < baseStart_1790254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790431 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 3]
def baseStart_1790431 : Nat := 118140960795 + 1790431 * 2 ^ 59
def prefixEnd_1790431 : Nat := 4983230072969 + 3 ^ 40 * 1790431 * 2
def baseEnd_1790431 : Nat := 408600747426750961857095

theorem tailTrace_1790431 : CollatzResearch.WordTrace tailWord_1790431 prefixEnd_1790431 408600747426750961857095 := by
  unfold tailWord_1790431
  simp only [CollatzResearch.WordTrace]
  refine ⟨65302383376581743115419147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43534922251054495410279431 65302383376581743115419147)
  ·
    refine ⟨97953575064872614673128721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65302383376581743115419147 97953575064872614673128721)
    ·
      refine ⟨73465181298654461004846541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97953575064872614673128721 73465181298654461004846541)
      ·
        refine ⟨27549442986995422876817453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73465181298654461004846541 27549442986995422876817453)
        ·
          refine ⟨10331041120123283578806545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27549442986995422876817453 10331041120123283578806545)
          ·
            refine ⟨7748280840092462684104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331041120123283578806545 7748280840092462684104909)
            ·
              refine ⟨2905605315034673506539341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7748280840092462684104909 2905605315034673506539341)
              ·
                refine ⟨1089601993138002564952253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905605315034673506539341 1089601993138002564952253)
                ·
                  refine ⟨408600747426750961857095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089601993138002564952253 408600747426750961857095)
                  ·
                    rfl

theorem cell21_1790431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].length) (baseStart_1790431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790431 prefixEnd_1790431 := by exact prefixLift 1790431
  have htrace : WordTrace (prefixWord ++ tailWord_1790431) baseStart_1790431 baseEnd_1790431 := by
    simpa [prefixWord, tailWord_1790431, baseEnd_1790431] using wordTrace_append hprefix tailTrace_1790431
  have hstable : (prefixWord ++ tailWord_1790431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790431).length < 2 ^ (prefixWord ++ tailWord_1790431).sum := by decide
  have hdescent : baseEnd_1790431 < baseStart_1790431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790434 : List Nat := [3, 3, 3, 2, 2, 1, 7]
def baseStart_1790434 : Nat := 118140960795 + 1790434 * 2 ^ 59
def prefixEnd_1790434 : Nat := 4983230072969 + 3 ^ 40 * 1790434 * 2
def baseEnd_1790434 : Nat := 45400159118624847034121

theorem tailTrace_1790434 : CollatzResearch.WordTrace tailWord_1790434 prefixEnd_1790434 45400159118624847034121 := by
  unfold tailWord_1790434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325623198892718656944589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43534995197047249751852237 16325623198892718656944589)
  ·
    refine ⟨6122108699584769496354221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16325623198892718656944589 6122108699584769496354221)
    ·
      refine ⟨2295790762344288561132833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6122108699584769496354221 2295790762344288561132833)
      ·
        refine ⟨1721843071758216420849625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295790762344288561132833 1721843071758216420849625)
        ·
          refine ⟨1291382303818662315637219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721843071758216420849625 1291382303818662315637219)
          ·
            refine ⟨1937073455727993473455829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291382303818662315637219 1937073455727993473455829)
            ·
              refine ⟨45400159118624847034121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1937073455727993473455829 45400159118624847034121)
              ·
                rfl

theorem cell21_1790434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 7].length) (baseStart_1790434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790434 prefixEnd_1790434 := by exact prefixLift 1790434
  have htrace : WordTrace (prefixWord ++ tailWord_1790434) baseStart_1790434 baseEnd_1790434 := by
    simpa [prefixWord, tailWord_1790434, baseEnd_1790434] using wordTrace_append hprefix tailTrace_1790434
  have hstable : (prefixWord ++ tailWord_1790434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790434).length < 2 ^ (prefixWord ++ tailWord_1790434).sum := by decide
  have hdescent : baseEnd_1790434 < baseStart_1790434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790445 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1790445 : Nat := 118140960795 + 1790445 * 2 ^ 59
def prefixEnd_1790445 : Nat := 4983230072969 + 3 ^ 40 * 1790445 * 2
def baseEnd_1790445 : Nat := 408603942417490048623733

theorem tailTrace_1790445 : CollatzResearch.WordTrace tailWord_1790445 prefixEnd_1790445 408603942417490048623733 := by
  unfold tailWord_1790445
  simp only [CollatzResearch.WordTrace]
  refine ⟨65302893998531023506428789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43535262665687349004285859 65302893998531023506428789)
  ·
    refine ⟨6122146312362283453727699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65302893998531023506428789 6122146312362283453727699)
    ·
      refine ⟨9183219468543425180591549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6122146312362283453727699 9183219468543425180591549)
      ·
        refine ⟨3443707300703784442721831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9183219468543425180591549 3443707300703784442721831)
        ·
          refine ⟨5165560951055676664082747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443707300703784442721831 5165560951055676664082747)
          ·
            refine ⟨7748341426583514996124121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165560951055676664082747 7748341426583514996124121)
            ·
              refine ⟨5811256069937636247093091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748341426583514996124121 5811256069937636247093091)
              ·
                refine ⟨8716884104906454370639637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811256069937636247093091 8716884104906454370639637)
                ·
                  refine ⟨408603942417490048623733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8716884104906454370639637 408603942417490048623733)
                  ·
                    rfl

theorem cell21_1790445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1790445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790445 prefixEnd_1790445 := by exact prefixLift 1790445
  have htrace : WordTrace (prefixWord ++ tailWord_1790445) baseStart_1790445 baseEnd_1790445 := by
    simpa [prefixWord, tailWord_1790445, baseEnd_1790445] using wordTrace_append hprefix tailTrace_1790445
  have hstable : (prefixWord ++ tailWord_1790445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790445).length < 2 ^ (prefixWord ++ tailWord_1790445).sum := by decide
  have hdescent : baseEnd_1790445 < baseStart_1790445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790670 : List Nat := [4, 1, 1, 1, 3, 11]
def baseStart_1790670 : Nat := 118140960795 + 1790670 * 2 ^ 59
def prefixEnd_1790670 : Nat := 4983230072969 + 3 ^ 40 * 1790670 * 2
def baseEnd_1790670 : Nat := 15135381128997765087899

theorem tailTrace_1790670 : CollatzResearch.WordTrace tailWord_1790670 prefixEnd_1790670 15135381128997765087899 := by
  unfold tailWord_1790670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163887552839485866671183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43540733615143924622246309 8163887552839485866671183)
  ·
    refine ⟨12245831329259228800006775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163887552839485866671183 12245831329259228800006775)
    ·
      refine ⟨18368746993888843200010163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12245831329259228800006775 18368746993888843200010163)
      ·
        refine ⟨27553120490833264800015245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18368746993888843200010163 27553120490833264800015245)
        ·
          refine ⟨10332420184062474300005717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27553120490833264800015245 10332420184062474300005717)
          ·
            refine ⟨15135381128997765087899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10332420184062474300005717 15135381128997765087899)
            ·
              rfl

theorem cell21_1790670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 11].length) (baseStart_1790670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790670 prefixEnd_1790670 := by exact prefixLift 1790670
  have htrace : WordTrace (prefixWord ++ tailWord_1790670) baseStart_1790670 baseEnd_1790670 := by
    simpa [prefixWord, tailWord_1790670, baseEnd_1790670] using wordTrace_append hprefix tailTrace_1790670
  have hstable : (prefixWord ++ tailWord_1790670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790670).length < 2 ^ (prefixWord ++ tailWord_1790670).sum := by decide
  have hdescent : baseEnd_1790670 < baseStart_1790670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790676 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1790676 : Nat := 118140960795 + 1790676 * 2 ^ 59
def prefixEnd_1790676 : Nat := 4983230072969 + 3 ^ 40 * 1790676 * 2
def baseEnd_1790676 : Nat := 408656659764684980273261

theorem tailTrace_1790676 : CollatzResearch.WordTrace tailWord_1790676 prefixEnd_1790676 408656659764684980273261 := by
  unfold tailWord_1790676
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655659630347074979043941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43540879507129433305391921 32655659630347074979043941)
  ·
    refine ⟨6122936180690076558570739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32655659630347074979043941 6122936180690076558570739)
    ·
      refine ⟨9184404271035114837856109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6122936180690076558570739 9184404271035114837856109)
      ·
        refine ⟨3444151601638168064196041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9184404271035114837856109 3444151601638168064196041)
        ·
          refine ⟨2583113701228626048147031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444151601638168064196041 2583113701228626048147031)
          ·
            refine ⟨3874670551842939072220547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583113701228626048147031 3874670551842939072220547)
            ·
              refine ⟨5812005827764408608330821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874670551842939072220547 5812005827764408608330821)
              ·
                refine ⟨1089751092705826614062029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5812005827764408608330821 1089751092705826614062029)
                ·
                  refine ⟨408656659764684980273261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089751092705826614062029 408656659764684980273261)
                  ·
                    rfl

theorem cell21_1790676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1790676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790676 prefixEnd_1790676 := by exact prefixLift 1790676
  have htrace : WordTrace (prefixWord ++ tailWord_1790676) baseStart_1790676 baseEnd_1790676 := by
    simpa [prefixWord, tailWord_1790676, baseEnd_1790676] using wordTrace_append hprefix tailTrace_1790676
  have hstable : (prefixWord ++ tailWord_1790676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790676).length < 2 ^ (prefixWord ++ tailWord_1790676).sum := by decide
  have hdescent : baseEnd_1790676 < baseStart_1790676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790687 : List Nat := [1, 1, 2, 3, 2, 5, 1, 6]
def baseStart_1790687 : Nat := 118140960795 + 1790687 * 2 ^ 59
def prefixEnd_1790687 : Nat := 4983230072969 + 3 ^ 40 * 1790687 * 2
def baseEnd_1790687 : Nat := 136219723371517135196635

theorem tailTrace_1790687 : CollatzResearch.WordTrace tailWord_1790687 prefixEnd_1790687 136219723371517135196635 := by
  unfold tailWord_1790687
  simp only [CollatzResearch.WordTrace]
  refine ⟨65311720463654298836738315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43541146975769532557825543 65311720463654298836738315)
  ·
    refine ⟨97967580695481448255107473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65311720463654298836738315 97967580695481448255107473)
    ·
      refine ⟨73475685521611086191330605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97967580695481448255107473 73475685521611086191330605)
      ·
        refine ⟨27553382070604157321748977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73475685521611086191330605 27553382070604157321748977)
        ·
          refine ⟨20665036552953117991311733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27553382070604157321748977 20665036552953117991311733)
          ·
            refine ⟨1937347176839354811685475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20665036552953117991311733 1937347176839354811685475)
            ·
              refine ⟨2906020765259032217528213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937347176839354811685475 2906020765259032217528213)
              ·
                refine ⟨136219723371517135196635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906020765259032217528213 136219723371517135196635)
                ·
                  rfl

theorem cell21_1790687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_1790687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790687 prefixEnd_1790687 := by exact prefixLift 1790687
  have htrace : WordTrace (prefixWord ++ tailWord_1790687) baseStart_1790687 baseEnd_1790687 := by
    simpa [prefixWord, tailWord_1790687, baseEnd_1790687] using wordTrace_append hprefix tailTrace_1790687
  have hstable : (prefixWord ++ tailWord_1790687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790687).length < 2 ^ (prefixWord ++ tailWord_1790687).sum := by decide
  have hdescent : baseEnd_1790687 < baseStart_1790687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790746 : List Nat := [3, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1790746 : Nat := 118140960795 + 1790746 * 2 ^ 59
def prefixEnd_1790746 : Nat := 4983230072969 + 3 ^ 40 * 1790746 * 2
def baseEnd_1790746 : Nat := 136224211572793471368817

theorem tailTrace_1790746 : CollatzResearch.WordTrace tailWord_1790746 prefixEnd_1790746 136224211572793471368817 := by
  unfold tailWord_1790746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328468092610137978284023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43542581580293701275424061 16328468092610137978284023)
  ·
    refine ⟨24492702138915206967426035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16328468092610137978284023 24492702138915206967426035)
    ·
      refine ⟨36739053208372810451139053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492702138915206967426035 36739053208372810451139053)
      ·
        refine ⟨13777144953139803919177145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36739053208372810451139053 13777144953139803919177145)
        ·
          refine ⟨10332858714854852939382859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777144953139803919177145 10332858714854852939382859)
          ·
            refine ⟨15499288072282279409074289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332858714854852939382859 15499288072282279409074289)
            ·
              refine ⟨11624466054211709556805717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15499288072282279409074289 11624466054211709556805717)
              ·
                refine ⟨136224211572793471368817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11624466054211709556805717 136224211572793471368817)
                ·
                  rfl

theorem cell21_1790746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1790746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790746 prefixEnd_1790746 := by exact prefixLift 1790746
  have htrace : WordTrace (prefixWord ++ tailWord_1790746) baseStart_1790746 baseEnd_1790746 := by
    simpa [prefixWord, tailWord_1790746, baseEnd_1790746] using wordTrace_append hprefix tailTrace_1790746
  have hstable : (prefixWord ++ tailWord_1790746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790746).length < 2 ^ (prefixWord ++ tailWord_1790746).sum := by decide
  have hdescent : baseEnd_1790746 < baseStart_1790746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790932 : List Nat := [2, 4, 1, 2, 1, 4, 2, 5]
def baseStart_1790932 : Nat := 118140960795 + 1790932 * 2 ^ 59
def prefixEnd_1790932 : Nat := 4983230072969 + 3 ^ 40 * 1790932 * 2
def baseEnd_1790932 : Nat := 136238360817495141335357

theorem tailTrace_1790932 : CollatzResearch.WordTrace tailWord_1790932 prefixEnd_1790932 136238360817495141335357 := by
  unfold tailWord_1790932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660328173883352839703525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43547104231844470452938033 32660328173883352839703525)
  ·
    refine ⟨6123811532603128657444411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32660328173883352839703525 6123811532603128657444411)
    ·
      refine ⟨9185717298904692986166617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6123811532603128657444411 9185717298904692986166617)
      ·
        refine ⟨6889287974178519739624963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9185717298904692986166617 6889287974178519739624963)
        ·
          refine ⟨10333931961267779609437445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6889287974178519739624963 10333931961267779609437445)
          ·
            refine ⟨1937612242737708676769521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10333931961267779609437445 1937612242737708676769521)
            ·
              refine ⟨1453209182053281507577141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937612242737708676769521 1453209182053281507577141)
              ·
                refine ⟨136238360817495141335357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453209182053281507577141 136238360817495141335357)
                ·
                  rfl

theorem cell21_1790932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_1790932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790932 prefixEnd_1790932 := by exact prefixLift 1790932
  have htrace : WordTrace (prefixWord ++ tailWord_1790932) baseStart_1790932 baseEnd_1790932 := by
    simpa [prefixWord, tailWord_1790932, baseEnd_1790932] using wordTrace_append hprefix tailTrace_1790932
  have hstable : (prefixWord ++ tailWord_1790932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790932).length < 2 ^ (prefixWord ++ tailWord_1790932).sum := by decide
  have hdescent : baseEnd_1790932 < baseStart_1790932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790977 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 4]
def baseStart_1790977 : Nat := 118140960795 + 1790977 * 2 ^ 59
def prefixEnd_1790977 : Nat := 4983230072969 + 3 ^ 40 * 1790977 * 2
def baseEnd_1790977 : Nat := 408725352065575345755979

theorem tailTrace_1790977 : CollatzResearch.WordTrace tailWord_1790977 prefixEnd_1790977 408725352065575345755979 := by
  unfold tailWord_1790977
  simp only [CollatzResearch.WordTrace]
  refine ⟨65322297632603678364795185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43548198421735785576530123 65322297632603678364795185)
  ·
    refine ⟨48991723224452758773596389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65322297632603678364795185 48991723224452758773596389)
    ·
      refine ⟨9185948104584892270049323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48991723224452758773596389 9185948104584892270049323)
      ·
        refine ⟨13778922156877338405073985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9185948104584892270049323 13778922156877338405073985)
        ·
          refine ⟨10334191617658003803805489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13778922156877338405073985 10334191617658003803805489)
          ·
            refine ⟨7750643713243502852854117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10334191617658003803805489 7750643713243502852854117)
            ·
              refine ⟨1453245696233156784910147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7750643713243502852854117 1453245696233156784910147)
              ·
                refine ⟨2179868544349735177365221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453245696233156784910147 2179868544349735177365221)
                ·
                  refine ⟨408725352065575345755979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179868544349735177365221 408725352065575345755979)
                  ·
                    rfl

theorem cell21_1790977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_1790977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1790977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1790977 prefixEnd_1790977 := by exact prefixLift 1790977
  have htrace : WordTrace (prefixWord ++ tailWord_1790977) baseStart_1790977 baseEnd_1790977 := by
    simpa [prefixWord, tailWord_1790977, baseEnd_1790977] using wordTrace_append hprefix tailTrace_1790977
  have hstable : (prefixWord ++ tailWord_1790977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790977).length < 2 ^ (prefixWord ++ tailWord_1790977).sum := by decide
  have hdescent : baseEnd_1790977 < baseStart_1790977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791036 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_1791036 : Nat := 118140960795 + 1791036 * 2 ^ 59
def prefixEnd_1791036 : Nat := 4983230072969 + 3 ^ 40 * 1791036 * 2
def baseEnd_1791036 : Nat := 408738816669404354272525

theorem tailTrace_1791036 : CollatzResearch.WordTrace tailWord_1791036 prefixEnd_1791036 408738816669404354272525 := by
  unfold tailWord_1791036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662224769694965720596481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43549633026259954294128641 32662224769694965720596481)
  ·
    refine ⟨24496668577271224290447361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32662224769694965720596481 24496668577271224290447361)
    ·
      refine ⟨18372501432953418217835521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24496668577271224290447361 18372501432953418217835521)
      ·
        refine ⟨13779376074715063663376641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18372501432953418217835521 13779376074715063663376641)
        ·
          refine ⟨10334532056036297747532481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13779376074715063663376641 10334532056036297747532481)
          ·
            refine ⟨7750899042027223310649361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10334532056036297747532481 7750899042027223310649361)
            ·
              refine ⟨5813174281520417482987021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750899042027223310649361 5813174281520417482987021)
              ·
                refine ⟨2179940355570156556120133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813174281520417482987021 2179940355570156556120133)
                ·
                  refine ⟨408738816669404354272525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179940355570156556120133 408738816669404354272525)
                  ·
                    rfl

theorem cell21_1791036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_1791036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791036 prefixEnd_1791036 := by exact prefixLift 1791036
  have htrace : WordTrace (prefixWord ++ tailWord_1791036) baseStart_1791036 baseEnd_1791036 := by
    simpa [prefixWord, tailWord_1791036, baseEnd_1791036] using wordTrace_append hprefix tailTrace_1791036
  have hstable : (prefixWord ++ tailWord_1791036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791036).length < 2 ^ (prefixWord ++ tailWord_1791036).sum := by decide
  have hdescent : baseEnd_1791036 < baseStart_1791036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791064 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_1791064 : Nat := 118140960795 + 1791064 * 2 ^ 59
def prefixEnd_1791064 : Nat := 4983230072969 + 3 ^ 40 * 1791064 * 2
def baseEnd_1791064 : Nat := 408745206650882527805801

theorem tailTrace_1791064 : CollatzResearch.WordTrace tailWord_1791064 prefixEnd_1791064 408745206650882527805801 := by
  unfold tailWord_1791064
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662735391644246111606123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43550313855525661482141497 32662735391644246111606123)
  ·
    refine ⟨48994103087466369167409185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32662735391644246111606123 48994103087466369167409185)
    ·
      refine ⟨36745577315599776875556889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48994103087466369167409185 36745577315599776875556889)
      ·
        refine ⟨27559182986699832656667667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36745577315599776875556889 27559182986699832656667667)
        ·
          refine ⟨41338774480049748985001501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559182986699832656667667 41338774480049748985001501)
          ·
            refine ⟨15502040430018655869375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41338774480049748985001501 15502040430018655869375563)
            ·
              refine ⟨23253060645027983804063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15502040430018655869375563 23253060645027983804063345)
              ·
                refine ⟨17439795483770987853047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23253060645027983804063345 17439795483770987853047509)
                ·
                  refine ⟨408745206650882527805801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17439795483770987853047509 408745206650882527805801)
                  ·
                    rfl

theorem cell21_1791064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_1791064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791064 prefixEnd_1791064 := by exact prefixLift 1791064
  have htrace : WordTrace (prefixWord ++ tailWord_1791064) baseStart_1791064 baseEnd_1791064 := by
    simpa [prefixWord, tailWord_1791064, baseEnd_1791064] using wordTrace_append hprefix tailTrace_1791064
  have hstable : (prefixWord ++ tailWord_1791064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791064).length < 2 ^ (prefixWord ++ tailWord_1791064).sum := by decide
  have hdescent : baseEnd_1791064 < baseStart_1791064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791070 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1791070 : Nat := 118140960795 + 1791070 * 2 ^ 59
def prefixEnd_1791070 : Nat := 4983230072969 + 3 ^ 40 * 1791070 * 2
def baseEnd_1791070 : Nat := 408746575932627850705789

theorem tailTrace_1791070 : CollatzResearch.WordTrace tailWord_1791070 prefixEnd_1791070 408746575932627850705789 := by
  unfold tailWord_1791070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165711202658344405991333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43550459747511170165287109 8165711202658344405991333)
  ·
    refine ⟨1531070850498439576123375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8165711202658344405991333 1531070850498439576123375)
    ·
      refine ⟨2296606275747659364185063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531070850498439576123375 2296606275747659364185063)
      ·
        refine ⟨3444909413621489046277595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296606275747659364185063 3444909413621489046277595)
        ·
          refine ⟨5167364120432233569416393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444909413621489046277595 5167364120432233569416393)
          ·
            refine ⟨3875523090324175177062295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167364120432233569416393 3875523090324175177062295)
            ·
              refine ⟨5813284635486262765593443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875523090324175177062295 5813284635486262765593443)
              ·
                refine ⟨8719926953229394148390165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813284635486262765593443 8719926953229394148390165)
                ·
                  refine ⟨408746575932627850705789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8719926953229394148390165 408746575932627850705789)
                  ·
                    rfl

theorem cell21_1791070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1791070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791070 prefixEnd_1791070 := by exact prefixLift 1791070
  have htrace : WordTrace (prefixWord ++ tailWord_1791070) baseStart_1791070 baseEnd_1791070 := by
    simpa [prefixWord, tailWord_1791070, baseEnd_1791070] using wordTrace_append hprefix tailTrace_1791070
  have hstable : (prefixWord ++ tailWord_1791070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791070).length < 2 ^ (prefixWord ++ tailWord_1791070).sum := by decide
  have hdescent : baseEnd_1791070 < baseStart_1791070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791081 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_1791081 : Nat := 118140960795 + 1791081 * 2 ^ 59
def prefixEnd_1791081 : Nat := 4983230072969 + 3 ^ 40 * 1791081 * 2
def baseEnd_1791081 : Nat := 408749086282494276022433

theorem tailTrace_1791081 : CollatzResearch.WordTrace tailWord_1791081 prefixEnd_1791081 408749086282494276022433 := by
  unfold tailWord_1791081
  simp only [CollatzResearch.WordTrace]
  refine ⟨65326090824226904126581097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43550727216151269417720731 65326090824226904126581097)
  ·
    refine ⟨48994568118170178094935823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65326090824226904126581097 48994568118170178094935823)
    ·
      refine ⟨73491852177255267142403735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994568118170178094935823 73491852177255267142403735)
      ·
        refine ⟨110237778265882900713605603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73491852177255267142403735 110237778265882900713605603)
        ·
          refine ⟨165356667398824351070408405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110237778265882900713605603 165356667398824351070408405)
          ·
            refine ⟨3875546892159945728212697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165356667398824351070408405 3875546892159945728212697)
            ·
              refine ⟨2906660169119959296159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875546892159945728212697 2906660169119959296159523)
              ·
                refine ⟨4359990253679938944239285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906660169119959296159523 4359990253679938944239285)
                ·
                  refine ⟨408749086282494276022433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4359990253679938944239285 408749086282494276022433)
                  ·
                    rfl

theorem cell21_1791081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_1791081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791081 prefixEnd_1791081 := by exact prefixLift 1791081
  have htrace : WordTrace (prefixWord ++ tailWord_1791081) baseStart_1791081 baseEnd_1791081 := by
    simpa [prefixWord, tailWord_1791081, baseEnd_1791081] using wordTrace_append hprefix tailTrace_1791081
  have hstable : (prefixWord ++ tailWord_1791081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791081).length < 2 ^ (prefixWord ++ tailWord_1791081).sum := by decide
  have hdescent : baseEnd_1791081 < baseStart_1791081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791143 : List Nat := [1, 1, 6, 2, 1, 2, 2, 6]
def baseStart_1791143 : Nat := 118140960795 + 1791143 * 2 ^ 59
def prefixEnd_1791143 : Nat := 4983230072969 + 3 ^ 40 * 1791143 * 2
def baseEnd_1791143 : Nat := 136254411842398648662991

theorem tailTrace_1791143 : CollatzResearch.WordTrace tailWord_1791143 prefixEnd_1791143 136254411842398648662991 := by
  unfold tailWord_1791143
  simp only [CollatzResearch.WordTrace]
  refine ⟨65328352150002288715338083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43552234766668192476892055 65328352150002288715338083)
  ·
    refine ⟨97992528225003433073007125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65328352150002288715338083 97992528225003433073007125)
    ·
      refine ⟨4593399760547035925297209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97992528225003433073007125 4593399760547035925297209)
      ·
        refine ⟨3445049820410276943972907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4593399760547035925297209 3445049820410276943972907)
        ·
          refine ⟨5167574730615415415959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445049820410276943972907 5167574730615415415959361)
          ·
            refine ⟨3875681047961561561969521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167574730615415415959361 3875681047961561561969521)
            ·
              refine ⟨2906760785971171171477141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875681047961561561969521 2906760785971171171477141)
              ·
                refine ⟨136254411842398648662991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906760785971171171477141 136254411842398648662991)
                ·
                  rfl

theorem cell21_1791143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_1791143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791143 prefixEnd_1791143 := by exact prefixLift 1791143
  have htrace : WordTrace (prefixWord ++ tailWord_1791143) baseStart_1791143 baseEnd_1791143 := by
    simpa [prefixWord, tailWord_1791143, baseEnd_1791143] using wordTrace_append hprefix tailTrace_1791143
  have hstable : (prefixWord ++ tailWord_1791143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791143).length < 2 ^ (prefixWord ++ tailWord_1791143).sum := by decide
  have hdescent : baseEnd_1791143 < baseStart_1791143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791146 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_1791146 : Nat := 118140960795 + 1791146 * 2 ^ 59
def prefixEnd_1791146 : Nat := 4983230072969 + 3 ^ 40 * 1791146 * 2
def baseEnd_1791146 : Nat := 408763920168068607438967

theorem tailTrace_1791146 : CollatzResearch.WordTrace tailWord_1791146 prefixEnd_1791146 408763920168068607438967 := by
  unfold tailWord_1791146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332115392247855056924323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43552307712660946818464861 16332115392247855056924323)
  ·
    refine ⟨24498173088371782585386485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16332115392247855056924323 24498173088371782585386485)
    ·
      refine ⟨2296703727034854617379983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24498173088371782585386485 2296703727034854617379983)
      ·
        refine ⟨3445055590552281926069975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296703727034854617379983 3445055590552281926069975)
        ·
          refine ⟨5167583385828422889104963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445055590552281926069975 5167583385828422889104963)
          ·
            refine ⟨7751375078742634333657445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167583385828422889104963 7751375078742634333657445)
            ·
              refine ⟨1453382827264243937560771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7751375078742634333657445 1453382827264243937560771)
              ·
                refine ⟨2180074240896365906341157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453382827264243937560771 2180074240896365906341157)
                ·
                  refine ⟨408763920168068607438967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180074240896365906341157 408763920168068607438967)
                  ·
                    rfl

theorem cell21_1791146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_1791146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791146 prefixEnd_1791146 := by exact prefixLift 1791146
  have htrace : WordTrace (prefixWord ++ tailWord_1791146) baseStart_1791146 baseEnd_1791146 := by
    simpa [prefixWord, tailWord_1791146, baseEnd_1791146] using wordTrace_append hprefix tailTrace_1791146
  have hstable : (prefixWord ++ tailWord_1791146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791146).length < 2 ^ (prefixWord ++ tailWord_1791146).sum := by decide
  have hdescent : baseEnd_1791146 < baseStart_1791146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791388 : List Nat := [2, 2, 3, 4, 1, 1, 3, 5]
def baseStart_1791388 : Nat := 118140960795 + 1791388 * 2 ^ 59
def prefixEnd_1791388 : Nat := 4983230072969 + 3 ^ 40 * 1791388 * 2
def baseEnd_1791388 : Nat := 136273049288376654801713

theorem tailTrace_1791388 : CollatzResearch.WordTrace tailWord_1791388 prefixEnd_1791388 136273049288376654801713 := by
  unfold tailWord_1791388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32668644017057347779003409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43558192022743130372004545 32668644017057347779003409)
  ·
    refine ⟨24501483012793010834252557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32668644017057347779003409 24501483012793010834252557)
    ·
      refine ⟨9188056129797379062844709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24501483012793010834252557 9188056129797379062844709)
      ·
        refine ⟨1722760524337008574283383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9188056129797379062844709 1722760524337008574283383)
        ·
          refine ⟨2584140786505512861425075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722760524337008574283383 2584140786505512861425075)
          ·
            refine ⟨3876211179758269292137613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584140786505512861425075 3876211179758269292137613)
            ·
              refine ⟨1453579192409350984551605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3876211179758269292137613 1453579192409350984551605)
              ·
                refine ⟨136273049288376654801713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453579192409350984551605 136273049288376654801713)
                ·
                  rfl

theorem cell21_1791388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_1791388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791388 prefixEnd_1791388 := by exact prefixLift 1791388
  have htrace : WordTrace (prefixWord ++ tailWord_1791388) baseStart_1791388 baseEnd_1791388 := by
    simpa [prefixWord, tailWord_1791388, baseEnd_1791388] using wordTrace_append hprefix tailTrace_1791388
  have hstable : (prefixWord ++ tailWord_1791388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791388).length < 2 ^ (prefixWord ++ tailWord_1791388).sum := by decide
  have hdescent : baseEnd_1791388 < baseStart_1791388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791399 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_1791399 : Nat := 118140960795 + 1791399 * 2 ^ 59
def prefixEnd_1791399 : Nat := 4983230072969 + 3 ^ 40 * 1791399 * 2
def baseEnd_1791399 : Nat := 408821658214996389721783

theorem tailTrace_1791399 : CollatzResearch.WordTrace tailWord_1791399 prefixEnd_1791399 408821658214996389721783 := by
  unfold tailWord_1791399
  simp only [CollatzResearch.WordTrace]
  refine ⟨65337689237074844436657251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43558459491383229624438167 65337689237074844436657251)
  ·
    refine ⟨98006533855612266654985877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65337689237074844436657251 98006533855612266654985877)
    ·
      refine ⟨4594056274481824999452463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98006533855612266654985877 4594056274481824999452463)
      ·
        refine ⟨6891084411722737499178695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594056274481824999452463 6891084411722737499178695)
        ·
          refine ⟨10336626617584106248768043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891084411722737499178695 10336626617584106248768043)
          ·
            refine ⟨15504939926376159373152065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336626617584106248768043 15504939926376159373152065)
            ·
              refine ⟨11628704944782119529864049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504939926376159373152065 11628704944782119529864049)
              ·
                refine ⟨8721528708586589647398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11628704944782119529864049 8721528708586589647398037)
                ·
                  refine ⟨408821658214996389721783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8721528708586589647398037 408821658214996389721783)
                  ·
                    rfl

theorem cell21_1791399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_1791399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791399 prefixEnd_1791399 := by exact prefixLift 1791399
  have htrace : WordTrace (prefixWord ++ tailWord_1791399) baseStart_1791399 baseEnd_1791399 := by
    simpa [prefixWord, tailWord_1791399, baseEnd_1791399] using wordTrace_append hprefix tailTrace_1791399
  have hstable : (prefixWord ++ tailWord_1791399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791399).length < 2 ^ (prefixWord ++ tailWord_1791399).sum := by decide
  have hdescent : baseEnd_1791399 < baseStart_1791399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791478 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1791478 : Nat := 118140960795 + 1791478 * 2 ^ 59
def prefixEnd_1791478 : Nat := 4983230072969 + 3 ^ 40 * 1791478 * 2
def baseEnd_1791478 : Nat := 408839687091309807904955

theorem tailTrace_1791478 : CollatzResearch.WordTrace tailWord_1791478 prefixEnd_1791478 408839687091309807904955 := by
  unfold tailWord_1791478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083785662736790058048943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43560380402525760619188725 4083785662736790058048943)
  ·
    refine ⟨6125678494105185087073415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4083785662736790058048943 6125678494105185087073415)
    ·
      refine ⟨9188517741157777630610123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125678494105185087073415 9188517741157777630610123)
      ·
        refine ⟨13782776611736666445915185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188517741157777630610123 13782776611736666445915185)
        ·
          refine ⟨10337082458802499834436389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13782776611736666445915185 10337082458802499834436389)
          ·
            refine ⟨1938202961025468718956823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10337082458802499834436389 1938202961025468718956823)
            ·
              refine ⟨2907304441538203078435235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938202961025468718956823 2907304441538203078435235)
              ·
                refine ⟨4360956662307304617652853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907304441538203078435235 4360956662307304617652853)
                ·
                  refine ⟨408839687091309807904955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4360956662307304617652853 408839687091309807904955)
                  ·
                    rfl

theorem cell21_1791478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1791478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791478 prefixEnd_1791478 := by exact prefixLift 1791478
  have htrace : WordTrace (prefixWord ++ tailWord_1791478) baseStart_1791478 baseEnd_1791478 := by
    simpa [prefixWord, tailWord_1791478, baseEnd_1791478] using wordTrace_append hprefix tailTrace_1791478
  have hstable : (prefixWord ++ tailWord_1791478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791478).length < 2 ^ (prefixWord ++ tailWord_1791478).sum := by decide
  have hdescent : baseEnd_1791478 < baseStart_1791478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791551 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_1791551 : Nat := 118140960795 + 1791551 * 2 ^ 59
def prefixEnd_1791551 : Nat := 4983230072969 + 3 ^ 40 * 1791551 * 2
def baseEnd_1791551 : Nat := 408856346685877903188139

theorem tailTrace_1791551 : CollatzResearch.WordTrace tailWord_1791551 prefixEnd_1791551 408856346685877903188139 := by
  unfold tailWord_1791551
  simp only [CollatzResearch.WordTrace]
  refine ⟨65343233132524174396190507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43562155421682782930793671 65343233132524174396190507)
  ·
    refine ⟨98014849698786261594285761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65343233132524174396190507 98014849698786261594285761)
    ·
      refine ⟨73511137274089696195714321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98014849698786261594285761 73511137274089696195714321)
      ·
        refine ⟨55133352955567272146785741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73511137274089696195714321 55133352955567272146785741)
        ·
          refine ⟨20675007358337727055044653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55133352955567272146785741 20675007358337727055044653)
          ·
            refine ⟨7753127759376647645641745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20675007358337727055044653 7753127759376647645641745)
            ·
              refine ⟨5814845819532485734231309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753127759376647645641745 5814845819532485734231309)
              ·
                refine ⟨2180567182324682150336741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5814845819532485734231309 2180567182324682150336741)
                ·
                  refine ⟨408856346685877903188139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180567182324682150336741 408856346685877903188139)
                  ·
                    rfl

theorem cell21_1791551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_1791551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791551 prefixEnd_1791551 := by exact prefixLift 1791551
  have htrace : WordTrace (prefixWord ++ tailWord_1791551) baseStart_1791551 baseEnd_1791551 := by
    simpa [prefixWord, tailWord_1791551, baseEnd_1791551] using wordTrace_append hprefix tailTrace_1791551
  have hstable : (prefixWord ++ tailWord_1791551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791551).length < 2 ^ (prefixWord ++ tailWord_1791551).sum := by decide
  have hdescent : baseEnd_1791551 < baseStart_1791551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791630 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1791630 : Nat := 118140960795 + 1791630 * 2 ^ 59
def prefixEnd_1791630 : Nat := 4983230072969 + 3 ^ 40 * 1791630 * 2
def baseEnd_1791630 : Nat := 408874375562191321371311

theorem tailTrace_1791630 : CollatzResearch.WordTrace tailWord_1791630 prefixEnd_1791630 408874375562191321371311 := by
  unfold tailWord_1791630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168264312404746361039543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43564076332825313925544229 8168264312404746361039543)
  ·
    refine ⟨12252396468607119541559315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8168264312404746361039543 12252396468607119541559315)
    ·
      refine ⟨18378594702910679312338973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252396468607119541559315 18378594702910679312338973)
      ·
        refine ⟨6891973013591504742127115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18378594702910679312338973 6891973013591504742127115)
        ·
          refine ⟨10337959520387257113190673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891973013591504742127115 10337959520387257113190673)
          ·
            refine ⟨7753469640290442834893005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337959520387257113190673 7753469640290442834893005)
            ·
              refine ⟨2907551115108916063084877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7753469640290442834893005 2907551115108916063084877)
              ·
                refine ⟨1090331668165843523656829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2907551115108916063084877 1090331668165843523656829)
                ·
                  refine ⟨408874375562191321371311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090331668165843523656829 408874375562191321371311)
                  ·
                    rfl

theorem cell21_1791630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1791630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791630 prefixEnd_1791630 := by exact prefixLift 1791630
  have htrace : WordTrace (prefixWord ++ tailWord_1791630) baseStart_1791630 baseEnd_1791630 := by
    simpa [prefixWord, tailWord_1791630, baseEnd_1791630] using wordTrace_append hprefix tailTrace_1791630
  have hstable : (prefixWord ++ tailWord_1791630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791630).length < 2 ^ (prefixWord ++ tailWord_1791630).sum := by decide
  have hdescent : baseEnd_1791630 < baseStart_1791630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791647 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 5]
def baseStart_1791647 : Nat := 118140960795 + 1791647 * 2 ^ 59
def prefixEnd_1791647 : Nat := 4983230072969 + 3 ^ 40 * 1791647 * 2
def baseEnd_1791647 : Nat := 408878255193803069587943

theorem tailTrace_1791647 : CollatzResearch.WordTrace tailWord_1791647 prefixEnd_1791647 408878255193803069587943 := by
  unfold tailWord_1791647
  simp only [CollatzResearch.WordTrace]
  refine ⟨65346734540176382791685195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43564489693450921861123463 65346734540176382791685195)
  ·
    refine ⟨98020101810264574187527793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65346734540176382791685195 98020101810264574187527793)
    ·
      refine ⟨73515076357698430640645845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98020101810264574187527793 73515076357698430640645845)
      ·
        refine ⟨1723009602133556968140137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73515076357698430640645845 1723009602133556968140137)
        ·
          refine ⟨1292257201600167726105103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723009602133556968140137 1292257201600167726105103)
          ·
            refine ⟨1938385802400251589157655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292257201600167726105103 1938385802400251589157655)
            ·
              refine ⟨2907578703600377383736483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938385802400251589157655 2907578703600377383736483)
              ·
                refine ⟨4361368055400566075604725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907578703600377383736483 4361368055400566075604725)
                ·
                  refine ⟨408878255193803069587943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361368055400566075604725 408878255193803069587943)
                  ·
                    rfl

theorem cell21_1791647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].length) (baseStart_1791647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791647 prefixEnd_1791647 := by exact prefixLift 1791647
  have htrace : WordTrace (prefixWord ++ tailWord_1791647) baseStart_1791647 baseEnd_1791647 := by
    simpa [prefixWord, tailWord_1791647, baseEnd_1791647] using wordTrace_append hprefix tailTrace_1791647
  have hstable : (prefixWord ++ tailWord_1791647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791647).length < 2 ^ (prefixWord ++ tailWord_1791647).sum := by decide
  have hdescent : baseEnd_1791647 < baseStart_1791647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791703 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_1791703 : Nat := 118140960795 + 1791703 * 2 ^ 59
def prefixEnd_1791703 : Nat := 4983230072969 + 3 ^ 40 * 1791703 * 2
def baseEnd_1791703 : Nat := 408891035156759416654495

theorem tailTrace_1791703 : CollatzResearch.WordTrace tailWord_1791703 prefixEnd_1791703 408891035156759416654495 := by
  unfold tailWord_1791703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65348777027973504355723763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43565851351982336237149175 65348777027973504355723763)
  ·
    refine ⟨98023165541960256533585645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65348777027973504355723763 98023165541960256533585645)
    ·
      refine ⟨36758687078235096200094617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98023165541960256533585645 36758687078235096200094617)
      ·
        refine ⟨27569015308676322150070963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36758687078235096200094617 27569015308676322150070963)
        ·
          refine ⟨41353522963014483225106445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27569015308676322150070963 41353522963014483225106445)
          ·
            refine ⟨15507571111130431209414917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41353522963014483225106445 15507571111130431209414917)
            ·
              refine ⟨2907669583336955851765297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15507571111130431209414917 2907669583336955851765297)
              ·
                refine ⟨2180752187502716888823973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907669583336955851765297 2180752187502716888823973)
                ·
                  refine ⟨408891035156759416654495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180752187502716888823973 408891035156759416654495)
                  ·
                    rfl

theorem cell21_1791703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_1791703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791703 prefixEnd_1791703 := by exact prefixLift 1791703
  have htrace : WordTrace (prefixWord ++ tailWord_1791703) baseStart_1791703 baseEnd_1791703 := by
    simpa [prefixWord, tailWord_1791703, baseEnd_1791703] using wordTrace_append hprefix tailTrace_1791703
  have hstable : (prefixWord ++ tailWord_1791703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791703).length < 2 ^ (prefixWord ++ tailWord_1791703).sum := by decide
  have hdescent : baseEnd_1791703 < baseStart_1791703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791706 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1791706 : Nat := 118140960795 + 1791706 * 2 ^ 59
def prefixEnd_1791706 : Nat := 4983230072969 + 3 ^ 40 * 1791706 * 2
def baseEnd_1791706 : Nat := 408891719797632078104489

theorem tailTrace_1791706 : CollatzResearch.WordTrace tailWord_1791706 prefixEnd_1791706 408891719797632078104489 := by
  unfold tailWord_1791706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337221611740658967020743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43565924297975090578721981 16337221611740658967020743)
  ·
    refine ⟨24505832417610988450531115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16337221611740658967020743 24505832417610988450531115)
    ·
      refine ⟨36758748626416482675796673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24505832417610988450531115 36758748626416482675796673)
      ·
        refine ⟨27569061469812362006847505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36758748626416482675796673 27569061469812362006847505)
        ·
          refine ⟨20676796102359271505135629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569061469812362006847505 20676796102359271505135629)
          ·
            refine ⟨7753798538384726814425861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20676796102359271505135629 7753798538384726814425861)
            ·
              refine ⟨1453837225947136277704849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7753798538384726814425861 1453837225947136277704849)
              ·
                refine ⟨1090377919460352208278637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453837225947136277704849 1090377919460352208278637)
                ·
                  refine ⟨408891719797632078104489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090377919460352208278637 408891719797632078104489)
                  ·
                    rfl

theorem cell21_1791706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1791706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791706 prefixEnd_1791706 := by exact prefixLift 1791706
  have htrace : WordTrace (prefixWord ++ tailWord_1791706) baseStart_1791706 baseEnd_1791706 := by
    simpa [prefixWord, tailWord_1791706, baseEnd_1791706] using wordTrace_append hprefix tailTrace_1791706
  have hstable : (prefixWord ++ tailWord_1791706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791706).length < 2 ^ (prefixWord ++ tailWord_1791706).sum := by decide
  have hdescent : baseEnd_1791706 < baseStart_1791706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791731 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_1791731 : Nat := 118140960795 + 1791731 * 2 ^ 59
def prefixEnd_1791731 : Nat := 4983230072969 + 3 ^ 40 * 1791731 * 2
def baseEnd_1791731 : Nat := 408897425138237590187771

theorem tailTrace_1791731 : CollatzResearch.WordTrace tailWord_1791731 prefixEnd_1791731 408897425138237590187771 := by
  unfold tailWord_1791731
  simp only [CollatzResearch.WordTrace]
  refine ⟨65349798271872065137743047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43566532181248043425162031 65349798271872065137743047)
  ·
    refine ⟨98024697407808097706614571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65349798271872065137743047 98024697407808097706614571)
    ·
      refine ⟨147037046111712146559921857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98024697407808097706614571 147037046111712146559921857)
      ·
        refine ⟨110277784583784109919941393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147037046111712146559921857 110277784583784109919941393)
        ·
          refine ⟨82708338437838082439956045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110277784583784109919941393 82708338437838082439956045)
          ·
            refine ⟨31015626914189280914983517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82708338437838082439956045 31015626914189280914983517)
            ·
              refine ⟨11630860092820980343118819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31015626914189280914983517 11630860092820980343118819)
              ·
                refine ⟨17446290139231470514678229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630860092820980343118819 17446290139231470514678229)
                ·
                  refine ⟨408897425138237590187771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17446290139231470514678229 408897425138237590187771)
                  ·
                    rfl

theorem cell21_1791731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_1791731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791731 prefixEnd_1791731 := by exact prefixLift 1791731
  have htrace : WordTrace (prefixWord ++ tailWord_1791731) baseStart_1791731 baseEnd_1791731 := by
    simpa [prefixWord, tailWord_1791731, baseEnd_1791731] using wordTrace_append hprefix tailTrace_1791731
  have hstable : (prefixWord ++ tailWord_1791731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791731).length < 2 ^ (prefixWord ++ tailWord_1791731).sum := by decide
  have hdescent : baseEnd_1791731 < baseStart_1791731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791765 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 3]
def baseStart_1791765 : Nat := 118140960795 + 1791765 * 2 ^ 59
def prefixEnd_1791765 : Nat := 4983230072969 + 3 ^ 40 * 1791765 * 2
def baseEnd_1791765 : Nat := 408905184401461086621035

theorem tailTrace_1791765 : CollatzResearch.WordTrace tailWord_1791765 prefixEnd_1791765 408905184401461086621035 := by
  unfold tailWord_1791765
  simp only [CollatzResearch.WordTrace]
  refine ⟨65351038353748888944480749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43567358902499259296320499 65351038353748888944480749)
  ·
    refine ⟨24506639382655833354180281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65351038353748888944480749 24506639382655833354180281)
    ·
      refine ⟨18379979536991875015635211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24506639382655833354180281 18379979536991875015635211)
      ·
        refine ⟨27569969305487812523452817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18379979536991875015635211 27569969305487812523452817)
        ·
          refine ⟨20677476979115859392589613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569969305487812523452817 20677476979115859392589613)
          ·
            refine ⟨7754053867168447272221105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20677476979115859392589613 7754053867168447272221105)
            ·
              refine ⟨5815540400376335454165829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754053867168447272221105 5815540400376335454165829)
              ·
                refine ⟨1090413825070562897656093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5815540400376335454165829 1090413825070562897656093)
                ·
                  refine ⟨408905184401461086621035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090413825070562897656093 408905184401461086621035)
                  ·
                    rfl

theorem cell21_1791765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_1791765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791765 prefixEnd_1791765 := by exact prefixLift 1791765
  have htrace : WordTrace (prefixWord ++ tailWord_1791765) baseStart_1791765 baseEnd_1791765 := by
    simpa [prefixWord, tailWord_1791765, baseEnd_1791765] using wordTrace_append hprefix tailTrace_1791765
  have hstable : (prefixWord ++ tailWord_1791765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791765).length < 2 ^ (prefixWord ++ tailWord_1791765).sum := by decide
  have hdescent : baseEnd_1791765 < baseStart_1791765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791793 : List Nat := [1, 2, 2, 3, 2, 3, 1, 7]
def baseStart_1791793 : Nat := 118140960795 + 1791793 * 2 ^ 59
def prefixEnd_1791793 : Nat := 4983230072969 + 3 ^ 40 * 1791793 * 2
def baseEnd_1791793 : Nat := 136303858127646420051437

theorem tailTrace_1791793 : CollatzResearch.WordTrace tailWord_1791793 prefixEnd_1791793 136303858127646420051437 := by
  unfold tailWord_1791793
  simp only [CollatzResearch.WordTrace]
  refine ⟨65352059597647449726500033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43568039731764966484333355 65352059597647449726500033)
  ·
    refine ⟨49014044698235587294875025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65352059597647449726500033 49014044698235587294875025)
    ·
      refine ⟨36760533523676690471156269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49014044698235587294875025 36760533523676690471156269)
      ·
        refine ⟨13785200071378758926683601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36760533523676690471156269 13785200071378758926683601)
        ·
          refine ⟨10338900053534069195012701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13785200071378758926683601 10338900053534069195012701)
          ·
            refine ⟨3877087520075275948129763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10338900053534069195012701 3877087520075275948129763)
            ·
              refine ⟨5815631280112913922194645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877087520075275948129763 5815631280112913922194645)
              ·
                refine ⟨136303858127646420051437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5815631280112913922194645 136303858127646420051437)
                ·
                  rfl

theorem cell21_1791793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_1791793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791793 prefixEnd_1791793 := by exact prefixLift 1791793
  have htrace : WordTrace (prefixWord ++ tailWord_1791793) baseStart_1791793 baseEnd_1791793 := by
    simpa [prefixWord, tailWord_1791793, baseEnd_1791793] using wordTrace_append hprefix tailTrace_1791793
  have hstable : (prefixWord ++ tailWord_1791793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791793).length < 2 ^ (prefixWord ++ tailWord_1791793).sum := by decide
  have hdescent : baseEnd_1791793 < baseStart_1791793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791883 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_1791883 : Nat := 118140960795 + 1791883 * 2 ^ 59
def prefixEnd_1791883 : Nat := 4983230072969 + 3 ^ 40 * 1791883 * 2
def baseEnd_1791883 : Nat := 408932113609119103654127

theorem tailTrace_1791883 : CollatzResearch.WordTrace tailWord_1791883 prefixEnd_1791883 408932113609119103654127 := by
  unfold tailWord_1791883
  simp only [CollatzResearch.WordTrace]
  refine ⟨65355342167321395097276303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43570228111547596731517535 65355342167321395097276303)
  ·
    refine ⟨98033013250982092645914455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65355342167321395097276303 98033013250982092645914455)
    ·
      refine ⟨147049519876473138968871683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98033013250982092645914455 147049519876473138968871683)
      ·
        refine ⟨220574279814709708453307525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147049519876473138968871683 220574279814709708453307525)
        ·
          refine ⟨41357677465258070334995161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220574279814709708453307525 41357677465258070334995161)
          ·
            refine ⟨31018258098943552751246371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41357677465258070334995161 31018258098943552751246371)
            ·
              refine ⟨46527387148415329126869557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31018258098943552751246371 46527387148415329126869557)
              ·
                refine ⟨4361942545163937105644021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46527387148415329126869557 4361942545163937105644021)
                ·
                  refine ⟨408932113609119103654127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361942545163937105644021 408932113609119103654127)
                  ·
                    rfl

theorem cell21_1791883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_1791883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791883 prefixEnd_1791883 := by exact prefixLift 1791883
  have htrace : WordTrace (prefixWord ++ tailWord_1791883) baseStart_1791883 baseEnd_1791883 := by
    simpa [prefixWord, tailWord_1791883, baseEnd_1791883] using wordTrace_append hprefix tailTrace_1791883
  have hstable : (prefixWord ++ tailWord_1791883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791883).length < 2 ^ (prefixWord ++ tailWord_1791883).sum := by decide
  have hdescent : baseEnd_1791883 < baseStart_1791883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791900 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1791900 : Nat := 118140960795 + 1791900 * 2 ^ 59
def prefixEnd_1791900 : Nat := 4983230072969 + 3 ^ 40 * 1791900 * 2
def baseEnd_1791900 : Nat := 408935993240730851870759

theorem tailTrace_1791900 : CollatzResearch.WordTrace tailWord_1791900 prefixEnd_1791900 408935993240730851870759 := by
  unfold tailWord_1791900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32677981104129903500322577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43570641472173204667096769 32677981104129903500322577)
  ·
    refine ⟨24508485828097427625241933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32677981104129903500322577 24508485828097427625241933)
    ·
      refine ⟨9190682185536535359465725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24508485828097427625241933 9190682185536535359465725)
      ·
        refine ⟨3446505819576200759799647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9190682185536535359465725 3446505819576200759799647)
        ·
          refine ⟨5169758729364301139699471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446505819576200759799647 5169758729364301139699471)
          ·
            refine ⟨7754638094046451709549207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169758729364301139699471 7754638094046451709549207)
            ·
              refine ⟨11631957141069677564323811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754638094046451709549207 11631957141069677564323811)
              ·
                refine ⟨17447935711604516346485717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11631957141069677564323811 17447935711604516346485717)
                ·
                  refine ⟨408935993240730851870759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17447935711604516346485717 408935993240730851870759)
                  ·
                    rfl

theorem cell21_1791900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1791900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791900 prefixEnd_1791900 := by exact prefixLift 1791900
  have htrace : WordTrace (prefixWord ++ tailWord_1791900) baseStart_1791900 baseEnd_1791900 := by
    simpa [prefixWord, tailWord_1791900, baseEnd_1791900] using wordTrace_append hprefix tailTrace_1791900
  have hstable : (prefixWord ++ tailWord_1791900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791900).length < 2 ^ (prefixWord ++ tailWord_1791900).sum := by decide
  have hdescent : baseEnd_1791900 < baseStart_1791900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791928 : List Nat := [2, 1, 2, 1, 2, 3, 10]
def baseStart_1791928 : Nat := 118140960795 + 1791928 * 2 ^ 59
def prefixEnd_1791928 : Nat := 4983230072969 + 3 ^ 40 * 1791928 * 2
def baseEnd_1791928 : Nat := 45438042580245447267115

theorem tailTrace_1791928 : CollatzResearch.WordTrace tailWord_1791928 prefixEnd_1791928 45438042580245447267115 := by
  unfold tailWord_1791928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32678491726079183891332219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43571322301438911855109625 32678491726079183891332219)
  ·
    refine ⟨49017737589118775836998329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32678491726079183891332219 49017737589118775836998329)
    ·
      refine ⟨36763303191839081877748747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49017737589118775836998329 36763303191839081877748747)
      ·
        refine ⟨55144954787758622816623121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36763303191839081877748747 55144954787758622816623121)
        ·
          refine ⟨41358716090818967112467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55144954787758622816623121 41358716090818967112467341)
          ·
            refine ⟨15509518534057112667175253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41358716090818967112467341 15509518534057112667175253)
            ·
              refine ⟨45438042580245447267115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15509518534057112667175253 45438042580245447267115)
              ·
                rfl

theorem cell21_1791928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 10].length) (baseStart_1791928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791928 prefixEnd_1791928 := by exact prefixLift 1791928
  have htrace : WordTrace (prefixWord ++ tailWord_1791928) baseStart_1791928 baseEnd_1791928 := by
    simpa [prefixWord, tailWord_1791928, baseEnd_1791928] using wordTrace_append hprefix tailTrace_1791928
  have hstable : (prefixWord ++ tailWord_1791928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791928).length < 2 ^ (prefixWord ++ tailWord_1791928).sum := by decide
  have hdescent : baseEnd_1791928 < baseStart_1791928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791948 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1791948 : Nat := 118140960795 + 1791948 * 2 ^ 59
def prefixEnd_1791948 : Nat := 4983230072969 + 3 ^ 40 * 1791948 * 2
def baseEnd_1791948 : Nat := 408946947494693435070661

theorem tailTrace_1791948 : CollatzResearch.WordTrace tailWord_1791948 prefixEnd_1791948 408946947494693435070661 := by
  unfold tailWord_1791948
  simp only [CollatzResearch.WordTrace]
  refine ⟨32678856456042955599196249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43571808608057274132261665 32678856456042955599196249)
  ·
    refine ⟨24509142342032216699397187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32678856456042955599196249 24509142342032216699397187)
    ·
      refine ⟨36763713513048325049095781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24509142342032216699397187 36763713513048325049095781)
      ·
        refine ⟨6893196283696560946705459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36763713513048325049095781 6893196283696560946705459)
        ·
          refine ⟨10339794425544841420058189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893196283696560946705459 10339794425544841420058189)
          ·
            refine ⟨3877422909579315532521821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10339794425544841420058189 3877422909579315532521821)
            ·
              refine ⟨1454033591092243324695683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3877422909579315532521821 1454033591092243324695683)
              ·
                refine ⟨2181050386638364987043525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454033591092243324695683 2181050386638364987043525)
                ·
                  refine ⟨408946947494693435070661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181050386638364987043525 408946947494693435070661)
                  ·
                    rfl

theorem cell21_1791948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1791948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791948 prefixEnd_1791948 := by exact prefixLift 1791948
  have htrace : WordTrace (prefixWord ++ tailWord_1791948) baseStart_1791948 baseEnd_1791948 := by
    simpa [prefixWord, tailWord_1791948, baseEnd_1791948] using wordTrace_append hprefix tailTrace_1791948
  have hstable : (prefixWord ++ tailWord_1791948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791948).length < 2 ^ (prefixWord ++ tailWord_1791948).sum := by decide
  have hdescent : baseEnd_1791948 < baseStart_1791948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791959 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_1791959 : Nat := 118140960795 + 1791959 * 2 ^ 59
def prefixEnd_1791959 : Nat := 4983230072969 + 3 ^ 40 * 1791959 * 2
def baseEnd_1791959 : Nat := 408949457844559860387305

theorem tailTrace_1791959 : CollatzResearch.WordTrace tailWord_1791959 prefixEnd_1791959 408949457844559860387305 := by
  unfold tailWord_1791959
  simp only [CollatzResearch.WordTrace]
  refine ⟨65358114115046060077042931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43572076076697373384695287 65358114115046060077042931)
  ·
    refine ⟨98037171172569090115564397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65358114115046060077042931 98037171172569090115564397)
    ·
      refine ⟨36763939189713408793336649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98037171172569090115564397 36763939189713408793336649)
      ·
        refine ⟨27572954392285056595002487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36763939189713408793336649 27572954392285056595002487)
        ·
          refine ⟨41359431588427584892503731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27572954392285056595002487 41359431588427584892503731)
          ·
            refine ⟨62039147382641377338755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41359431588427584892503731 62039147382641377338755597)
            ·
              refine ⟨23264680268490516502033349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62039147382641377338755597 23264680268490516502033349)
              ·
                refine ⟨4362127550341971844131253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23264680268490516502033349 4362127550341971844131253)
                ·
                  refine ⟨408949457844559860387305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362127550341971844131253 408949457844559860387305)
                  ·
                    rfl

theorem cell21_1791959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_1791959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1791959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1791959 prefixEnd_1791959 := by exact prefixLift 1791959
  have htrace : WordTrace (prefixWord ++ tailWord_1791959) baseStart_1791959 baseEnd_1791959 := by
    simpa [prefixWord, tailWord_1791959, baseEnd_1791959] using wordTrace_append hprefix tailTrace_1791959
  have hstable : (prefixWord ++ tailWord_1791959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791959).length < 2 ^ (prefixWord ++ tailWord_1791959).sum := by decide
  have hdescent : baseEnd_1791959 < baseStart_1791959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792007 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_1792007 : Nat := 118140960795 + 1792007 * 2 ^ 59
def prefixEnd_1792007 : Nat := 4983230072969 + 3 ^ 40 * 1792007 * 2
def baseEnd_1792007 : Nat := 408960412098522443587207

theorem tailTrace_1792007 : CollatzResearch.WordTrace tailWord_1792007 prefixEnd_1792007 408960412098522443587207 := by
  unfold tailWord_1792007
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359864818872164274790275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43573243212581442849860183 65359864818872164274790275)
  ·
    refine ⟨98039797228308246412185413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65359864818872164274790275 98039797228308246412185413)
    ·
      refine ⟨18382461980307796202284765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98039797228308246412185413 18382461980307796202284765)
      ·
        refine ⟨6893423242615423575856787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18382461980307796202284765 6893423242615423575856787)
        ·
          refine ⟨10340134863923135363785181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893423242615423575856787 10340134863923135363785181)
          ·
            refine ⟨3877550573971175761419443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10340134863923135363785181 3877550573971175761419443)
            ·
              refine ⟨5816325860956763642129165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877550573971175761419443 5816325860956763642129165)
              ·
                refine ⟨2181122197858786365798437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5816325860956763642129165 2181122197858786365798437)
                ·
                  refine ⟨408960412098522443587207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181122197858786365798437 408960412098522443587207)
                  ·
                    rfl

theorem cell21_1792007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_1792007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792007 prefixEnd_1792007 := by exact prefixLift 1792007
  have htrace : WordTrace (prefixWord ++ tailWord_1792007) baseStart_1792007 baseEnd_1792007 := by
    simpa [prefixWord, tailWord_1792007, baseEnd_1792007] using wordTrace_append hprefix tailTrace_1792007
  have hstable : (prefixWord ++ tailWord_1792007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792007).length < 2 ^ (prefixWord ++ tailWord_1792007).sum := by decide
  have hdescent : baseEnd_1792007 < baseStart_1792007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792111 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_1792111 : Nat := 118140960795 + 1792111 * 2 ^ 59
def prefixEnd_1792111 : Nat := 4983230072969 + 3 ^ 40 * 1792111 * 2
def baseEnd_1792111 : Nat := 408984146315441373853661

theorem tailTrace_1792111 : CollatzResearch.WordTrace tailWord_1792111 prefixEnd_1792111 408984146315441373853661 := by
  unfold tailWord_1792111
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363658010495390036576187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43575772006996926691050791 65363658010495390036576187)
  ·
    refine ⟨98045487015743085054864281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65363658010495390036576187 98045487015743085054864281)
    ·
      refine ⟨73534115261807313791148211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98045487015743085054864281 73534115261807313791148211)
      ·
        refine ⟨110301172892710970686722317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73534115261807313791148211 110301172892710970686722317)
        ·
          refine ⟨41362939834766614007520869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110301172892710970686722317 41362939834766614007520869)
          ·
            refine ⟨7755551219018740126410163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41362939834766614007520869 7755551219018740126410163)
            ·
              refine ⟨11633326828528110189615245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755551219018740126410163 11633326828528110189615245)
              ·
                refine ⟨4362497560698041321105717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633326828528110189615245 4362497560698041321105717)
                ·
                  refine ⟨408984146315441373853661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362497560698041321105717 408984146315441373853661)
                  ·
                    rfl

theorem cell21_1792111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_1792111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792111 prefixEnd_1792111 := by exact prefixLift 1792111
  have htrace : WordTrace (prefixWord ++ tailWord_1792111) baseStart_1792111 baseEnd_1792111 := by
    simpa [prefixWord, tailWord_1792111, baseEnd_1792111] using wordTrace_append hprefix tailTrace_1792111
  have hstable : (prefixWord ++ tailWord_1792111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792111).length < 2 ^ (prefixWord ++ tailWord_1792111).sum := by decide
  have hdescent : baseEnd_1792111 < baseStart_1792111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792173 : List Nat := [1, 5, 2, 1, 2, 1, 1, 8]
def baseStart_1792173 : Nat := 118140960795 + 1792173 * 2 ^ 59
def prefixEnd_1792173 : Nat := 4983230072969 + 3 ^ 40 * 1792173 * 2
def baseEnd_1792173 : Nat := 136332765186714347940067

theorem tailTrace_1792173 : CollatzResearch.WordTrace tailWord_1792173 prefixEnd_1792173 136332765186714347940067 := by
  unfold tailWord_1792173
  simp only [CollatzResearch.WordTrace]
  refine ⟨65365919336270774625333173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43577279557513849750222115 65365919336270774625333173)
  ·
    refine ⟨6128054937775385121124985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65365919336270774625333173 6128054937775385121124985)
    ·
      refine ⟨4596041203331538840843739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6128054937775385121124985 4596041203331538840843739)
      ·
        refine ⟨6894061804997308261265609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596041203331538840843739 6894061804997308261265609)
        ·
          refine ⟨5170546353747981195949207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6894061804997308261265609 5170546353747981195949207)
          ·
            refine ⟨7755819530621971793923811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170546353747981195949207 7755819530621971793923811)
            ·
              refine ⟨11633729295932957690885717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755819530621971793923811 11633729295932957690885717)
              ·
                refine ⟨136332765186714347940067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11633729295932957690885717 136332765186714347940067)
                ·
                  rfl

theorem cell21_1792173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_1792173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792173 prefixEnd_1792173 := by exact prefixLift 1792173
  have htrace : WordTrace (prefixWord ++ tailWord_1792173) baseStart_1792173 baseEnd_1792173 := by
    simpa [prefixWord, tailWord_1792173, baseEnd_1792173] using wordTrace_append hprefix tailTrace_1792173
  have hstable : (prefixWord ++ tailWord_1792173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792173).length < 2 ^ (prefixWord ++ tailWord_1792173).sum := by decide
  have hdescent : baseEnd_1792173 < baseStart_1792173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792201 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_1792201 : Nat := 118140960795 + 1792201 * 2 ^ 59
def prefixEnd_1792201 : Nat := 4983230072969 + 3 ^ 40 * 1792201 * 2
def baseEnd_1792201 : Nat := 409004685541621217353477

theorem tailTrace_1792201 : CollatzResearch.WordTrace tailWord_1792201 prefixEnd_1792201 409004685541621217353477 := by
  unfold tailWord_1792201
  simp only [CollatzResearch.WordTrace]
  refine ⟨65366940580169335407352457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43577960386779556938234971 65366940580169335407352457)
  ·
    refine ⟨49025205435127001555514343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65366940580169335407352457 49025205435127001555514343)
    ·
      refine ⟨73537808152690502333271515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49025205435127001555514343 73537808152690502333271515)
      ·
        refine ⟨110306712229035753499907273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73537808152690502333271515 110306712229035753499907273)
        ·
          refine ⟨82730034171776815124930455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110306712229035753499907273 82730034171776815124930455)
          ·
            refine ⟨124095051257665222687395683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82730034171776815124930455 124095051257665222687395683)
            ·
              refine ⟨186142576886497834031093525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124095051257665222687395683 186142576886497834031093525)
              ·
                refine ⟨8725433291554585970207509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186142576886497834031093525 8725433291554585970207509)
                ·
                  refine ⟨409004685541621217353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8725433291554585970207509 409004685541621217353477)
                  ·
                    rfl

theorem cell21_1792201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_1792201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792201 prefixEnd_1792201 := by exact prefixLift 1792201
  have htrace : WordTrace (prefixWord ++ tailWord_1792201) baseStart_1792201 baseEnd_1792201 := by
    simpa [prefixWord, tailWord_1792201, baseEnd_1792201] using wordTrace_append hprefix tailTrace_1792201
  have hstable : (prefixWord ++ tailWord_1792201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792201).length < 2 ^ (prefixWord ++ tailWord_1792201).sum := by decide
  have hdescent : baseEnd_1792201 < baseStart_1792201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792218 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1792218 : Nat := 118140960795 + 1792218 * 2 ^ 59
def prefixEnd_1792218 : Nat := 4983230072969 + 3 ^ 40 * 1792218 * 2
def baseEnd_1792218 : Nat := 409008565173232965570109

theorem tailTrace_1792218 : CollatzResearch.WordTrace tailWord_1792218 prefixEnd_1792218 409008565173232965570109 := by
  unfold tailWord_1792218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16341890155276936827680327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43578373747405164873814205 16341890155276936827680327)
  ·
    refine ⟨24512835232915405241520491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16341890155276936827680327 24512835232915405241520491)
    ·
      refine ⟨36769252849373107862280737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24512835232915405241520491 36769252849373107862280737)
      ·
        refine ⟨27576939637029830896710553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36769252849373107862280737 27576939637029830896710553)
        ·
          refine ⟨20682704727772373172532915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27576939637029830896710553 20682704727772373172532915)
          ·
            refine ⟨31024057091658559758799373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20682704727772373172532915 31024057091658559758799373)
            ·
              refine ⟨11634021409371959909549765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31024057091658559758799373 11634021409371959909549765)
              ·
                refine ⟨2181379014257242483040581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11634021409371959909549765 2181379014257242483040581)
                ·
                  refine ⟨409008565173232965570109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181379014257242483040581 409008565173232965570109)
                  ·
                    rfl

theorem cell21_1792218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1792218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792218 prefixEnd_1792218 := by exact prefixLift 1792218
  have htrace : WordTrace (prefixWord ++ tailWord_1792218) baseStart_1792218 baseEnd_1792218 := by
    simpa [prefixWord, tailWord_1792218, baseEnd_1792218] using wordTrace_append hprefix tailTrace_1792218
  have hstable : (prefixWord ++ tailWord_1792218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792218).length < 2 ^ (prefixWord ++ tailWord_1792218).sum := by decide
  have hdescent : baseEnd_1792218 < baseStart_1792218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792280 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_1792280 : Nat := 118140960795 + 1792280 * 2 ^ 59
def prefixEnd_1792280 : Nat := 4983230072969 + 3 ^ 40 * 1792280 * 2
def baseEnd_1792280 : Nat := 409022714417934635536649

theorem tailTrace_1792280 : CollatzResearch.WordTrace tailWord_1792280 prefixEnd_1792280 409022714417934635536649 := by
  unfold tailWord_1792280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32684910973441565949739147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43579881297922087932985529 32684910973441565949739147)
  ·
    refine ⟨49027366460162348924608721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32684910973441565949739147 49027366460162348924608721)
    ·
      refine ⟨36770524845121761693456541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49027366460162348924608721 36770524845121761693456541)
      ·
        refine ⟨13788946816920660635046203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36770524845121761693456541 13788946816920660635046203)
        ·
          refine ⟨20683420225380990952569305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13788946816920660635046203 20683420225380990952569305)
          ·
            refine ⟨15512565169035743214426979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20683420225380990952569305 15512565169035743214426979)
            ·
              refine ⟨23268847753553614821640469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15512565169035743214426979 23268847753553614821640469)
              ·
                refine ⟨1090727238447825694764397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23268847753553614821640469 1090727238447825694764397)
                ·
                  refine ⟨409022714417934635536649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090727238447825694764397 409022714417934635536649)
                  ·
                    rfl

theorem cell21_1792280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_1792280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792280 prefixEnd_1792280 := by exact prefixLift 1792280
  have htrace : WordTrace (prefixWord ++ tailWord_1792280) baseStart_1792280 baseEnd_1792280 := by
    simpa [prefixWord, tailWord_1792280, baseEnd_1792280] using wordTrace_append hprefix tailTrace_1792280
  have hstable : (prefixWord ++ tailWord_1792280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792280).length < 2 ^ (prefixWord ++ tailWord_1792280).sum := by decide
  have hdescent : baseEnd_1792280 < baseStart_1792280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792387 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_1792387 : Nat := 118140960795 + 1792387 * 2 ^ 59
def prefixEnd_1792387 : Nat := 4983230072969 + 3 ^ 40 * 1792387 * 2
def baseEnd_1792387 : Nat := 409047133275726227253097

theorem tailTrace_1792387 : CollatzResearch.WordTrace tailWord_1792387 prefixEnd_1792387 409047133275726227253097 := by
  unfold tailWord_1792387
  simp only [CollatzResearch.WordTrace]
  refine ⟨65373724557495489173623415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43582483038330326115748943 65373724557495489173623415)
  ·
    refine ⟨98060586836243233760435123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65373724557495489173623415 98060586836243233760435123)
    ·
      refine ⟨147090880254364850640652685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98060586836243233760435123 147090880254364850640652685)
      ·
        refine ⟨55159080095386818990244757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147090880254364850640652685 55159080095386818990244757)
        ·
          refine ⟨2585581879471257140167723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55159080095386818990244757 2585581879471257140167723)
          ·
            refine ⟨3878372819206885710251585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585581879471257140167723 3878372819206885710251585)
            ·
              refine ⟨2908779614405164282688689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878372819206885710251585 2908779614405164282688689)
              ·
                refine ⟨2181584710803873212016517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908779614405164282688689 2181584710803873212016517)
                ·
                  refine ⟨409047133275726227253097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181584710803873212016517 409047133275726227253097)
                  ·
                    rfl

theorem cell21_1792387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_1792387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792387 prefixEnd_1792387 := by exact prefixLift 1792387
  have htrace : WordTrace (prefixWord ++ tailWord_1792387) baseStart_1792387 baseEnd_1792387 := by
    simpa [prefixWord, tailWord_1792387, baseEnd_1792387] using wordTrace_append hprefix tailTrace_1792387
  have hstable : (prefixWord ++ tailWord_1792387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792387).length < 2 ^ (prefixWord ++ tailWord_1792387).sum := by decide
  have hdescent : baseEnd_1792387 < baseStart_1792387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792415 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_1792415 : Nat := 118140960795 + 1792415 * 2 ^ 59
def prefixEnd_1792415 : Nat := 4983230072969 + 3 ^ 40 * 1792415 * 2
def baseEnd_1792415 : Nat := 409053523257204400786373

theorem tailTrace_1792415 : CollatzResearch.WordTrace tailWord_1792415 prefixEnd_1792415 409053523257204400786373 := by
  unfold tailWord_1792415
  simp only [CollatzResearch.WordTrace]
  refine ⟨65374745801394049955642699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43583163867596033303761799 65374745801394049955642699)
  ·
    refine ⟨98062118702091074933464049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65374745801394049955642699 98062118702091074933464049)
    ·
      refine ⟨73546589026568306200098037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98062118702091074933464049 73546589026568306200098037)
      ·
        refine ⟨6894992721240778706259191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73546589026568306200098037 6894992721240778706259191)
        ·
          refine ⟨10342489081861168059388787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894992721240778706259191 10342489081861168059388787)
          ·
            refine ⟨15513733622791752089083181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342489081861168059388787 15513733622791752089083181)
            ·
              refine ⟨5817650108546907033406193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15513733622791752089083181 5817650108546907033406193)
              ·
                refine ⟨4363237581410180275054645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5817650108546907033406193 4363237581410180275054645)
                ·
                  refine ⟨409053523257204400786373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4363237581410180275054645 409053523257204400786373)
                  ·
                    rfl

theorem cell21_1792415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_1792415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792415 prefixEnd_1792415 := by exact prefixLift 1792415
  have htrace : WordTrace (prefixWord ++ tailWord_1792415) baseStart_1792415 baseEnd_1792415 := by
    simpa [prefixWord, tailWord_1792415, baseEnd_1792415] using wordTrace_append hprefix tailTrace_1792415
  have hstable : (prefixWord ++ tailWord_1792415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792415).length < 2 ^ (prefixWord ++ tailWord_1792415).sum := by decide
  have hdescent : baseEnd_1792415 < baseStart_1792415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792505 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1792505 : Nat := 118140960795 + 1792505 * 2 ^ 59
def prefixEnd_1792505 : Nat := 4983230072969 + 3 ^ 40 * 1792505 * 2
def baseEnd_1792505 : Nat := 409074062483384244286189

theorem tailTrace_1792505 : CollatzResearch.WordTrace tailWord_1792505 prefixEnd_1792505 409074062483384244286189 := by
  unfold tailWord_1792505
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378028371067995326418969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43585352247378663550945979 65378028371067995326418969)
  ·
    refine ⟨49033521278300996494814227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65378028371067995326418969 49033521278300996494814227)
    ·
      refine ⟨73550281917451494742221341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49033521278300996494814227 73550281917451494742221341)
      ·
        refine ⟨27581355719044310528333003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73550281917451494742221341 27581355719044310528333003)
        ·
          refine ⟨41372033578566465792499505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581355719044310528333003 41372033578566465792499505)
          ·
            refine ⟨31029025183924849344374629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41372033578566465792499505 31029025183924849344374629)
            ·
              refine ⟨5817942221985909252070243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31029025183924849344374629 5817942221985909252070243)
              ·
                refine ⟨8726913332978863878105365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817942221985909252070243 8726913332978863878105365)
                ·
                  refine ⟨409074062483384244286189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8726913332978863878105365 409074062483384244286189)
                  ·
                    rfl

theorem cell21_1792505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1792505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792505 prefixEnd_1792505 := by exact prefixLift 1792505
  have htrace : WordTrace (prefixWord ++ tailWord_1792505) baseStart_1792505 baseEnd_1792505 := by
    simpa [prefixWord, tailWord_1792505, baseEnd_1792505] using wordTrace_append hprefix tailTrace_1792505
  have hstable : (prefixWord ++ tailWord_1792505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792505).length < 2 ^ (prefixWord ++ tailWord_1792505).sum := by decide
  have hdescent : baseEnd_1792505 < baseStart_1792505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792514 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1792514 : Nat := 118140960795 + 1792514 * 2 ^ 59
def prefixEnd_1792514 : Nat := 4983230072969 + 3 ^ 40 * 1792514 * 2
def baseEnd_1792514 : Nat := 409076116406002228636171

theorem tailTrace_1792514 : CollatzResearch.WordTrace tailWord_1792514 prefixEnd_1792514 409076116406002228636171 := by
  unfold tailWord_1792514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16344589157008847465874149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43585571085356926575664397 16344589157008847465874149)
  ·
    refine ⟨3064610466939158899851403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16344589157008847465874149 3064610466939158899851403)
    ·
      refine ⟨4596915700408738349777105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064610466939158899851403 4596915700408738349777105)
      ·
        refine ⟨3447686775306553762332829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4596915700408738349777105 3447686775306553762332829)
        ·
          refine ⟨1292882540739957660874811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3447686775306553762332829 1292882540739957660874811)
          ·
            refine ⟨1939323811109936491312217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292882540739957660874811 1939323811109936491312217)
            ·
              refine ⟨1454492858332452368484163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939323811109936491312217 1454492858332452368484163)
              ·
                refine ⟨2181739287498678552726245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454492858332452368484163 2181739287498678552726245)
                ·
                  refine ⟨409076116406002228636171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181739287498678552726245 409076116406002228636171)
                  ·
                    rfl

theorem cell21_1792514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1792514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792514 prefixEnd_1792514 := by exact prefixLift 1792514
  have htrace : WordTrace (prefixWord ++ tailWord_1792514) baseStart_1792514 baseEnd_1792514 := by
    simpa [prefixWord, tailWord_1792514, baseEnd_1792514] using wordTrace_append hprefix tailTrace_1792514
  have hstable : (prefixWord ++ tailWord_1792514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792514).length < 2 ^ (prefixWord ++ tailWord_1792514).sum := by decide
  have hdescent : baseEnd_1792514 < baseStart_1792514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792522 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1792522 : Nat := 118140960795 + 1792522 * 2 ^ 59
def prefixEnd_1792522 : Nat := 4983230072969 + 3 ^ 40 * 1792522 * 2
def baseEnd_1792522 : Nat := 409077942114995992502821

theorem tailTrace_1792522 : CollatzResearch.WordTrace tailWord_1792522 prefixEnd_1792522 409077942114995992502821 := by
  unfold tailWord_1792522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16344662103001601807446955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43585765608004271486525213 16344662103001601807446955)
  ·
    refine ⟨24516993154502402711170433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16344662103001601807446955 24516993154502402711170433)
    ·
      refine ⟨18387744865876802033377825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24516993154502402711170433 18387744865876802033377825)
      ·
        refine ⟨13790808649407601525033369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18387744865876802033377825 13790808649407601525033369)
        ·
          refine ⟨10343106487055701143775027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13790808649407601525033369 10343106487055701143775027)
          ·
            refine ⟨15514659730583551715662541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343106487055701143775027 15514659730583551715662541)
            ·
              refine ⟨5817997398968831893373453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15514659730583551715662541 5817997398968831893373453)
              ·
                refine ⟨2181749024613311960015045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5817997398968831893373453 2181749024613311960015045)
                ·
                  refine ⟨409077942114995992502821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181749024613311960015045 409077942114995992502821)
                  ·
                    rfl

theorem cell21_1792522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1792522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792522 prefixEnd_1792522 := by exact prefixLift 1792522
  have htrace : WordTrace (prefixWord ++ tailWord_1792522) baseStart_1792522 baseEnd_1792522 := by
    simpa [prefixWord, tailWord_1792522, baseEnd_1792522] using wordTrace_append hprefix tailTrace_1792522
  have hstable : (prefixWord ++ tailWord_1792522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792522).length < 2 ^ (prefixWord ++ tailWord_1792522).sum := by decide
  have hdescent : baseEnd_1792522 < baseStart_1792522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792536 : List Nat := [2, 1, 2, 3, 3, 1, 2, 7]
def baseStart_1792536 : Nat := 118140960795 + 1792536 * 2 ^ 59
def prefixEnd_1792536 : Nat := 4983230072969 + 3 ^ 40 * 1792536 * 2
def baseEnd_1792536 : Nat := 136360379035245026423153

theorem tailTrace_1792536 : CollatzResearch.WordTrace tailWord_1792536 prefixEnd_1792536 136360379035245026423153 := by
  unfold tailWord_1792536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689579516977843810398731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43586106022637125080531641 32689579516977843810398731)
  ·
    refine ⟨49034369275466765715598097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32689579516977843810398731 49034369275466765715598097)
    ·
      refine ⟨36775776956600074286698573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49034369275466765715598097 36775776956600074286698573)
      ·
        refine ⟨13790916358725027857511965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36775776956600074286698573 13790916358725027857511965)
        ·
          refine ⟨5171593634521885446566987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13790916358725027857511965 5171593634521885446566987)
          ·
            refine ⟨7757390451782828169850481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171593634521885446566987 7757390451782828169850481)
            ·
              refine ⟨5818042838837121127387861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757390451782828169850481 5818042838837121127387861)
              ·
                refine ⟨136360379035245026423153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5818042838837121127387861 136360379035245026423153)
                ·
                  rfl

theorem cell21_1792536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_1792536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792536 prefixEnd_1792536 := by exact prefixLift 1792536
  have htrace : WordTrace (prefixWord ++ tailWord_1792536) baseStart_1792536 baseEnd_1792536 := by
    simpa [prefixWord, tailWord_1792536, baseEnd_1792536] using wordTrace_append hprefix tailTrace_1792536
  have hstable : (prefixWord ++ tailWord_1792536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792536).length < 2 ^ (prefixWord ++ tailWord_1792536).sum := by decide
  have hdescent : baseEnd_1792536 < baseStart_1792536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792691 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 4]
def baseStart_1792691 : Nat := 118140960795 + 1792691 * 2 ^ 59
def prefixEnd_1792691 : Nat := 4983230072969 + 3 ^ 40 * 1792691 * 2
def baseEnd_1792691 : Nat := 409116510217489254185809

theorem tailTrace_1792691 : CollatzResearch.WordTrace tailWord_1792691 prefixEnd_1792691 409116510217489254185809 := by
  unfold tailWord_1792691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65384812348394149092689927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43589874898929432728459951 65384812348394149092689927)
  ·
    refine ⟨98077218522591223639034891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65384812348394149092689927 98077218522591223639034891)
    ·
      refine ⟨147115827783886835458552337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98077218522591223639034891 147115827783886835458552337)
      ·
        refine ⟨110336870837915126593914253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147115827783886835458552337 110336870837915126593914253)
        ·
          refine ⟨41376326564218172472717845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110336870837915126593914253 41376326564218172472717845)
          ·
            refine ⟨1939515307697726834658649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41376326564218172472717845 1939515307697726834658649)
            ·
              refine ⟨1454636480773295125993987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939515307697726834658649 1454636480773295125993987)
              ·
                refine ⟨2181954721159942688990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454636480773295125993987 2181954721159942688990981)
                ·
                  refine ⟨409116510217489254185809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181954721159942688990981 409116510217489254185809)
                  ·
                    rfl

theorem cell21_1792691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_1792691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792691 prefixEnd_1792691 := by exact prefixLift 1792691
  have htrace : WordTrace (prefixWord ++ tailWord_1792691) baseStart_1792691 baseEnd_1792691 := by
    simpa [prefixWord, tailWord_1792691, baseEnd_1792691] using wordTrace_append hprefix tailTrace_1792691
  have hstable : (prefixWord ++ tailWord_1792691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792691).length < 2 ^ (prefixWord ++ tailWord_1792691).sum := by decide
  have hdescent : baseEnd_1792691 < baseStart_1792691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792750 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1792750 : Nat := 118140960795 + 1792750 * 2 ^ 59
def prefixEnd_1792750 : Nat := 4983230072969 + 3 ^ 40 * 1792750 * 2
def baseEnd_1792750 : Nat := 409129974821318262702355

theorem tailTrace_1792750 : CollatzResearch.WordTrace tailWord_1792750 prefixEnd_1792750 409129974821318262702355 := by
  unfold tailWord_1792750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173370531897550271135963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43591309503453601446058469 8173370531897550271135963)
  ·
    refine ⟨12260055797846325406703945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8173370531897550271135963 12260055797846325406703945)
    ·
      refine ⟨9195041848384744055027959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12260055797846325406703945 9195041848384744055027959)
      ·
        refine ⟨13792562772577116082541939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195041848384744055027959 13792562772577116082541939)
        ·
          refine ⟨20688844158865674123812909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13792562772577116082541939 20688844158865674123812909)
          ·
            refine ⟨7758316559574627796429841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20688844158865674123812909 7758316559574627796429841)
            ·
              refine ⟨5818737419680970847322381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7758316559574627796429841 5818737419680970847322381)
              ·
                refine ⟨2182026532380364067745893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5818737419680970847322381 2182026532380364067745893)
                ·
                  refine ⟨409129974821318262702355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2182026532380364067745893 409129974821318262702355)
                  ·
                    rfl

theorem cell21_1792750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1792750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792750 prefixEnd_1792750 := by exact prefixLift 1792750
  have htrace : WordTrace (prefixWord ++ tailWord_1792750) baseStart_1792750 baseEnd_1792750 := by
    simpa [prefixWord, tailWord_1792750, baseEnd_1792750] using wordTrace_append hprefix tailTrace_1792750
  have hstable : (prefixWord ++ tailWord_1792750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792750).length < 2 ^ (prefixWord ++ tailWord_1792750).sum := by decide
  have hdescent : baseEnd_1792750 < baseStart_1792750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792778 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1792778 : Nat := 118140960795 + 1792778 * 2 ^ 59
def prefixEnd_1792778 : Nat := 4983230072969 + 3 ^ 40 * 1792778 * 2
def baseEnd_1792778 : Nat := 409136364802796436235631

theorem tailTrace_1792778 : CollatzResearch.WordTrace tailWord_1792778 prefixEnd_1792778 409136364802796436235631 := by
  unfold tailWord_1792778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346996374769740737776747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43591990332719308634071325 16346996374769740737776747)
  ·
    refine ⟨24520494562154611106665121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16346996374769740737776747 24520494562154611106665121)
    ·
      refine ⟨18390370921615958329998841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24520494562154611106665121 18390370921615958329998841)
      ·
        refine ⟨13792778191211968747499131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18390370921615958329998841 13792778191211968747499131)
        ·
          refine ⟨20689167286817953121248697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13792778191211968747499131 20689167286817953121248697)
          ·
            refine ⟨15516875465113464840936523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20689167286817953121248697 15516875465113464840936523)
            ·
              refine ⟨23275313197670197261404785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516875465113464840936523 23275313197670197261404785)
              ·
                refine ⟨17456484898252647946053589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23275313197670197261404785 17456484898252647946053589)
                ·
                  refine ⟨409136364802796436235631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17456484898252647946053589 409136364802796436235631)
                  ·
                    rfl

theorem cell21_1792778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1792778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792778 prefixEnd_1792778 := by exact prefixLift 1792778
  have htrace : WordTrace (prefixWord ++ tailWord_1792778) baseStart_1792778 baseEnd_1792778 := by
    simpa [prefixWord, tailWord_1792778, baseEnd_1792778] using wordTrace_append hprefix tailTrace_1792778
  have hstable : (prefixWord ++ tailWord_1792778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792778).length < 2 ^ (prefixWord ++ tailWord_1792778).sum := by decide
  have hdescent : baseEnd_1792778 < baseStart_1792778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792823 : List Nat := [1, 1, 3, 1, 2, 1, 5, 7]
def baseStart_1792823 : Nat := 118140960795 + 1792823 * 2 ^ 59
def prefixEnd_1792823 : Nat := 4983230072969 + 3 ^ 40 * 1792823 * 2
def baseEnd_1792823 : Nat := 136382211471962119328513

theorem tailTrace_1792823 : CollatzResearch.WordTrace tailWord_1792823 prefixEnd_1792823 136382211471962119328513 := by
  unfold tailWord_1792823
  simp only [CollatzResearch.WordTrace]
  refine ⟨65389626783915935636495123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43593084522610623757663415 65389626783915935636495123)
  ·
    refine ⟨98084440175873903454742685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65389626783915935636495123 98084440175873903454742685)
    ·
      refine ⟨36781665065952713795528507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98084440175873903454742685 36781665065952713795528507)
      ·
        refine ⟨55172497598929070693292761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36781665065952713795528507 55172497598929070693292761)
        ·
          refine ⟨41379373199196803019969571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55172497598929070693292761 41379373199196803019969571)
          ·
            refine ⟨62069059798795204529954357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41379373199196803019969571 62069059798795204529954357)
            ·
              refine ⟨5818974356137050424683221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62069059798795204529954357 5818974356137050424683221)
              ·
                refine ⟨136382211471962119328513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5818974356137050424683221 136382211471962119328513)
                ·
                  rfl

theorem cell21_1792823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_1792823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792823 prefixEnd_1792823 := by exact prefixLift 1792823
  have htrace : WordTrace (prefixWord ++ tailWord_1792823) baseStart_1792823 baseEnd_1792823 := by
    simpa [prefixWord, tailWord_1792823, baseEnd_1792823] using wordTrace_append hprefix tailTrace_1792823
  have hstable : (prefixWord ++ tailWord_1792823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792823).length < 2 ^ (prefixWord ++ tailWord_1792823).sum := by decide
  have hdescent : baseEnd_1792823 < baseStart_1792823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792860 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1792860 : Nat := 118140960795 + 1792860 * 2 ^ 59
def prefixEnd_1792860 : Nat := 4983230072969 + 3 ^ 40 * 1792860 * 2
def baseEnd_1792860 : Nat := 409155078319982515868797

theorem tailTrace_1792860 : CollatzResearch.WordTrace tailWord_1792860 prefixEnd_1792860 409155078319982515868797 := by
  unfold tailWord_1792860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32695488142390945477796017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43593984189854593970394689 32695488142390945477796017)
  ·
    refine ⟨24521616106793209108347013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32695488142390945477796017 24521616106793209108347013)
    ·
      refine ⟨4597803020023726707815065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24521616106793209108347013 4597803020023726707815065)
      ·
        refine ⟨3448352265017795030861299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4597803020023726707815065 3448352265017795030861299)
        ·
          refine ⟨5172528397526692546291949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448352265017795030861299 5172528397526692546291949)
          ·
            refine ⟨1939698149072509704859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5172528397526692546291949 1939698149072509704859481)
            ·
              refine ⟨1454773611804382278644611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939698149072509704859481 1454773611804382278644611)
              ·
                refine ⟨2182160417706573417966917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454773611804382278644611 2182160417706573417966917)
                ·
                  refine ⟨409155078319982515868797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2182160417706573417966917 409155078319982515868797)
                  ·
                    rfl

theorem cell21_1792860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1792860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792860 prefixEnd_1792860 := by exact prefixLift 1792860
  have htrace : WordTrace (prefixWord ++ tailWord_1792860) baseStart_1792860 baseEnd_1792860 := by
    simpa [prefixWord, tailWord_1792860, baseEnd_1792860] using wordTrace_append hprefix tailTrace_1792860
  have hstable : (prefixWord ++ tailWord_1792860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792860).length < 2 ^ (prefixWord ++ tailWord_1792860).sum := by decide
  have hdescent : baseEnd_1792860 < baseStart_1792860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792905 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 3]
def baseStart_1792905 : Nat := 118140960795 + 1792905 * 2 ^ 59
def prefixEnd_1792905 : Nat := 4983230072969 + 3 ^ 40 * 1792905 * 2
def baseEnd_1792905 : Nat := 409165347933072437618705

theorem tailTrace_1792905 : CollatzResearch.WordTrace tailWord_1792905 prefixEnd_1792905 409165347933072437618705 := by
  unfold tailWord_1792905
  simp only [CollatzResearch.WordTrace]
  refine ⟨65392617569618863640980169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43595078379745909093986779 65392617569618863640980169)
  ·
    refine ⟨49044463177214147730735127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65392617569618863640980169 49044463177214147730735127)
    ·
      refine ⟨73566694765821221596102691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49044463177214147730735127 73566694765821221596102691)
      ·
        refine ⟨110350042148731832394154037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73566694765821221596102691 110350042148731832394154037)
        ·
          refine ⟨10345316451443609286951941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110350042148731832394154037 10345316451443609286951941)
          ·
            refine ⟨1939746834645676741303489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10345316451443609286951941 1939746834645676741303489)
            ·
              refine ⟨1454810125984257555977617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939746834645676741303489 1454810125984257555977617)
              ·
                refine ⟨1091107594488193166983213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454810125984257555977617 1091107594488193166983213)
                ·
                  refine ⟨409165347933072437618705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091107594488193166983213 409165347933072437618705)
                  ·
                    rfl

theorem cell21_1792905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_1792905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1792905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1792905 prefixEnd_1792905 := by exact prefixLift 1792905
  have htrace : WordTrace (prefixWord ++ tailWord_1792905) baseStart_1792905 baseEnd_1792905 := by
    simpa [prefixWord, tailWord_1792905, baseEnd_1792905] using wordTrace_append hprefix tailTrace_1792905
  have hstable : (prefixWord ++ tailWord_1792905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792905).length < 2 ^ (prefixWord ++ tailWord_1792905).sum := by decide
  have hdescent : baseEnd_1792905 < baseStart_1792905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793026 : List Nat := [3, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1793026 : Nat := 118140960795 + 1793026 * 2 ^ 59
def prefixEnd_1793026 : Nat := 4983230072969 + 3 ^ 40 * 1793026 * 2
def baseEnd_1793026 : Nat := 136397653927201038700597

theorem tailTrace_1793026 : CollatzResearch.WordTrace tailWord_1793026 prefixEnd_1793026 136397653927201038700597 := by
  unfold tailWord_1793026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349257700545125326533733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43598020534787000870756621 16349257700545125326533733)
  ·
    refine ⟨3065485818852210998725075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16349257700545125326533733 3065485818852210998725075)
    ·
      refine ⟨4598228728278316498087613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065485818852210998725075 4598228728278316498087613)
      ·
        refine ⟨1724335773104368686782855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4598228728278316498087613 1724335773104368686782855)
        ·
          refine ⟨2586503659656553030174283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724335773104368686782855 2586503659656553030174283)
          ·
            refine ⟨3879755489484829545261425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586503659656553030174283 3879755489484829545261425)
            ·
              refine ⟨2909816617113622158946069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879755489484829545261425 2909816617113622158946069)
              ·
                refine ⟨136397653927201038700597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2909816617113622158946069 136397653927201038700597)
                ·
                  rfl

theorem cell21_1793026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1793026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793026 prefixEnd_1793026 := by exact prefixLift 1793026
  have htrace : WordTrace (prefixWord ++ tailWord_1793026) baseStart_1793026 baseEnd_1793026 := by
    simpa [prefixWord, tailWord_1793026, baseEnd_1793026] using wordTrace_append hprefix tailTrace_1793026
  have hstable : (prefixWord ++ tailWord_1793026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793026).length < 2 ^ (prefixWord ++ tailWord_1793026).sum := by decide
  have hdescent : baseEnd_1793026 < baseStart_1793026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793116 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_1793116 : Nat := 118140960795 + 1793116 * 2 ^ 59
def prefixEnd_1793116 : Nat := 4983230072969 + 3 ^ 40 * 1793116 * 2
def baseEnd_1793116 : Nat := 409213501007782959601607

theorem tailTrace_1793116 : CollatzResearch.WordTrace tailWord_1793116 prefixEnd_1793116 409213501007782959601607 := by
  unfold tailWord_1793116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700156685927223338455601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43600208914569631117940801 32700156685927223338455601)
  ·
    refine ⟨24525117514445417503841701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32700156685927223338455601 24525117514445417503841701)
    ·
      refine ⟨4598459533958515781970319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24525117514445417503841701 4598459533958515781970319)
      ·
        refine ⟨6897689300937773672955479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4598459533958515781970319 6897689300937773672955479)
        ·
          refine ⟨10346533951406660509433219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897689300937773672955479 10346533951406660509433219)
          ·
            refine ⟨15519800927109990764149829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346533951406660509433219 15519800927109990764149829)
            ·
              refine ⟨2909962673833123268278093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15519800927109990764149829 2909962673833123268278093)
              ·
                refine ⟨1091236002687421225604285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2909962673833123268278093 1091236002687421225604285)
                ·
                  refine ⟨409213501007782959601607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091236002687421225604285 409213501007782959601607)
                  ·
                    rfl

theorem cell21_1793116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_1793116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793116 prefixEnd_1793116 := by exact prefixLift 1793116
  have htrace : WordTrace (prefixWord ++ tailWord_1793116) baseStart_1793116 baseEnd_1793116 := by
    simpa [prefixWord, tailWord_1793116, baseEnd_1793116] using wordTrace_append hprefix tailTrace_1793116
  have hstable : (prefixWord ++ tailWord_1793116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793116).length < 2 ^ (prefixWord ++ tailWord_1793116).sum := by decide
  have hdescent : baseEnd_1793116 < baseStart_1793116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793127 : List Nat := [1, 1, 5, 1, 1, 4, 8]
def baseStart_1793127 : Nat := 118140960795 + 1793127 * 2 ^ 59
def prefixEnd_1793127 : Nat := 4983230072969 + 3 ^ 40 * 1793127 * 2
def baseEnd_1793127 : Nat := 45468445706405487213139

theorem tailTrace_1793127 : CollatzResearch.WordTrace tailWord_1793127 prefixEnd_1793127 45468445706405487213139 := by
  unfold tailWord_1793127
  simp only [CollatzResearch.WordTrace]
  refine ⟨65400714574814595555561635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43600476383209730370374423 65400714574814595555561635)
  ·
    refine ⟨98101071862221893333342453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65400714574814595555561635 98101071862221893333342453)
    ·
      refine ⟨9196975487083302500000855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98101071862221893333342453 9196975487083302500000855)
      ·
        refine ⟨13795463230624953750001283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9196975487083302500000855 13795463230624953750001283)
        ·
          refine ⟨20693194845937430625001925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795463230624953750001283 20693194845937430625001925)
          ·
            refine ⟨3879974033613268242187861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20693194845937430625001925 3879974033613268242187861)
            ·
              refine ⟨45468445706405487213139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3879974033613268242187861 45468445706405487213139)
              ·
                rfl

theorem cell21_1793127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_1793127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793127 prefixEnd_1793127 := by exact prefixLift 1793127
  have htrace : WordTrace (prefixWord ++ tailWord_1793127) baseStart_1793127 baseEnd_1793127 := by
    simpa [prefixWord, tailWord_1793127, baseEnd_1793127] using wordTrace_append hprefix tailTrace_1793127
  have hstable : (prefixWord ++ tailWord_1793127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793127).length < 2 ^ (prefixWord ++ tailWord_1793127).sum := by decide
  have hdescent : baseEnd_1793127 < baseStart_1793127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793130 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1793130 : Nat := 118140960795 + 1793130 * 2 ^ 59
def prefixEnd_1793130 : Nat := 4983230072969 + 3 ^ 40 * 1793130 * 2
def baseEnd_1793130 : Nat := 409216695998522046368245

theorem tailTrace_1793130 : CollatzResearch.WordTrace tailWord_1793130 prefixEnd_1793130 409216695998522046368245 := by
  unfold tailWord_1793130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350205998450931766980211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43600549329202484711947229 16350205998450931766980211)
  ·
    refine ⟨24525308997676397650470317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350205998450931766980211 24525308997676397650470317)
    ·
      refine ⟨9196990874128649118926369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24525308997676397650470317 9196990874128649118926369)
      ·
        refine ⟨6897743155596486839194777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196990874128649118926369 6897743155596486839194777)
        ·
          refine ⟨5173307366697365129396083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6897743155596486839194777 5173307366697365129396083)
          ·
            refine ⟨7759961050046047694094125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173307366697365129396083 7759961050046047694094125)
            ·
              refine ⟨2909985393767267885285297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7759961050046047694094125 2909985393767267885285297)
              ·
                refine ⟨2182489045325450913963973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909985393767267885285297 2182489045325450913963973)
                ·
                  refine ⟨409216695998522046368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2182489045325450913963973 409216695998522046368245)
                  ·
                    rfl

theorem cell21_1793130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1793130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793130 prefixEnd_1793130 := by exact prefixLift 1793130
  have htrace : WordTrace (prefixWord ++ tailWord_1793130) baseStart_1793130 baseEnd_1793130 := by
    simpa [prefixWord, tailWord_1793130, baseEnd_1793130] using wordTrace_append hprefix tailTrace_1793130
  have hstable : (prefixWord ++ tailWord_1793130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793130).length < 2 ^ (prefixWord ++ tailWord_1793130).sum := by decide
  have hdescent : baseEnd_1793130 < baseStart_1793130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793507 : List Nat := [1, 1, 1, 6, 2, 2, 1, 7]
def baseStart_1793507 : Nat := 118140960795 + 1793507 * 2 ^ 59
def prefixEnd_1793507 : Nat := 4983230072969 + 3 ^ 40 * 1793507 * 2
def baseEnd_1793507 : Nat := 136434244178284389528047

theorem tailTrace_1793507 : CollatzResearch.WordTrace tailWord_1793507 prefixEnd_1793507 136434244178284389528047 := by
  unfold tailWord_1793507
  simp only [CollatzResearch.WordTrace]
  refine ⟨65414574313437920454394775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43609716208958613636263183 65414574313437920454394775)
  ·
    refine ⟨98121861470156880681592163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65414574313437920454394775 98121861470156880681592163)
    ·
      refine ⟨147182792205235321022388245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98121861470156880681592163 147182792205235321022388245)
      ·
        refine ⟨6899193384620405672924449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147182792205235321022388245 6899193384620405672924449)
        ·
          refine ⟨5174395038465304254693337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899193384620405672924449 5174395038465304254693337)
          ·
            refine ⟨3880796278848978191020003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5174395038465304254693337 3880796278848978191020003)
            ·
              refine ⟨5821194418273467286530005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880796278848978191020003 5821194418273467286530005)
              ·
                refine ⟨136434244178284389528047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5821194418273467286530005 136434244178284389528047)
                ·
                  rfl

theorem cell21_1793507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_1793507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793507 prefixEnd_1793507 := by exact prefixLift 1793507
  have htrace : WordTrace (prefixWord ++ tailWord_1793507) baseStart_1793507 baseEnd_1793507 := by
    simpa [prefixWord, tailWord_1793507, baseEnd_1793507] using wordTrace_append hprefix tailTrace_1793507
  have hstable : (prefixWord ++ tailWord_1793507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793507).length < 2 ^ (prefixWord ++ tailWord_1793507).sum := by decide
  have hdescent : baseEnd_1793507 < baseStart_1793507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793611 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_1793611 : Nat := 118140960795 + 1793611 * 2 ^ 59
def prefixEnd_1793611 : Nat := 4983230072969 + 3 ^ 40 * 1793611 * 2
def baseEnd_1793611 : Nat := 409326466751772098850595

theorem tailTrace_1793611 : CollatzResearch.WordTrace tailWord_1793611 prefixEnd_1793611 409326466751772098850595 := by
  unfold tailWord_1793611
  simp only [CollatzResearch.WordTrace]
  refine ⟨65418367505061146216180687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43612245003374097477453791 65418367505061146216180687)
  ·
    refine ⟨98127551257591719324271031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65418367505061146216180687 98127551257591719324271031)
    ·
      refine ⟨147191326886387578986406547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98127551257591719324271031 147191326886387578986406547)
      ·
        refine ⟨220786990329581368479609821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147191326886387578986406547 220786990329581368479609821)
        ·
          refine ⟨82795121373593013179853683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220786990329581368479609821 82795121373593013179853683)
          ·
            refine ⟨124192682060389519769780525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82795121373593013179853683 124192682060389519769780525)
            ·
              refine ⟨46572255772646069913667697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124192682060389519769780525 46572255772646069913667697)
              ·
                refine ⟨34929191829484552435250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46572255772646069913667697 34929191829484552435250773)
                ·
                  refine ⟨409326466751772098850595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34929191829484552435250773 409326466751772098850595)
                  ·
                    rfl

theorem cell21_1793611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_1793611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793611 prefixEnd_1793611 := by exact prefixLift 1793611
  have htrace : WordTrace (prefixWord ++ tailWord_1793611) baseStart_1793611 baseEnd_1793611 := by
    simpa [prefixWord, tailWord_1793611, baseEnd_1793611] using wordTrace_append hprefix tailTrace_1793611
  have hstable : (prefixWord ++ tailWord_1793611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793611).length < 2 ^ (prefixWord ++ tailWord_1793611).sum := by decide
  have hdescent : baseEnd_1793611 < baseStart_1793611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793645 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1793645 : Nat := 118140960795 + 1793645 * 2 ^ 59
def prefixEnd_1793645 : Nat := 4983230072969 + 3 ^ 40 * 1793645 * 2
def baseEnd_1793645 : Nat := 409334226014995595283859

theorem tailTrace_1793645 : CollatzResearch.WordTrace tailWord_1793645 prefixEnd_1793645 409334226014995595283859 := by
  unfold tailWord_1793645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65419607586937970022918389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43613071724625313348612259 65419607586937970022918389)
  ·
    refine ⟨6133088211275434689648599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65419607586937970022918389 6133088211275434689648599)
    ·
      refine ⟨9199632316913152034472899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133088211275434689648599 9199632316913152034472899)
      ·
        refine ⟨13799448475369728051709349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199632316913152034472899 13799448475369728051709349)
        ·
          refine ⟨2587396589131824009695503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13799448475369728051709349 2587396589131824009695503)
          ·
            refine ⟨3881094883697736014543255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587396589131824009695503 3881094883697736014543255)
            ·
              refine ⟨5821642325546604021814883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881094883697736014543255 5821642325546604021814883)
              ·
                refine ⟨8732463488319906032722325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821642325546604021814883 8732463488319906032722325)
                ·
                  refine ⟨409334226014995595283859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8732463488319906032722325 409334226014995595283859)
                  ·
                    rfl

theorem cell21_1793645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1793645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793645 prefixEnd_1793645 := by exact prefixLift 1793645
  have htrace : WordTrace (prefixWord ++ tailWord_1793645) baseStart_1793645 baseEnd_1793645 := by
    simpa [prefixWord, tailWord_1793645, baseEnd_1793645] using wordTrace_append hprefix tailTrace_1793645
  have hstable : (prefixWord ++ tailWord_1793645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793645).length < 2 ^ (prefixWord ++ tailWord_1793645).sum := by decide
  have hdescent : baseEnd_1793645 < baseStart_1793645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
