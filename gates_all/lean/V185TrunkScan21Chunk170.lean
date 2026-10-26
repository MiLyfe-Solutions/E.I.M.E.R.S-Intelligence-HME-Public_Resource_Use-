import V185TrunkScan21Chunk169

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2070757 : List Nat := [1, 3, 1, 4, 2, 3, 7]
def baseStart_2070757 : Nat := 118140960795 + 2070757 * 2 ^ 59
def prefixEnd_2070757 : Nat := 4983230072969 + 3 ^ 40 * 2070757 * 2
def baseEnd_2070757 : Nat := 52508328872220241353791

theorem tailTrace_2070757 : CollatzResearch.WordTrace tailWord_2070757 prefixEnd_2070757 52508328872220241353791 := by
  unfold tailWord_2070757
  simp only [CollatzResearch.WordTrace]
  refine ⟨75526712559008520984626525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50351141706005680656417683 75526712559008520984626525)
  ·
    refine ⟨28322517209628195369234947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75526712559008520984626525 28322517209628195369234947)
    ·
      refine ⟨42483775814442293053852421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28322517209628195369234947 42483775814442293053852421)
      ·
        refine ⟨7965707965207929947597329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42483775814442293053852421 7965707965207929947597329)
        ·
          refine ⟨5974280973905947460697997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7965707965207929947597329 5974280973905947460697997)
          ·
            refine ⟨2240355365214730297761749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5974280973905947460697997 2240355365214730297761749)
            ·
              refine ⟨52508328872220241353791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2240355365214730297761749 52508328872220241353791)
              ·
                rfl

theorem cell21_2070757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 7].length) (baseStart_2070757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070757 prefixEnd_2070757 := by exact prefixLift 2070757
  have htrace : WordTrace (prefixWord ++ tailWord_2070757) baseStart_2070757 baseEnd_2070757 := by
    simpa [prefixWord, tailWord_2070757, baseEnd_2070757] using wordTrace_append hprefix tailTrace_2070757
  have hstable : (prefixWord ++ tailWord_2070757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070757).length < 2 ^ (prefixWord ++ tailWord_2070757).sum := by decide
  have hdescent : baseEnd_2070757 < baseStart_2070757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070816 : List Nat := [2, 1, 1, 5, 2, 10]
def baseStart_2070816 : Nat := 118140960795 + 2070816 * 2 ^ 59
def prefixEnd_2070816 : Nat := 4983230072969 + 3 ^ 40 * 2070816 * 2
def baseEnd_2070816 : Nat := 17503274979770784470395

theorem tailTrace_2070816 : CollatzResearch.WordTrace tailWord_2070816 prefixEnd_2070816 17503274979770784470395 := by
  unfold tailWord_2070816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37764432232897387030512151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50352576310529849374016201 37764432232897387030512151)
  ·
    refine ⟨56646648349346080545768227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37764432232897387030512151 56646648349346080545768227)
    ·
      refine ⟨84969972524019120818652341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56646648349346080545768227 84969972524019120818652341)
      ·
        refine ⟨7965934924126792576748657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84969972524019120818652341 7965934924126792576748657)
        ·
          refine ⟨5974451193095094432561493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7965934924126792576748657 5974451193095094432561493)
          ·
            refine ⟨17503274979770784470395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5974451193095094432561493 17503274979770784470395)
            ·
              rfl

theorem cell21_2070816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 10].length) (baseStart_2070816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070816 prefixEnd_2070816 := by exact prefixLift 2070816
  have htrace : WordTrace (prefixWord ++ tailWord_2070816) baseStart_2070816 baseEnd_2070816 := by
    simpa [prefixWord, tailWord_2070816, baseEnd_2070816] using wordTrace_append hprefix tailTrace_2070816
  have hstable : (prefixWord ++ tailWord_2070816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070816).length < 2 ^ (prefixWord ++ tailWord_2070816).sum := by decide
  have hdescent : baseEnd_2070816 < baseStart_2070816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070847 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_2070847 : Nat := 118140960795 + 2070847 * 2 ^ 59
def prefixEnd_2070847 : Nat := 4983230072969 + 3 ^ 40 * 2070847 * 2
def baseEnd_2070847 : Nat := 472595499076162015683935

theorem tailTrace_2070847 : CollatzResearch.WordTrace tailWord_2070847 prefixEnd_2070847 472595499076162015683935 := by
  unfold tailWord_2070847
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529995128682466355402795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50353330085788310903601863 75529995128682466355402795)
  ·
    refine ⟨113294992693023699533104193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75529995128682466355402795 113294992693023699533104193)
    ·
      refine ⟨84971244519767774649828145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113294992693023699533104193 84971244519767774649828145)
      ·
        refine ⟨63728433389825830987371109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84971244519767774649828145 63728433389825830987371109)
        ·
          refine ⟨11949081260592343310132083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63728433389825830987371109 11949081260592343310132083)
          ·
            refine ⟨17923621890888514965198125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949081260592343310132083 17923621890888514965198125)
            ·
              refine ⟨6721358209083193111949297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17923621890888514965198125 6721358209083193111949297)
              ·
                refine ⟨5041018656812394833961973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721358209083193111949297 5041018656812394833961973)
                ·
                  refine ⟨472595499076162015683935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041018656812394833961973 472595499076162015683935)
                  ·
                    rfl

theorem cell21_2070847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_2070847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070847 prefixEnd_2070847 := by exact prefixLift 2070847
  have htrace : WordTrace (prefixWord ++ tailWord_2070847) baseStart_2070847 baseEnd_2070847 := by
    simpa [prefixWord, tailWord_2070847, baseEnd_2070847] using wordTrace_append hprefix tailTrace_2070847
  have hstable : (prefixWord ++ tailWord_2070847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070847).length < 2 ^ (prefixWord ++ tailWord_2070847).sum := by decide
  have hdescent : baseEnd_2070847 < baseStart_2070847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070864 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_2070864 : Nat := 118140960795 + 2070864 * 2 ^ 59
def prefixEnd_2070864 : Nat := 4983230072969 + 3 ^ 40 * 2070864 * 2
def baseEnd_2070864 : Nat := 472599378707773763900567

theorem tailTrace_2070864 : CollatzResearch.WordTrace tailWord_2070864 prefixEnd_2070864 472599378707773763900567 := by
  unfold tailWord_2070864
  simp only [CollatzResearch.WordTrace]
  refine ⟨37765307584810439129385823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50353743446413918839181097 37765307584810439129385823)
  ·
    refine ⟨56647961377215658694078735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37765307584810439129385823 56647961377215658694078735)
    ·
      refine ⟨84971942065823488041118103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56647961377215658694078735 84971942065823488041118103)
      ·
        refine ⟨127457913098735232061677155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84971942065823488041118103 127457913098735232061677155)
        ·
          refine ⟨191186869648102848092515733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127457913098735232061677155 191186869648102848092515733)
          ·
            refine ⟨8961884514754821004336675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191186869648102848092515733 8961884514754821004336675)
            ·
              refine ⟨13442826772132231506505013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961884514754821004336675 13442826772132231506505013)
              ·
                refine ⟨1260265009887396703734845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13442826772132231506505013 1260265009887396703734845)
                ·
                  refine ⟨472599378707773763900567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260265009887396703734845 472599378707773763900567)
                  ·
                    rfl

theorem cell21_2070864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_2070864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070864 prefixEnd_2070864 := by exact prefixLift 2070864
  have htrace : WordTrace (prefixWord ++ tailWord_2070864) baseStart_2070864 baseEnd_2070864 := by
    simpa [prefixWord, tailWord_2070864, baseEnd_2070864] using wordTrace_append hprefix tailTrace_2070864
  have hstable : (prefixWord ++ tailWord_2070864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070864).length < 2 ^ (prefixWord ++ tailWord_2070864).sum := by decide
  have hdescent : baseEnd_2070864 < baseStart_2070864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070909 : List Nat := [1, 4, 1, 1, 2, 3, 4, 5]
def baseStart_2070909 : Nat := 118140960795 + 2070909 * 2 ^ 59
def prefixEnd_2070909 : Nat := 4983230072969 + 3 ^ 40 * 2070909 * 2
def baseEnd_2070909 : Nat := 157536549440287895216825

theorem tailTrace_2070909 : CollatzResearch.WordTrace tailWord_2070909 prefixEnd_2070909 157536549440287895216825 := by
  unfold tailWord_2070909
  simp only [CollatzResearch.WordTrace]
  refine ⟨75532256454457850944159781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50354837636305233962773187 75532256454457850944159781)
  ·
    refine ⟨14162298085210847052029959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75532256454457850944159781 14162298085210847052029959)
    ·
      refine ⟨21243447127816270578044939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162298085210847052029959 21243447127816270578044939)
      ·
        refine ⟨31865170691724405867067409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243447127816270578044939 31865170691724405867067409)
        ·
          refine ⟨23898878018793304400300557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31865170691724405867067409 23898878018793304400300557)
          ·
            refine ⟨8962079257047489150112709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23898878018793304400300557 8962079257047489150112709)
            ·
              refine ⟨1680389860696404215646133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8962079257047489150112709 1680389860696404215646133)
              ·
                refine ⟨157536549440287895216825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680389860696404215646133 157536549440287895216825)
                ·
                  rfl

theorem cell21_2070909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].length) (baseStart_2070909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070909 prefixEnd_2070909 := by exact prefixLift 2070909
  have htrace : WordTrace (prefixWord ++ tailWord_2070909) baseStart_2070909 baseEnd_2070909 := by
    simpa [prefixWord, tailWord_2070909, baseEnd_2070909] using wordTrace_append hprefix tailTrace_2070909
  have hstable : (prefixWord ++ tailWord_2070909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070909).length < 2 ^ (prefixWord ++ tailWord_2070909).sum := by decide
  have hdescent : baseEnd_2070909 < baseStart_2070909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070937 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_2070937 : Nat := 118140960795 + 2070937 * 2 ^ 59
def prefixEnd_2070937 : Nat := 4983230072969 + 3 ^ 40 * 2070937 * 2
def baseEnd_2070937 : Nat := 472616038302341859183751

theorem tailTrace_2070937 : CollatzResearch.WordTrace tailWord_2070937 prefixEnd_2070937 472616038302341859183751 := by
  unfold tailWord_2070937
  simp only [CollatzResearch.WordTrace]
  refine ⟨75533277698356411726179065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50355518465570941150786043 75533277698356411726179065)
  ·
    refine ⟨56649958273767308794634299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75533277698356411726179065 56649958273767308794634299)
    ·
      refine ⟨84974937410650963191951449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56649958273767308794634299 84974937410650963191951449)
      ·
        refine ⟨63731203057988222393963587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84974937410650963191951449 63731203057988222393963587)
        ·
          refine ⟨95596804586982333590945381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63731203057988222393963587 95596804586982333590945381)
          ·
            refine ⟨17924400860059187548302259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95596804586982333590945381 17924400860059187548302259)
            ·
              refine ⟨26886601290088781322453389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924400860059187548302259 26886601290088781322453389)
              ·
                refine ⟨10082475483783292995920021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26886601290088781322453389 10082475483783292995920021)
                ·
                  refine ⟨472616038302341859183751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10082475483783292995920021 472616038302341859183751)
                  ·
                    rfl

theorem cell21_2070937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_2070937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070937 prefixEnd_2070937 := by exact prefixLift 2070937
  have htrace : WordTrace (prefixWord ++ tailWord_2070937) baseStart_2070937 baseEnd_2070937 := by
    simpa [prefixWord, tailWord_2070937, baseEnd_2070937] using wordTrace_append hprefix tailTrace_2070937
  have hstable : (prefixWord ++ tailWord_2070937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070937).length < 2 ^ (prefixWord ++ tailWord_2070937).sum := by decide
  have hdescent : baseEnd_2070937 < baseStart_2070937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071030 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2071030 : Nat := 118140960795 + 2071030 * 2 ^ 59
def prefixEnd_2071030 : Nat := 4983230072969 + 3 ^ 40 * 2071030 * 2
def baseEnd_2071030 : Nat := 472637262169394364133561

theorem tailTrace_2071030 : CollatzResearch.WordTrace tailWord_2071030 prefixEnd_2071030 472637262169394364133561 := by
  unfold tailWord_2071030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721041855438718038082159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50357779791346325739543029 4721041855438718038082159)
  ·
    refine ⟨7081562783158077057123239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721041855438718038082159 7081562783158077057123239)
    ·
      refine ⟨10622344174737115585684859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081562783158077057123239 10622344174737115585684859)
      ·
        refine ⟨15933516262105673378527289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622344174737115585684859 15933516262105673378527289)
        ·
          refine ⟨11950137196579255033895467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15933516262105673378527289 11950137196579255033895467)
          ·
            refine ⟨17925205794868882550843201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950137196579255033895467 17925205794868882550843201)
            ·
              refine ⟨13443904346151661913132401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17925205794868882550843201 13443904346151661913132401)
              ·
                refine ⟨10082928259613746434849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443904346151661913132401 10082928259613746434849301)
                ·
                  refine ⟨472637262169394364133561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10082928259613746434849301 472637262169394364133561)
                  ·
                    rfl

theorem cell21_2071030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2071030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071030 prefixEnd_2071030 := by exact prefixLift 2071030
  have htrace : WordTrace (prefixWord ++ tailWord_2071030) baseStart_2071030 baseEnd_2071030 := by
    simpa [prefixWord, tailWord_2071030, baseEnd_2071030] using wordTrace_append hprefix tailTrace_2071030
  have hstable : (prefixWord ++ tailWord_2071030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071030).length < 2 ^ (prefixWord ++ tailWord_2071030).sum := by decide
  have hdescent : baseEnd_2071030 < baseStart_2071030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071075 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_2071075 : Nat := 118140960795 + 2071075 * 2 ^ 59
def prefixEnd_2071075 : Nat := 4983230072969 + 3 ^ 40 * 2071075 * 2
def baseEnd_2071075 : Nat := 472647531782484285883469

theorem tailTrace_2071075 : CollatzResearch.WordTrace tailWord_2071075 prefixEnd_2071075 472647531782484285883469 := by
  unfold tailWord_2071075
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538310971856461294702679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50358873981237640863135119 75538310971856461294702679)
  ·
    refine ⟨113307466457784691942054019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75538310971856461294702679 113307466457784691942054019)
    ·
      refine ⟨169961199686677037913081029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113307466457784691942054019 169961199686677037913081029)
      ·
        refine ⟨31867724941251944608702693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169961199686677037913081029 31867724941251944608702693)
        ·
          refine ⟨5975198426484739614131755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31867724941251944608702693 5975198426484739614131755)
          ·
            refine ⟨8962797639727109421197633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975198426484739614131755 8962797639727109421197633)
            ·
              refine ⟨6722098229795332065898225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8962797639727109421197633 6722098229795332065898225)
              ·
                refine ⟨5041573672346499049423669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722098229795332065898225 5041573672346499049423669)
                ·
                  refine ⟨472647531782484285883469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041573672346499049423669 472647531782484285883469)
                  ·
                    rfl

theorem cell21_2071075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_2071075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071075 prefixEnd_2071075 := by exact prefixLift 2071075
  have htrace : WordTrace (prefixWord ++ tailWord_2071075) baseStart_2071075 baseEnd_2071075 := by
    simpa [prefixWord, tailWord_2071075, baseEnd_2071075] using wordTrace_append hprefix tailTrace_2071075
  have hstable : (prefixWord ++ tailWord_2071075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071075).length < 2 ^ (prefixWord ++ tailWord_2071075).sum := by decide
  have hdescent : baseEnd_2071075 < baseStart_2071075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071089 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2071089 : Nat := 118140960795 + 2071089 * 2 ^ 59
def prefixEnd_2071089 : Nat := 4983230072969 + 3 ^ 40 * 2071089 * 2
def baseEnd_2071089 : Nat := 472650726773223372650107

theorem tailTrace_2071089 : CollatzResearch.WordTrace tailWord_2071089 prefixEnd_2071089 472650726773223372650107 := by
  unfold tailWord_2071089
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538821593805741685712321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50359214395870494457141547 75538821593805741685712321)
  ·
    refine ⟨56654116195354306264284241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75538821593805741685712321 56654116195354306264284241)
    ·
      refine ⟨42490587146515729698213181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56654116195354306264284241 42490587146515729698213181)
      ·
        refine ⟨15933970179943398636829943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42490587146515729698213181 15933970179943398636829943)
        ·
          refine ⟨23900955269915097955244915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933970179943398636829943 23900955269915097955244915)
          ·
            refine ⟨35851432904872646932867373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23900955269915097955244915 35851432904872646932867373)
            ·
              refine ⟨13444287339327242599825265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35851432904872646932867373 13444287339327242599825265)
              ·
                refine ⟨10083215504495431949868949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13444287339327242599825265 10083215504495431949868949)
                ·
                  refine ⟨472650726773223372650107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10083215504495431949868949 472650726773223372650107)
                  ·
                    rfl

theorem cell21_2071089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2071089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071089 prefixEnd_2071089 := by exact prefixLift 2071089
  have htrace : WordTrace (prefixWord ++ tailWord_2071089) baseStart_2071089 baseEnd_2071089 := by
    simpa [prefixWord, tailWord_2071089, baseEnd_2071089] using wordTrace_append hprefix tailTrace_2071089
  have hstable : (prefixWord ++ tailWord_2071089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071089).length < 2 ^ (prefixWord ++ tailWord_2071089).sum := by decide
  have hdescent : baseEnd_2071089 < baseStart_2071089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071109 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 3]
def baseStart_2071109 : Nat := 118140960795 + 2071109 * 2 ^ 59
def prefixEnd_2071109 : Nat := 4983230072969 + 3 ^ 40 * 2071109 * 2
def baseEnd_2071109 : Nat := 472655291045707782316733

theorem tailTrace_2071109 : CollatzResearch.WordTrace tailWord_2071109 prefixEnd_2071109 472655291045707782316733 := by
  unfold tailWord_2071109
  simp only [CollatzResearch.WordTrace]
  refine ⟨75539551053733285101440381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50359700702488856734293587 75539551053733285101440381)
  ·
    refine ⟨28327331645149981913040143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75539551053733285101440381 28327331645149981913040143)
    ·
      refine ⟨42490997467724972869560215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28327331645149981913040143 42490997467724972869560215)
      ·
        refine ⟨63736496201587459304340323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42490997467724972869560215 63736496201587459304340323)
        ·
          refine ⟨95604744302381188956510485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63736496201587459304340323 95604744302381188956510485)
          ·
            refine ⟨4481472389174118232336429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95604744302381188956510485 4481472389174118232336429)
            ·
              refine ⟨1680552145940294337126161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481472389174118232336429 1680552145940294337126161)
              ·
                refine ⟨1260414109455220752844621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680552145940294337126161 1260414109455220752844621)
                ·
                  refine ⟨472655291045707782316733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260414109455220752844621 472655291045707782316733)
                  ·
                    rfl

theorem cell21_2071109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_2071109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071109 prefixEnd_2071109 := by exact prefixLift 2071109
  have htrace : WordTrace (prefixWord ++ tailWord_2071109) baseStart_2071109 baseEnd_2071109 := by
    simpa [prefixWord, tailWord_2071109, baseEnd_2071109] using wordTrace_append hprefix tailTrace_2071109
  have hstable : (prefixWord ++ tailWord_2071109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071109).length < 2 ^ (prefixWord ++ tailWord_2071109).sum := by decide
  have hdescent : baseEnd_2071109 < baseStart_2071109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071168 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_2071168 : Nat := 118140960795 + 2071168 * 2 ^ 59
def prefixEnd_2071168 : Nat := 4983230072969 + 3 ^ 40 * 2071168 * 2
def baseEnd_2071168 : Nat := 472668755649536790833279

theorem tailTrace_2071168 : CollatzResearch.WordTrace tailWord_2071168 prefixEnd_2071168 472668755649536790833279 := by
  unfold tailWord_2071168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37770851480259769088919079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50361135307013025451892105 37770851480259769088919079)
  ·
    refine ⟨56656277220389653633378619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37770851480259769088919079 56656277220389653633378619)
    ·
      refine ⟨84984415830584480450067929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56656277220389653633378619 84984415830584480450067929)
      ·
        refine ⟨63738311872938360337550947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84984415830584480450067929 63738311872938360337550947)
        ·
          refine ⟨95607467809407540506326421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63738311872938360337550947 95607467809407540506326421)
          ·
            refine ⟨4481600053565978461234051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95607467809407540506326421 4481600053565978461234051)
            ·
              refine ⟨6722400080348967691851077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481600053565978461234051 6722400080348967691851077)
              ·
                refine ⟨1260450015065431442222077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6722400080348967691851077 1260450015065431442222077)
                ·
                  refine ⟨472668755649536790833279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260450015065431442222077 472668755649536790833279)
                  ·
                    rfl

theorem cell21_2071168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_2071168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071168 prefixEnd_2071168 := by exact prefixLift 2071168
  have htrace : WordTrace (prefixWord ++ tailWord_2071168) baseStart_2071168 baseEnd_2071168 := by
    simpa [prefixWord, tailWord_2071168, baseEnd_2071168] using wordTrace_append hprefix tailTrace_2071168
  have hstable : (prefixWord ++ tailWord_2071168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071168).length < 2 ^ (prefixWord ++ tailWord_2071168).sum := by decide
  have hdescent : baseEnd_2071168 < baseStart_2071168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071179 : List Nat := [1, 1, 1, 1, 4, 1, 2, 10]
def baseStart_2071179 : Nat := 118140960795 + 2071179 * 2 ^ 59
def prefixEnd_2071179 : Nat := 4983230072969 + 3 ^ 40 * 2071179 * 2
def baseEnd_2071179 : Nat := 157557088666467738716641

theorem tailTrace_2071179 : CollatzResearch.WordTrace tailWord_2071179 prefixEnd_2071179 157557088666467738716641 := by
  unfold tailWord_2071179
  simp only [CollatzResearch.WordTrace]
  refine ⟨75542104163479687056488591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50361402775653124704325727 75542104163479687056488591)
  ·
    refine ⟨113313156245219530584732887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75542104163479687056488591 113313156245219530584732887)
    ·
      refine ⟨169969734367829295877099331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113313156245219530584732887 169969734367829295877099331)
      ·
        refine ⟨254954601551743943815648997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169969734367829295877099331 254954601551743943815648997)
        ·
          refine ⟨47803987790951989465434187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254954601551743943815648997 47803987790951989465434187)
          ·
            refine ⟨71705981686427984198151281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47803987790951989465434187 71705981686427984198151281)
            ·
              refine ⟨53779486264820988148613461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71705981686427984198151281 53779486264820988148613461)
              ·
                refine ⟨157557088666467738716641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53779486264820988148613461 157557088666467738716641)
                ·
                  rfl

theorem cell21_2071179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_2071179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071179 prefixEnd_2071179 := by exact prefixLift 2071179
  have htrace : WordTrace (prefixWord ++ tailWord_2071179) baseStart_2071179 baseEnd_2071179 := by
    simpa [prefixWord, tailWord_2071179, baseEnd_2071179] using wordTrace_append hprefix tailTrace_2071179
  have hstable : (prefixWord ++ tailWord_2071179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071179).length < 2 ^ (prefixWord ++ tailWord_2071179).sum := by decide
  have hdescent : baseEnd_2071179 < baseStart_2071179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071182 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2071182 : Nat := 118140960795 + 2071182 * 2 ^ 59
def prefixEnd_2071182 : Nat := 4983230072969 + 3 ^ 40 * 2071182 * 2
def baseEnd_2071182 : Nat := 472671950640275877599917

theorem tailTrace_2071182 : CollatzResearch.WordTrace tailWord_2071182 prefixEnd_2071182 472671950640275877599917 := by
  unfold tailWord_2071182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442776697808602321105975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50361475721645879045898533 9442776697808602321105975)
  ·
    refine ⟨14164165046712903481658963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9442776697808602321105975 14164165046712903481658963)
    ·
      refine ⟨21246247570069355222488445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14164165046712903481658963 21246247570069355222488445)
      ·
        refine ⟨7967342838776008208433167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21246247570069355222488445 7967342838776008208433167)
        ·
          refine ⟨11951014258164012312649751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967342838776008208433167 11951014258164012312649751)
          ·
            refine ⟨17926521387246018468974627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951014258164012312649751 17926521387246018468974627)
            ·
              refine ⟨26889782080869027703461941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926521387246018468974627 26889782080869027703461941)
              ·
                refine ⟨2520917070081471347199557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26889782080869027703461941 2520917070081471347199557)
                ·
                  refine ⟨472671950640275877599917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520917070081471347199557 472671950640275877599917)
                  ·
                    rfl

theorem cell21_2071182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2071182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071182 prefixEnd_2071182 := by exact prefixLift 2071182
  have htrace : WordTrace (prefixWord ++ tailWord_2071182) baseStart_2071182 baseEnd_2071182 := by
    simpa [prefixWord, tailWord_2071182, baseEnd_2071182] using wordTrace_append hprefix tailTrace_2071182
  have hstable : (prefixWord ++ tailWord_2071182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071182).length < 2 ^ (prefixWord ++ tailWord_2071182).sum := by decide
  have hdescent : baseEnd_2071182 < baseStart_2071182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071233 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 4]
def baseStart_2071233 : Nat := 118140960795 + 2071233 * 2 ^ 59
def prefixEnd_2071233 : Nat := 4983230072969 + 3 ^ 40 * 2071233 * 2
def baseEnd_2071233 : Nat := 472683589535111122249813

theorem tailTrace_2071233 : CollatzResearch.WordTrace tailWord_2071233 prefixEnd_2071233 472683589535111122249813 := by
  unfold tailWord_2071233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75544073705284054278954353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50362715803522702852636235 75544073705284054278954353)
  ·
    refine ⟨56658055278963040709215765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75544073705284054278954353 56658055278963040709215765)
    ·
      refine ⟨2655846341201392533244489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56658055278963040709215765 2655846341201392533244489)
      ·
        refine ⟨1991884755901044399933367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655846341201392533244489 1991884755901044399933367)
        ·
          refine ⟨2987827133851566599900051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991884755901044399933367 2987827133851566599900051)
          ·
            refine ⟨4481740700777349899850077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987827133851566599900051 4481740700777349899850077)
            ·
              refine ⟨1680652762791506212443779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481740700777349899850077 1680652762791506212443779)
              ·
                refine ⟨2520979144187259318665669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680652762791506212443779 2520979144187259318665669)
                ·
                  refine ⟨472683589535111122249813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520979144187259318665669 472683589535111122249813)
                  ·
                    rfl

theorem cell21_2071233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_2071233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071233 prefixEnd_2071233 := by exact prefixLift 2071233
  have htrace : WordTrace (prefixWord ++ tailWord_2071233) baseStart_2071233 baseEnd_2071233 := by
    simpa [prefixWord, tailWord_2071233, baseEnd_2071233] using wordTrace_append hprefix tailTrace_2071233
  have hstable : (prefixWord ++ tailWord_2071233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071233).length < 2 ^ (prefixWord ++ tailWord_2071233).sum := by decide
  have hdescent : baseEnd_2071233 < baseStart_2071233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071393 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_2071393 : Nat := 118140960795 + 2071393 * 2 ^ 59
def prefixEnd_2071393 : Nat := 4983230072969 + 3 ^ 40 * 2071393 * 2
def baseEnd_2071393 : Nat := 472720103714986399582819

theorem tailTrace_2071393 : CollatzResearch.WordTrace tailWord_2071393 prefixEnd_2071393 472720103714986399582819 := by
  unfold tailWord_2071393
  simp only [CollatzResearch.WordTrace]
  refine ⟨75549909384704401604778833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50366606256469601069852555 75549909384704401604778833)
  ·
    refine ⟨56662432038528301203584125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75549909384704401604778833 56662432038528301203584125)
    ·
      refine ⟨21248412014448112951344047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56662432038528301203584125 21248412014448112951344047)
      ·
        refine ⟨31872618021672169427016071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21248412014448112951344047 31872618021672169427016071)
        ·
          refine ⟨47808927032508254140524107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31872618021672169427016071 47808927032508254140524107)
          ·
            refine ⟨71713390548762381210786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47808927032508254140524107 71713390548762381210786161)
            ·
              refine ⟨53785042911571785908089621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71713390548762381210786161 53785042911571785908089621)
              ·
                refine ⟨2521173886479927464441701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53785042911571785908089621 2521173886479927464441701)
                ·
                  refine ⟨472720103714986399582819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521173886479927464441701 472720103714986399582819)
                  ·
                    rfl

theorem cell21_2071393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_2071393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071393 prefixEnd_2071393 := by exact prefixLift 2071393
  have htrace : WordTrace (prefixWord ++ tailWord_2071393) baseStart_2071393 baseEnd_2071393 := by
    simpa [prefixWord, tailWord_2071393, baseEnd_2071393] using wordTrace_append hprefix tailTrace_2071393
  have hstable : (prefixWord ++ tailWord_2071393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071393).length < 2 ^ (prefixWord ++ tailWord_2071393).sum := by decide
  have hdescent : baseEnd_2071393 < baseStart_2071393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071396 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2071396 : Nat := 118140960795 + 2071396 * 2 ^ 59
def prefixEnd_2071396 : Nat := 4983230072969 + 3 ^ 40 * 2071396 * 2
def baseEnd_2071396 : Nat := 472720788355859061032813

theorem tailTrace_2071396 : CollatzResearch.WordTrace tailWord_2071396 prefixEnd_2071396 472720788355859061032813 := by
  unfold tailWord_2071396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37775009401846766558569021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50366679202462355411425361 37775009401846766558569021)
  ·
    refine ⟨14165628525692537459463383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37775009401846766558569021 14165628525692537459463383)
    ·
      refine ⟨21248442788538806189195075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14165628525692537459463383 21248442788538806189195075)
      ·
        refine ⟨31872664182808209283792613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21248442788538806189195075 31872664182808209283792613)
        ·
          refine ⟨5976124534276539240711115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31872664182808209283792613 5976124534276539240711115)
          ·
            refine ⟨8964186801414808861066673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976124534276539240711115 8964186801414808861066673)
            ·
              refine ⟨6723140101061106645800005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964186801414808861066673 6723140101061106645800005)
              ·
                refine ⟨1260588768948957496087501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6723140101061106645800005 1260588768948957496087501)
                ·
                  refine ⟨472720788355859061032813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260588768948957496087501 472720788355859061032813)
                  ·
                    rfl

theorem cell21_2071396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2071396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071396 prefixEnd_2071396 := by exact prefixLift 2071396
  have htrace : WordTrace (prefixWord ++ tailWord_2071396) baseStart_2071396 baseEnd_2071396 := by
    simpa [prefixWord, tailWord_2071396, baseEnd_2071396] using wordTrace_append hprefix tailTrace_2071396
  have hstable : (prefixWord ++ tailWord_2071396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071396).length < 2 ^ (prefixWord ++ tailWord_2071396).sum := by decide
  have hdescent : baseEnd_2071396 < baseStart_2071396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071455 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_2071455 : Nat := 118140960795 + 2071455 * 2 ^ 59
def prefixEnd_2071455 : Nat := 4983230072969 + 3 ^ 40 * 2071455 * 2
def baseEnd_2071455 : Nat := 472734252959688069549359

theorem tailTrace_2071455 : CollatzResearch.WordTrace tailWord_2071455 prefixEnd_2071455 472734252959688069549359 := by
  unfold tailWord_2071455
  simp only [CollatzResearch.WordTrace]
  refine ⟨75552170710479786193535819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50368113806986524129023879 75552170710479786193535819)
  ·
    refine ⟨113328256065719679290303729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75552170710479786193535819 113328256065719679290303729)
    ·
      refine ⟨84996192049289759467727797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113328256065719679290303729 84996192049289759467727797)
      ·
        refine ⟨7968393004620914950099481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84996192049289759467727797 7968393004620914950099481)
        ·
          refine ⟨5976294753465686212574611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7968393004620914950099481 5976294753465686212574611)
          ·
            refine ⟨8964442130198529318861917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976294753465686212574611 8964442130198529318861917)
            ·
              refine ⟨3361665798824448494573219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8964442130198529318861917 3361665798824448494573219)
              ·
                refine ⟨5042498698236672741859829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361665798824448494573219 5042498698236672741859829)
                ·
                  refine ⟨472734252959688069549359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042498698236672741859829 472734252959688069549359)
                  ·
                    rfl

theorem cell21_2071455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_2071455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071455 prefixEnd_2071455 := by exact prefixLift 2071455
  have htrace : WordTrace (prefixWord ++ tailWord_2071455) baseStart_2071455 baseEnd_2071455 := by
    simpa [prefixWord, tailWord_2071455, baseEnd_2071455] using wordTrace_append hprefix tailTrace_2071455
  have hstable : (prefixWord ++ tailWord_2071455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071455).length < 2 ^ (prefixWord ++ tailWord_2071455).sum := by decide
  have hdescent : baseEnd_2071455 < baseStart_2071455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071506 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2071506 : Nat := 118140960795 + 2071506 * 2 ^ 59
def prefixEnd_2071506 : Nat := 4983230072969 + 3 ^ 40 * 2071506 * 2
def baseEnd_2071506 : Nat := 472745891854523314199255

theorem tailTrace_2071506 : CollatzResearch.WordTrace tailWord_2071506 prefixEnd_2071506 472745891854523314199255 := by
  unfold tailWord_2071506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888507708323755475910593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50369353888863347935761581 18888507708323755475910593)
  ·
    refine ⟨14166380781242816606932945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18888507708323755475910593 14166380781242816606932945)
    ·
      refine ⟨10624785585932112455199709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14166380781242816606932945 10624785585932112455199709)
      ·
        refine ⟨3984294594724542170699891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10624785585932112455199709 3984294594724542170699891)
        ·
          refine ⟨5976441892086813256049837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984294594724542170699891 5976441892086813256049837)
          ·
            refine ⟨2241165709532554971018689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5976441892086813256049837 2241165709532554971018689)
            ·
              refine ⟨1680874282149416228264017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241165709532554971018689 1680874282149416228264017)
              ·
                refine ⟨1260655711612062171198013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680874282149416228264017 1260655711612062171198013)
                ·
                  refine ⟨472745891854523314199255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260655711612062171198013 472745891854523314199255)
                  ·
                    rfl

theorem cell21_2071506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2071506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071506 prefixEnd_2071506 := by exact prefixLift 2071506
  have htrace : WordTrace (prefixWord ++ tailWord_2071506) baseStart_2071506 baseEnd_2071506 := by
    simpa [prefixWord, tailWord_2071506, baseEnd_2071506] using wordTrace_append hprefix tailTrace_2071506
  have hstable : (prefixWord ++ tailWord_2071506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071506).length < 2 ^ (prefixWord ++ tailWord_2071506).sum := by decide
  have hdescent : baseEnd_2071506 < baseStart_2071506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071517 : List Nat := [1, 4, 3, 1, 2, 3, 1, 6]
def baseStart_2071517 : Nat := 118140960795 + 2071517 * 2 ^ 59
def prefixEnd_2071517 : Nat := 4983230072969 + 3 ^ 40 * 2071517 * 2
def baseEnd_2071517 : Nat := 157582800734796579838633

theorem tailTrace_2071517 : CollatzResearch.WordTrace tailWord_2071517 prefixEnd_2071517 157582800734796579838633 := by
  unfold tailWord_2071517
  simp only [CollatzResearch.WordTrace]
  refine ⟨75554432036255170782292805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50369621357503447188195203 75554432036255170782292805)
  ·
    refine ⟨14166456006797844521679901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75554432036255170782292805 14166456006797844521679901)
    ·
      refine ⟨5312421002549191695629963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14166456006797844521679901 5312421002549191695629963)
      ·
        refine ⟨7968631503823787543444945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312421002549191695629963 7968631503823787543444945)
        ·
          refine ⟨5976473627867840657583709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7968631503823787543444945 5976473627867840657583709)
          ·
            refine ⟨2241177610450440246593891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5976473627867840657583709 2241177610450440246593891)
            ·
              refine ⟨3361766415675660369890837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241177610450440246593891 3361766415675660369890837)
              ·
                refine ⟨157582800734796579838633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3361766415675660369890837 157582800734796579838633)
                ·
                  rfl

theorem cell21_2071517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_2071517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071517 prefixEnd_2071517 := by exact prefixLift 2071517
  have htrace : WordTrace (prefixWord ++ tailWord_2071517) baseStart_2071517 baseEnd_2071517 := by
    simpa [prefixWord, tailWord_2071517, baseEnd_2071517] using wordTrace_append hprefix tailTrace_2071517
  have hstable : (prefixWord ++ tailWord_2071517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071517).length < 2 ^ (prefixWord ++ tailWord_2071517).sum := by decide
  have hdescent : baseEnd_2071517 < baseStart_2071517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071540 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2071540 : Nat := 118140960795 + 2071540 * 2 ^ 59
def prefixEnd_2071540 : Nat := 4983230072969 + 3 ^ 40 * 2071540 * 2
def baseEnd_2071540 : Nat := 472753651117746810632519

theorem tailTrace_2071540 : CollatzResearch.WordTrace tailWord_2071540 prefixEnd_2071540 472753651117746810632519 := by
  unfold tailWord_2071540
  simp only [CollatzResearch.WordTrace]
  refine ⟨37777635457585922855190037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50370180610114563806920049 37777635457585922855190037)
  ·
    refine ⟨1770826662074340133837033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37777635457585922855190037 1770826662074340133837033)
    ·
      refine ⟨1328119996555755100377775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1770826662074340133837033 1328119996555755100377775)
      ·
        refine ⟨1992179994833632650566663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328119996555755100377775 1992179994833632650566663)
        ·
          refine ⟨2988269992250448975849995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992179994833632650566663 2988269992250448975849995)
          ·
            refine ⟨4482404988375673463774993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988269992250448975849995 4482404988375673463774993)
            ·
              refine ⟨3361803741281755097831245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482404988375673463774993 3361803741281755097831245)
              ·
                refine ⟨1260676402980658161686717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361803741281755097831245 1260676402980658161686717)
                ·
                  refine ⟨472753651117746810632519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260676402980658161686717 472753651117746810632519)
                  ·
                    rfl

theorem cell21_2071540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2071540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071540 prefixEnd_2071540 := by exact prefixLift 2071540
  have htrace : WordTrace (prefixWord ++ tailWord_2071540) baseStart_2071540 baseEnd_2071540 := by
    simpa [prefixWord, tailWord_2071540, baseEnd_2071540] using wordTrace_append hprefix tailTrace_2071540
  have hstable : (prefixWord ++ tailWord_2071540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071540).length < 2 ^ (prefixWord ++ tailWord_2071540).sum := by decide
  have hdescent : baseEnd_2071540 < baseStart_2071540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071548 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2071548 : Nat := 118140960795 + 2071548 * 2 ^ 59
def prefixEnd_2071548 : Nat := 4983230072969 + 3 ^ 40 * 2071548 * 2
def baseEnd_2071548 : Nat := 472755476826740574499169

theorem tailTrace_2071548 : CollatzResearch.WordTrace tailWord_2071548 prefixEnd_2071548 472755476826740574499169 := by
  unfold tailWord_2071548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37777781349571431538335649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50370375132761908717780865 37777781349571431538335649)
  ·
    refine ⟨28333336012178573653751737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37777781349571431538335649 28333336012178573653751737)
    ·
      refine ⟨21250002009133930240313803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28333336012178573653751737 21250002009133930240313803)
      ·
        refine ⟨31875003013700895360470705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250002009133930240313803 31875003013700895360470705)
        ·
          refine ⟨23906252260275671520353029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31875003013700895360470705 23906252260275671520353029)
          ·
            refine ⟨4482422298801688410066193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23906252260275671520353029 4482422298801688410066193)
            ·
              refine ⟨3361816724101266307549645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482422298801688410066193 3361816724101266307549645)
              ·
                refine ⟨1260681271537974865331117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361816724101266307549645 1260681271537974865331117)
                ·
                  refine ⟨472755476826740574499169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260681271537974865331117 472755476826740574499169)
                  ·
                    rfl

theorem cell21_2071548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2071548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071548 prefixEnd_2071548 := by exact prefixLift 2071548
  have htrace : WordTrace (prefixWord ++ tailWord_2071548) baseStart_2071548 baseEnd_2071548 := by
    simpa [prefixWord, tailWord_2071548, baseEnd_2071548] using wordTrace_append hprefix tailTrace_2071548
  have hstable : (prefixWord ++ tailWord_2071548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071548).length < 2 ^ (prefixWord ++ tailWord_2071548).sum := by decide
  have hdescent : baseEnd_2071548 < baseStart_2071548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071559 : List Nat := [1, 1, 4, 3, 1, 1, 10]
def baseStart_2071559 : Nat := 118140960795 + 2071559 * 2 ^ 59
def prefixEnd_2071559 : Nat := 4983230072969 + 3 ^ 40 * 2071559 * 2
def baseEnd_2071559 : Nat := 52528665241845222201757

theorem tailTrace_2071559 : CollatzResearch.WordTrace tailWord_2071559 prefixEnd_2071559 52528665241845222201757 := by
  unfold tailWord_2071559
  simp only [CollatzResearch.WordTrace]
  refine ⟨75555963902103011955321731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50370642601402007970214487 75555963902103011955321731)
  ·
    refine ⟨113333945853154517932982597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75555963902103011955321731 113333945853154517932982597)
    ·
      refine ⟨21250114847466472112434237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113333945853154517932982597 21250114847466472112434237)
      ·
        refine ⟨7968793067799927042162839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21250114847466472112434237 7968793067799927042162839)
        ·
          refine ⟨11953189601699890563244259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968793067799927042162839 11953189601699890563244259)
          ·
            refine ⟨17929784402549835844866389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953189601699890563244259 17929784402549835844866389)
            ·
              refine ⟨52528665241845222201757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17929784402549835844866389 52528665241845222201757)
              ·
                rfl

theorem cell21_2071559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_2071559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071559 prefixEnd_2071559 := by exact prefixLift 2071559
  have htrace : WordTrace (prefixWord ++ tailWord_2071559) baseStart_2071559 baseEnd_2071559 := by
    simpa [prefixWord, tailWord_2071559, baseEnd_2071559] using wordTrace_append hprefix tailTrace_2071559
  have hstable : (prefixWord ++ tailWord_2071559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071559).length < 2 ^ (prefixWord ++ tailWord_2071559).sum := by decide
  have hdescent : baseEnd_2071559 < baseStart_2071559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071562 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_2071562 : Nat := 118140960795 + 2071562 * 2 ^ 59
def prefixEnd_2071562 : Nat := 4983230072969 + 3 ^ 40 * 2071562 * 2
def baseEnd_2071562 : Nat := 472758671817479661265807

theorem tailTrace_2071562 : CollatzResearch.WordTrace tailWord_2071562 prefixEnd_2071562 472758671817479661265807 := by
  unfold tailWord_2071562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889018330273035866920235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50370715547394762311787293 18889018330273035866920235)
  ·
    refine ⟨28333527495409553800380353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889018330273035866920235 28333527495409553800380353)
    ·
      refine ⟨21250145621557165350285265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28333527495409553800380353 21250145621557165350285265)
      ·
        refine ⟨15937609216167874012713949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21250145621557165350285265 15937609216167874012713949)
        ·
          refine ⟨5976603456062952754767731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15937609216167874012713949 5976603456062952754767731)
          ·
            refine ⟨8964905184094429132151597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976603456062952754767731 8964905184094429132151597)
            ·
              refine ⟨3361839444035410924556849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8964905184094429132151597 3361839444035410924556849)
              ·
                refine ⟨2521379583026558193417637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361839444035410924556849 2521379583026558193417637)
                ·
                  refine ⟨472758671817479661265807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521379583026558193417637 472758671817479661265807)
                  ·
                    rfl

theorem cell21_2071562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_2071562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071562 prefixEnd_2071562 := by exact prefixLift 2071562
  have htrace : WordTrace (prefixWord ++ tailWord_2071562) baseStart_2071562 baseEnd_2071562 := by
    simpa [prefixWord, tailWord_2071562, baseEnd_2071562] using wordTrace_append hprefix tailTrace_2071562
  have hstable : (prefixWord ++ tailWord_2071562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071562).length < 2 ^ (prefixWord ++ tailWord_2071562).sum := by decide
  have hdescent : baseEnd_2071562 < baseStart_2071562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071624 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_2071624 : Nat := 118140960795 + 2071624 * 2 ^ 59
def prefixEnd_2071624 : Nat := 4983230072969 + 3 ^ 40 * 2071624 * 2
def baseEnd_2071624 : Nat := 472772821062181331232347

theorem tailTrace_2071624 : CollatzResearch.WordTrace tailWord_2071624 prefixEnd_2071624 472772821062181331232347 := by
  unfold tailWord_2071624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37779167323433764028218963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50372223097911685370958617 37779167323433764028218963)
  ·
    refine ⟨56668750985150646042328445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37779167323433764028218963 56668750985150646042328445)
    ·
      refine ⟨21250781619431492265873167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56668750985150646042328445 21250781619431492265873167)
      ·
        refine ⟨31876172429147238398809751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250781619431492265873167 31876172429147238398809751)
        ·
          refine ⟨47814258643720857598214627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31876172429147238398809751 47814258643720857598214627)
          ·
            refine ⟨71721387965581286397321941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47814258643720857598214627 71721387965581286397321941)
            ·
              refine ⟨1680970030443311399937233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71721387965581286397321941 1680970030443311399937233)
              ·
                refine ⟨1260727522832483549952925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680970030443311399937233 1260727522832483549952925)
                ·
                  refine ⟨472772821062181331232347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260727522832483549952925 472772821062181331232347)
                  ·
                    rfl

theorem cell21_2071624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_2071624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071624 prefixEnd_2071624 := by exact prefixLift 2071624
  have htrace : WordTrace (prefixWord ++ tailWord_2071624) baseStart_2071624 baseEnd_2071624 := by
    simpa [prefixWord, tailWord_2071624, baseEnd_2071624] using wordTrace_append hprefix tailTrace_2071624
  have hstable : (prefixWord ++ tailWord_2071624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071624).length < 2 ^ (prefixWord ++ tailWord_2071624).sum := by decide
  have hdescent : baseEnd_2071624 < baseStart_2071624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071669 : List Nat := [1, 3, 4, 3, 2, 8]
def baseStart_2071669 : Nat := 118140960795 + 2071669 * 2 ^ 59
def prefixEnd_2071669 : Nat := 4983230072969 + 3 ^ 40 * 2071669 * 2
def baseEnd_2071669 : Nat := 17510484839824861221565

theorem tailTrace_2071669 : CollatzResearch.WordTrace tailWord_2071669 prefixEnd_2071669 17510484839824861221565 := by
  unfold tailWord_2071669
  simp only [CollatzResearch.WordTrace]
  refine ⟨75559975931704500741826061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50373317287803000494550707 75559975931704500741826061)
  ·
    refine ⟨28334990974389187778184773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75559975931704500741826061 28334990974389187778184773)
    ·
      refine ⟨5312810807697972708409645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28334990974389187778184773 5312810807697972708409645)
      ·
        refine ⟨1992304052886739765653617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5312810807697972708409645 1992304052886739765653617)
        ·
          refine ⟨1494228039665054824240213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1992304052886739765653617 1494228039665054824240213)
          ·
            refine ⟨17510484839824861221565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1494228039665054824240213 17510484839824861221565)
            ·
              rfl

theorem cell21_2071669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 8].length) (baseStart_2071669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071669 prefixEnd_2071669 := by exact prefixLift 2071669
  have htrace : WordTrace (prefixWord ++ tailWord_2071669) baseStart_2071669 baseEnd_2071669 := by
    simpa [prefixWord, tailWord_2071669, baseEnd_2071669] using wordTrace_append hprefix tailTrace_2071669
  have hstable : (prefixWord ++ tailWord_2071669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071669).length < 2 ^ (prefixWord ++ tailWord_2071669).sum := by decide
  have hdescent : baseEnd_2071669 < baseStart_2071669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071680 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_2071680 : Nat := 118140960795 + 2071680 * 2 ^ 59
def prefixEnd_2071680 : Nat := 4983230072969 + 3 ^ 40 * 2071680 * 2
def baseEnd_2071680 : Nat := 472785601025137678298899

theorem tailTrace_2071680 : CollatzResearch.WordTrace tailWord_2071680 prefixEnd_2071680 472785601025137678298899 := by
  unfold tailWord_2071680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37780188567332324810238247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50373584756443099746984329 37780188567332324810238247)
  ·
    refine ⟨56670282850998487215357371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37780188567332324810238247 56670282850998487215357371)
    ·
      refine ⟨85005424276497730823036057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56670282850998487215357371 85005424276497730823036057)
      ·
        refine ⟨63754068207373298117277043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85005424276497730823036057 63754068207373298117277043)
        ·
          refine ⟨95631102311059947175915565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63754068207373298117277043 95631102311059947175915565)
          ·
            refine ⟨35861663366647480190968337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95631102311059947175915565 35861663366647480190968337)
            ·
              refine ⟨26896247524985610143226253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35861663366647480190968337 26896247524985610143226253)
              ·
                refine ⟨10086092821869603803709845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26896247524985610143226253 10086092821869603803709845)
                ·
                  refine ⟨472785601025137678298899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10086092821869603803709845 472785601025137678298899)
                  ·
                    rfl

theorem cell21_2071680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_2071680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071680 prefixEnd_2071680 := by exact prefixLift 2071680
  have htrace : WordTrace (prefixWord ++ tailWord_2071680) baseStart_2071680 baseEnd_2071680 := by
    simpa [prefixWord, tailWord_2071680, baseEnd_2071680] using wordTrace_append hprefix tailTrace_2071680
  have hstable : (prefixWord ++ tailWord_2071680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071680).length < 2 ^ (prefixWord ++ tailWord_2071680).sum := by decide
  have hdescent : baseEnd_2071680 < baseStart_2071680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071683 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 3]
def baseStart_2071683 : Nat := 118140960795 + 2071683 * 2 ^ 59
def prefixEnd_2071683 : Nat := 4983230072969 + 3 ^ 40 * 2071683 * 2
def baseEnd_2071683 : Nat := 472786285666010339748893

theorem tailTrace_2071683 : CollatzResearch.WordTrace tailWord_2071683 prefixEnd_2071683 472786285666010339748893 := by
  unfold tailWord_2071683
  simp only [CollatzResearch.WordTrace]
  refine ⟨75560486553653781132835703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50373657702435854088557135 75560486553653781132835703)
  ·
    refine ⟨113340729830480671699253555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75560486553653781132835703 113340729830480671699253555)
    ·
      refine ⟨170011094745721007548880333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113340729830480671699253555 170011094745721007548880333)
      ·
        refine ⟨63754160529645377830830125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170011094745721007548880333 63754160529645377830830125)
        ·
          refine ⟨23907810198617016686561297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63754160529645377830830125 23907810198617016686561297)
          ·
            refine ⟨17930857648962762514920973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23907810198617016686561297 17930857648962762514920973)
            ·
              refine ⟨6724071618361035943095365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17930857648962762514920973 6724071618361035943095365)
              ·
                refine ⟨1260763428442694239330381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6724071618361035943095365 1260763428442694239330381)
                ·
                  refine ⟨472786285666010339748893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260763428442694239330381 472786285666010339748893)
                  ·
                    rfl

theorem cell21_2071683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].length) (baseStart_2071683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071683 prefixEnd_2071683 := by exact prefixLift 2071683
  have htrace : WordTrace (prefixWord ++ tailWord_2071683) baseStart_2071683 baseEnd_2071683 := by
    simpa [prefixWord, tailWord_2071683, baseEnd_2071683] using wordTrace_append hprefix tailTrace_2071683
  have hstable : (prefixWord ++ tailWord_2071683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071683).length < 2 ^ (prefixWord ++ tailWord_2071683).sum := by decide
  have hdescent : baseEnd_2071683 < baseStart_2071683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071776 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_2071776 : Nat := 118140960795 + 2071776 * 2 ^ 59
def prefixEnd_2071776 : Nat := 4983230072969 + 3 ^ 40 * 2071776 * 2
def baseEnd_2071776 : Nat := 472807509533062844698703

theorem tailTrace_2071776 : CollatzResearch.WordTrace tailWord_2071776 prefixEnd_2071776 472807509533062844698703 := by
  unfold tailWord_2071776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781939271158429007985591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50375919028211238677314121 37781939271158429007985591)
  ·
    refine ⟨56672908906737643511978387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37781939271158429007985591 56672908906737643511978387)
    ·
      refine ⟨85009363360106465267967581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56672908906737643511978387 85009363360106465267967581)
      ·
        refine ⟨31878511260039924475487843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85009363360106465267967581 31878511260039924475487843)
        ·
          refine ⟨47817766890059886713231765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31878511260039924475487843 47817766890059886713231765)
          ·
            refine ⟨2241457822971557189682739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47817766890059886713231765 2241457822971557189682739)
            ·
              refine ⟨3362186734457335784524109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241457822971557189682739 3362186734457335784524109)
              ·
                refine ⟨1260820025421500919196541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3362186734457335784524109 1260820025421500919196541)
                ·
                  refine ⟨472807509533062844698703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260820025421500919196541 472807509533062844698703)
                  ·
                    rfl

theorem cell21_2071776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_2071776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071776 prefixEnd_2071776 := by exact prefixLift 2071776
  have htrace : WordTrace (prefixWord ++ tailWord_2071776) baseStart_2071776 baseEnd_2071776 := by
    simpa [prefixWord, tailWord_2071776, baseEnd_2071776] using wordTrace_append hprefix tailTrace_2071776
  have hstable : (prefixWord ++ tailWord_2071776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071776).length < 2 ^ (prefixWord ++ tailWord_2071776).sum := by decide
  have hdescent : baseEnd_2071776 < baseStart_2071776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071787 : List Nat := [1, 1, 1, 1, 2, 8, 7]
def baseStart_2071787 : Nat := 118140960795 + 2071787 * 2 ^ 59
def prefixEnd_2071787 : Nat := 4983230072969 + 3 ^ 40 * 2071787 * 2
def baseEnd_2071787 : Nat := 52534446653658807779483

theorem tailTrace_2071787 : CollatzResearch.WordTrace tailWord_2071787 prefixEnd_2071787 52534446653658807779483 := by
  unfold tailWord_2071787
  simp only [CollatzResearch.WordTrace]
  refine ⟨75564279745277006894621615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50376186496851337929747743 75564279745277006894621615)
  ·
    refine ⟨113346419617915510341932423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75564279745277006894621615 113346419617915510341932423)
    ·
      refine ⟨170019629426873265512898635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113346419617915510341932423 170019629426873265512898635)
      ·
        refine ⟨255029444140309898269347953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170019629426873265512898635 255029444140309898269347953)
        ·
          refine ⟨191272083105232423702010965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255029444140309898269347953 191272083105232423702010965)
          ·
            refine ⟨2241469723889442465257941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 191272083105232423702010965 2241469723889442465257941)
            ·
              refine ⟨52534446653658807779483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2241469723889442465257941 52534446653658807779483)
              ·
                rfl

theorem cell21_2071787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 7].length) (baseStart_2071787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071787 prefixEnd_2071787 := by exact prefixLift 2071787
  have htrace : WordTrace (prefixWord ++ tailWord_2071787) baseStart_2071787 baseEnd_2071787 := by
    simpa [prefixWord, tailWord_2071787, baseEnd_2071787] using wordTrace_append hprefix tailTrace_2071787
  have hstable : (prefixWord ++ tailWord_2071787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071787).length < 2 ^ (prefixWord ++ tailWord_2071787).sum := by decide
  have hdescent : baseEnd_2071787 < baseStart_2071787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071804 : List Nat := [2, 2, 2, 1, 5, 1, 2, 6]
def baseStart_2071804 : Nat := 118140960795 + 2071804 * 2 ^ 59
def prefixEnd_2071804 : Nat := 4983230072969 + 3 ^ 40 * 2071804 * 2
def baseEnd_2071804 : Nat := 157604633171513672743993

theorem tailTrace_2071804 : CollatzResearch.WordTrace tailWord_2071804 prefixEnd_2071804 157604633171513672743993 := by
  unfold tailWord_2071804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782449893107709398995233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50376599857476945865326977 37782449893107709398995233)
  ·
    refine ⟨28336837419830782049246425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37782449893107709398995233 28336837419830782049246425)
    ·
      refine ⟨21252628064873086536934819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28336837419830782049246425 21252628064873086536934819)
      ·
        refine ⟨31878942097309629805402229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21252628064873086536934819 31878942097309629805402229)
        ·
          refine ⟨2988650821622777794256459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31878942097309629805402229 2988650821622777794256459)
          ·
            refine ⟨4482976232434166691384689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988650821622777794256459 4482976232434166691384689)
            ·
              refine ⟨3362232174325625018538517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482976232434166691384689 3362232174325625018538517)
              ·
                refine ⟨157604633171513672743993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3362232174325625018538517 157604633171513672743993)
                ·
                  rfl

theorem cell21_2071804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_2071804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071804 prefixEnd_2071804 := by exact prefixLift 2071804
  have htrace : WordTrace (prefixWord ++ tailWord_2071804) baseStart_2071804 baseEnd_2071804 := by
    simpa [prefixWord, tailWord_2071804, baseEnd_2071804] using wordTrace_append hprefix tailTrace_2071804
  have hstable : (prefixWord ++ tailWord_2071804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071804).length < 2 ^ (prefixWord ++ tailWord_2071804).sum := by decide
  have hdescent : baseEnd_2071804 < baseStart_2071804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071911 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_2071911 : Nat := 118140960795 + 2071911 * 2 ^ 59
def prefixEnd_2071911 : Nat := 4983230072969 + 3 ^ 40 * 2071911 * 2
def baseEnd_2071911 : Nat := 472838318372332609948427

theorem tailTrace_2071911 : CollatzResearch.WordTrace tailWord_2071911 prefixEnd_2071911 472838318372332609948427 := by
  unfold tailWord_2071911
  simp only [CollatzResearch.WordTrace]
  refine ⟨75568802396827776072135587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50379201597885184048090391 75568802396827776072135587)
  ·
    refine ⟨113353203595241664108203381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75568802396827776072135587 113353203595241664108203381)
    ·
      refine ⟨10626862837053906010144067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113353203595241664108203381 10626862837053906010144067)
      ·
        refine ⟨15940294255580859015216101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626862837053906010144067 15940294255580859015216101)
        ·
          refine ⟨2988805172921411065353019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15940294255580859015216101 2988805172921411065353019)
          ·
            refine ⟨4483207759382116598029529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988805172921411065353019 4483207759382116598029529)
            ·
              refine ⟨3362405819536587448522147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4483207759382116598029529 3362405819536587448522147)
              ·
                refine ⟨5043608729304881172783221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362405819536587448522147 5043608729304881172783221)
                ·
                  refine ⟨472838318372332609948427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5043608729304881172783221 472838318372332609948427)
                  ·
                    rfl

theorem cell21_2071911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_2071911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071911 prefixEnd_2071911 := by exact prefixLift 2071911
  have htrace : WordTrace (prefixWord ++ tailWord_2071911) baseStart_2071911 baseEnd_2071911 := by
    simpa [prefixWord, tailWord_2071911, baseEnd_2071911] using wordTrace_append hprefix tailTrace_2071911
  have hstable : (prefixWord ++ tailWord_2071911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071911).length < 2 ^ (prefixWord ++ tailWord_2071911).sum := by decide
  have hdescent : baseEnd_2071911 < baseStart_2071911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071939 : List Nat := [1, 1, 1, 3, 5, 2, 1, 7]
def baseStart_2071939 : Nat := 118140960795 + 2071939 * 2 ^ 59
def prefixEnd_2071939 : Nat := 4983230072969 + 3 ^ 40 * 2071939 * 2
def baseEnd_2071939 : Nat := 157614902784603594493901

theorem tailTrace_2071939 : CollatzResearch.WordTrace tailWord_2071939 prefixEnd_2071939 157614902784603594493901 := by
  unfold tailWord_2071939
  simp only [CollatzResearch.WordTrace]
  refine ⟨75569823640726336854154871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50379882427150891236103247 75569823640726336854154871)
  ·
    refine ⟨113354735461089505281232307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75569823640726336854154871 113354735461089505281232307)
    ·
      refine ⟨170032103191634257921848461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113354735461089505281232307 170032103191634257921848461)
      ·
        refine ⟨63762038696862846720693173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170032103191634257921848461 63762038696862846720693173)
        ·
          refine ⟨5977691127830891880064985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63762038696862846720693173 5977691127830891880064985)
          ·
            refine ⟨4483268345873168910048739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5977691127830891880064985 4483268345873168910048739)
            ·
              refine ⟨6724902518809753365073109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483268345873168910048739 6724902518809753365073109)
              ·
                refine ⟨157614902784603594493901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6724902518809753365073109 157614902784603594493901)
                ·
                  rfl

theorem cell21_2071939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_2071939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071939 prefixEnd_2071939 := by exact prefixLift 2071939
  have htrace : WordTrace (prefixWord ++ tailWord_2071939) baseStart_2071939 baseEnd_2071939 := by
    simpa [prefixWord, tailWord_2071939, baseEnd_2071939] using wordTrace_append hprefix tailTrace_2071939
  have hstable : (prefixWord ++ tailWord_2071939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071939).length < 2 ^ (prefixWord ++ tailWord_2071939).sum := by decide
  have hdescent : baseEnd_2071939 < baseStart_2071939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071945 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 3]
def baseStart_2071945 : Nat := 118140960795 + 2071945 * 2 ^ 59
def prefixEnd_2071945 : Nat := 4983230072969 + 3 ^ 40 * 2071945 * 2
def baseEnd_2071945 : Nat := 472846077635556106381691

theorem tailTrace_2071945 : CollatzResearch.WordTrace tailWord_2071945 prefixEnd_2071945 472846077635556106381691 := by
  unfold tailWord_2071945
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570042478704599878873289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50380028319136399919248859 75570042478704599878873289)
  ·
    refine ⟨56677531859028449909154967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75570042478704599878873289 56677531859028449909154967)
    ·
      refine ⟨85016297788542674863732451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56677531859028449909154967 85016297788542674863732451)
      ·
        refine ⟨127524446682814012295598677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85016297788542674863732451 127524446682814012295598677)
        ·
          refine ⟨1494427109564226706589047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 127524446682814012295598677 1494427109564226706589047)
          ·
            refine ⟨2241640664346340059883571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494427109564226706589047 2241640664346340059883571)
            ·
              refine ⟨3362460996519510089825357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241640664346340059883571 3362460996519510089825357)
              ·
                refine ⟨1260922873694816283684509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3362460996519510089825357 1260922873694816283684509)
                ·
                  refine ⟨472846077635556106381691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260922873694816283684509 472846077635556106381691)
                  ·
                    rfl

theorem cell21_2071945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_2071945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071945 prefixEnd_2071945 := by exact prefixLift 2071945
  have htrace : WordTrace (prefixWord ++ tailWord_2071945) baseStart_2071945 baseEnd_2071945 := by
    simpa [prefixWord, tailWord_2071945, baseEnd_2071945] using wordTrace_append hprefix tailTrace_2071945
  have hstable : (prefixWord ++ tailWord_2071945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071945).length < 2 ^ (prefixWord ++ tailWord_2071945).sum := by decide
  have hdescent : baseEnd_2071945 < baseStart_2071945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071956 : List Nat := [2, 4, 2, 1, 2, 3, 7]
def baseStart_2071956 : Nat := 118140960795 + 2071956 * 2 ^ 59
def prefixEnd_2071956 : Nat := 4983230072969 + 3 ^ 40 * 2071956 * 2
def baseEnd_2071956 : Nat := 52538731998380281299815

theorem tailTrace_2071956 : CollatzResearch.WordTrace tailWord_2071956 prefixEnd_2071956 52538731998380281299815 := by
  unfold tailWord_2071956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785221840832374378761861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50380295787776499171682481 37785221840832374378761861)
  ·
    refine ⟨7084729095156070196017849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37785221840832374378761861 7084729095156070196017849)
    ·
      refine ⟨5313546821367052647013387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7084729095156070196017849 5313546821367052647013387)
      ·
        refine ⟨7970320232050578970520081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313546821367052647013387 7970320232050578970520081)
        ·
          refine ⟨5977740174037934227890061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7970320232050578970520081 5977740174037934227890061)
          ·
            refine ⟨2241652565264225335458773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5977740174037934227890061 2241652565264225335458773)
            ·
              refine ⟨52538731998380281299815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2241652565264225335458773 52538731998380281299815)
              ·
                rfl

theorem cell21_2071956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 7].length) (baseStart_2071956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071956 prefixEnd_2071956 := by exact prefixLift 2071956
  have htrace : WordTrace (prefixWord ++ tailWord_2071956) baseStart_2071956 baseEnd_2071956 := by
    simpa [prefixWord, tailWord_2071956, baseEnd_2071956] using wordTrace_append hprefix tailTrace_2071956
  have hstable : (prefixWord ++ tailWord_2071956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071956).length < 2 ^ (prefixWord ++ tailWord_2071956).sum := by decide
  have hdescent : baseEnd_2071956 < baseStart_2071956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071976 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_2071976 : Nat := 118140960795 + 2071976 * 2 ^ 59
def prefixEnd_2071976 : Nat := 4983230072969 + 3 ^ 40 * 2071976 * 2
def baseEnd_2071976 : Nat := 472853152257906941364961

theorem tailTrace_2071976 : CollatzResearch.WordTrace tailWord_2071976 prefixEnd_2071976 472853152257906941364961 := by
  unfold tailWord_2071976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785586570796146086625891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50380782094394861448834521 37785586570796146086625891)
  ·
    refine ⟨56678379856194219129938837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37785586570796146086625891 56678379856194219129938837)
    ·
      refine ⟨2656799055759104021715883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56678379856194219129938837 2656799055759104021715883)
      ·
        refine ⟨3985198583638656032573825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656799055759104021715883 3985198583638656032573825)
        ·
          refine ⟨2988898937728992024430369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985198583638656032573825 2988898937728992024430369)
          ·
            refine ⟨2241674203296744018322777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2988898937728992024430369 2241674203296744018322777)
            ·
              refine ⟨1681255652472558013742083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241674203296744018322777 1681255652472558013742083)
              ·
                refine ⟨2521883478708837020613125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681255652472558013742083 2521883478708837020613125)
                ·
                  refine ⟨472853152257906941364961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521883478708837020613125 472853152257906941364961)
                  ·
                    rfl

theorem cell21_2071976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_2071976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2071976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2071976 prefixEnd_2071976 := by exact prefixLift 2071976
  have htrace : WordTrace (prefixWord ++ tailWord_2071976) baseStart_2071976 baseEnd_2071976 := by
    simpa [prefixWord, tailWord_2071976, baseEnd_2071976] using wordTrace_append hprefix tailTrace_2071976
  have hstable : (prefixWord ++ tailWord_2071976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071976).length < 2 ^ (prefixWord ++ tailWord_2071976).sum := by decide
  have hdescent : baseEnd_2071976 < baseStart_2071976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072046 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2072046 : Nat := 118140960795 + 2072046 * 2 ^ 59
def prefixEnd_2072046 : Nat := 4983230072969 + 3 ^ 40 * 2072046 * 2
def baseEnd_2072046 : Nat := 472869127211602375198151

theorem tailTrace_2072046 : CollatzResearch.WordTrace tailWord_2072046 prefixEnd_2072046 472869127211602375198151 := by
  unfold tailWord_2072046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446715781417336766037499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50382484167559129418866661 9446715781417336766037499)
  ·
    refine ⟨14170073672126005149056249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446715781417336766037499 14170073672126005149056249)
    ·
      refine ⟨10627555254094503861792187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14170073672126005149056249 10627555254094503861792187)
      ·
        refine ⟨15941332881141755792688281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627555254094503861792187 15941332881141755792688281)
        ·
          refine ⟨11955999660856316844516211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15941332881141755792688281 11955999660856316844516211)
          ·
            refine ⟨17933999491284475266774317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955999660856316844516211 17933999491284475266774317)
            ·
              refine ⟨6725249809231678225040369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17933999491284475266774317 6725249809231678225040369)
              ·
                refine ⟨5043937356923758668780277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725249809231678225040369 5043937356923758668780277)
                ·
                  refine ⟨472869127211602375198151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5043937356923758668780277 472869127211602375198151)
                  ·
                    rfl

theorem cell21_2072046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2072046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072046 prefixEnd_2072046 := by exact prefixLift 2072046
  have htrace : WordTrace (prefixWord ++ tailWord_2072046) baseStart_2072046 baseEnd_2072046 := by
    simpa [prefixWord, tailWord_2072046, baseEnd_2072046] using wordTrace_append hprefix tailTrace_2072046
  have hstable : (prefixWord ++ tailWord_2072046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072046).length < 2 ^ (prefixWord ++ tailWord_2072046).sum := by decide
  have hdescent : baseEnd_2072046 < baseStart_2072046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072246 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2072246 : Nat := 118140960795 + 2072246 * 2 ^ 59
def prefixEnd_2072246 : Nat := 4983230072969 + 3 ^ 40 * 2072246 * 2
def baseEnd_2072246 : Nat := 472914769936446471864409

theorem tailTrace_2072246 : CollatzResearch.WordTrace tailWord_2072246 prefixEnd_2072246 472914769936446471864409 := by
  unfold tailWord_2072246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723813803163383017848787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50387347233742752190387061 4723813803163383017848787)
  ·
    refine ⟨7085720704745074526773181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723813803163383017848787 7085720704745074526773181)
    ·
      refine ⟨2657145264279402947539943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7085720704745074526773181 2657145264279402947539943)
      ·
        refine ⟨3985717896419104421309915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657145264279402947539943 3985717896419104421309915)
        ·
          refine ⟨5978576844628656631964873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985717896419104421309915 5978576844628656631964873)
          ·
            refine ⟨4483932633471492473973655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978576844628656631964873 4483932633471492473973655)
            ·
              refine ⟨6725898950207238710960483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483932633471492473973655 6725898950207238710960483)
              ·
                refine ⟨10088848425310858066440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725898950207238710960483 10088848425310858066440725)
                ·
                  refine ⟨472914769936446471864409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10088848425310858066440725 472914769936446471864409)
                  ·
                    rfl

theorem cell21_2072246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2072246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072246 prefixEnd_2072246 := by exact prefixLift 2072246
  have htrace : WordTrace (prefixWord ++ tailWord_2072246) baseStart_2072246 baseEnd_2072246 := by
    simpa [prefixWord, tailWord_2072246, baseEnd_2072246] using wordTrace_append hprefix tailTrace_2072246
  have hstable : (prefixWord ++ tailWord_2072246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072246).length < 2 ^ (prefixWord ++ tailWord_2072246).sum := by decide
  have hdescent : baseEnd_2072246 < baseStart_2072246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072274 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2072274 : Nat := 118140960795 + 2072274 * 2 ^ 59
def prefixEnd_2072274 : Nat := 4983230072969 + 3 ^ 40 * 2072274 * 2
def baseEnd_2072274 : Nat := 472921159917924645397685

theorem tailTrace_2072274 : CollatzResearch.WordTrace tailWord_2072274 prefixEnd_2072274 472921159917924645397685 := by
  unfold tailWord_2072274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895510523628172266899969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50388028063008459378399917 18895510523628172266899969)
  ·
    refine ⟨14171632892721129200174977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18895510523628172266899969 14171632892721129200174977)
    ·
      refine ⟨10628724669540846900131233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14171632892721129200174977 10628724669540846900131233)
      ·
        refine ⟨7971543502155635175098425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10628724669540846900131233 7971543502155635175098425)
        ·
          refine ⟨5978657626616726381323819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7971543502155635175098425 5978657626616726381323819)
          ·
            refine ⟨8967986439925089571985729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978657626616726381323819 8967986439925089571985729)
            ·
              refine ⟨6725989829943817178989297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8967986439925089571985729 6725989829943817178989297)
              ·
                refine ⟨5044492372457862884241973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725989829943817178989297 5044492372457862884241973)
                ·
                  refine ⟨472921159917924645397685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044492372457862884241973 472921159917924645397685)
                  ·
                    rfl

theorem cell21_2072274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2072274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072274 prefixEnd_2072274 := by exact prefixLift 2072274
  have htrace : WordTrace (prefixWord ++ tailWord_2072274) baseStart_2072274 baseEnd_2072274 := by
    simpa [prefixWord, tailWord_2072274, baseEnd_2072274] using wordTrace_append hprefix tailTrace_2072274
  have hstable : (prefixWord ++ tailWord_2072274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072274).length < 2 ^ (prefixWord ++ tailWord_2072274).sum := by decide
  have hdescent : baseEnd_2072274 < baseStart_2072274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072308 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2072308 : Nat := 118140960795 + 2072308 * 2 ^ 59
def prefixEnd_2072308 : Nat := 4983230072969 + 3 ^ 40 * 2072308 * 2
def baseEnd_2072308 : Nat := 472928919181148141830949

theorem tailTrace_2072308 : CollatzResearch.WordTrace tailWord_2072308 prefixEnd_2072308 472928919181148141830949 := by
  unfold tailWord_2072308
  simp only [CollatzResearch.WordTrace]
  refine ⟨37791641088194756437168789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50388854784259675249558385 37791641088194756437168789)
  ·
    refine ⟨1771483176009129207992287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37791641088194756437168789 1771483176009129207992287)
    ·
      refine ⟨2657224764013693811988431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771483176009129207992287 2657224764013693811988431)
      ·
        refine ⟨3985837146020540717982647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657224764013693811988431 3985837146020540717982647)
        ·
          refine ⟨5978755719030811076973971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985837146020540717982647 5978755719030811076973971)
          ·
            refine ⟨8968133578546216615460957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978755719030811076973971 8968133578546216615460957)
            ·
              refine ⟨3363050091954831230797859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8968133578546216615460957 3363050091954831230797859)
              ·
                refine ⟨5044575137932246846196789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363050091954831230797859 5044575137932246846196789)
                ·
                  refine ⟨472928919181148141830949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044575137932246846196789 472928919181148141830949)
                  ·
                    rfl

theorem cell21_2072308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2072308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072308 prefixEnd_2072308 := by exact prefixLift 2072308
  have htrace : WordTrace (prefixWord ++ tailWord_2072308) baseStart_2072308 baseEnd_2072308 := by
    simpa [prefixWord, tailWord_2072308, baseEnd_2072308] using wordTrace_append hprefix tailTrace_2072308
  have hstable : (prefixWord ++ tailWord_2072308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072308).length < 2 ^ (prefixWord ++ tailWord_2072308).sum := by decide
  have hdescent : baseEnd_2072308 < baseStart_2072308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072364 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2072364 : Nat := 118140960795 + 2072364 * 2 ^ 59
def prefixEnd_2072364 : Nat := 4983230072969 + 3 ^ 40 * 2072364 * 2
def baseEnd_2072364 : Nat := 472941699144104488897501

theorem tailTrace_2072364 : CollatzResearch.WordTrace tailWord_2072364 prefixEnd_2072364 472941699144104488897501 := by
  unfold tailWord_2072364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792662332093317219188073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50390216442791089625584097 37792662332093317219188073)
  ·
    refine ⟨28344496749069987914391055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37792662332093317219188073 28344496749069987914391055)
    ·
      refine ⟨42516745123604981871586583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28344496749069987914391055 42516745123604981871586583)
      ·
        refine ⟨63775117685407472807379875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42516745123604981871586583 63775117685407472807379875)
        ·
          refine ⟨95662676528111209211069813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63775117685407472807379875 95662676528111209211069813)
          ·
            refine ⟨8968375924510425863537795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95662676528111209211069813 8968375924510425863537795)
            ·
              refine ⟨13452563886765638795306693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8968375924510425863537795 13452563886765638795306693)
              ·
                refine ⟨2522355728768557274120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13452563886765638795306693 2522355728768557274120005)
                ·
                  refine ⟨472941699144104488897501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522355728768557274120005 472941699144104488897501)
                  ·
                    rfl

theorem cell21_2072364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2072364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072364 prefixEnd_2072364 := by exact prefixLift 2072364
  have htrace : WordTrace (prefixWord ++ tailWord_2072364) baseStart_2072364 baseEnd_2072364 := by
    simpa [prefixWord, tailWord_2072364, baseEnd_2072364] using wordTrace_append hprefix tailTrace_2072364
  have hstable : (prefixWord ++ tailWord_2072364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072364).length < 2 ^ (prefixWord ++ tailWord_2072364).sum := by decide
  have hdescent : baseEnd_2072364 < baseStart_2072364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072381 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_2072381 : Nat := 118140960795 + 2072381 * 2 ^ 59
def prefixEnd_2072381 : Nat := 4983230072969 + 3 ^ 40 * 2072381 * 2
def baseEnd_2072381 : Nat := 472945578775716237114133

theorem tailTrace_2072381 : CollatzResearch.WordTrace tailWord_2072381 prefixEnd_2072381 472945578775716237114133 := by
  unfold tailWord_2072381
  simp only [CollatzResearch.WordTrace]
  refine ⟨75585944705125046341744997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50390629803416697561163331 75585944705125046341744997)
  ·
    refine ⟨14172364632210946189077187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75585944705125046341744997 14172364632210946189077187)
    ·
      refine ⟨21258546948316419283615781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14172364632210946189077187 21258546948316419283615781)
      ·
        refine ⟨3985977552809328615677959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21258546948316419283615781 3985977552809328615677959)
        ·
          refine ⟨5978966329213992923516939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985977552809328615677959 5978966329213992923516939)
          ·
            refine ⟨8968449493820989385275409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978966329213992923516939 8968449493820989385275409)
            ·
              refine ⟨6726337120365742038956557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8968449493820989385275409 6726337120365742038956557)
              ·
                refine ⟨2522376420137153264608709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726337120365742038956557 2522376420137153264608709)
                ·
                  refine ⟨472945578775716237114133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522376420137153264608709 472945578775716237114133)
                  ·
                    rfl

theorem cell21_2072381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_2072381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072381 prefixEnd_2072381 := by exact prefixLift 2072381
  have htrace : WordTrace (prefixWord ++ tailWord_2072381) baseStart_2072381 baseEnd_2072381 := by
    simpa [prefixWord, tailWord_2072381, baseEnd_2072381] using wordTrace_append hprefix tailTrace_2072381
  have hstable : (prefixWord ++ tailWord_2072381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072381).length < 2 ^ (prefixWord ++ tailWord_2072381).sum := by decide
  have hdescent : baseEnd_2072381 < baseStart_2072381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072530 : List Nat := [3, 2, 2, 3, 11]
def baseStart_2072530 : Nat := 118140960795 + 2072530 * 2 ^ 59
def prefixEnd_2072530 : Nat := 4983230072969 + 3 ^ 40 * 2072530 * 2
def baseEnd_2072530 : Nat := 5839254106243519618895

theorem tailTrace_2072530 : CollatzResearch.WordTrace tailWord_2072530 prefixEnd_2072530 5839254106243519618895 := by
  unfold tailWord_2072530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897844795396311197229761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50394252787723496525946029 18897844795396311197229761)
  ·
    refine ⟨14173383596547233397922321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18897844795396311197229761 14173383596547233397922321)
    ·
      refine ⟨10630037697410425048441741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14173383596547233397922321 10630037697410425048441741)
      ·
        refine ⟨3986264136528909393165653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10630037697410425048441741 3986264136528909393165653)
        ·
          refine ⟨5839254106243519618895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3986264136528909393165653 5839254106243519618895)
          ·
            rfl

theorem cell21_2072530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 11].length) (baseStart_2072530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072530 prefixEnd_2072530 := by exact prefixLift 2072530
  have htrace : WordTrace (prefixWord ++ tailWord_2072530) baseStart_2072530 baseEnd_2072530 := by
    simpa [prefixWord, tailWord_2072530, baseEnd_2072530] using wordTrace_append hprefix tailTrace_2072530
  have hstable : (prefixWord ++ tailWord_2072530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072530).length < 2 ^ (prefixWord ++ tailWord_2072530).sum := by decide
  have hdescent : baseEnd_2072530 < baseStart_2072530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072533 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_2072533 : Nat := 118140960795 + 2072533 * 2 ^ 59
def prefixEnd_2072533 : Nat := 4983230072969 + 3 ^ 40 * 2072533 * 2
def baseEnd_2072533 : Nat := 472980267246597750580489

theorem tailTrace_2072533 : CollatzResearch.WordTrace tailWord_2072533 prefixEnd_2072533 472980267246597750580489 := by
  unfold tailWord_2072533
  simp only [CollatzResearch.WordTrace]
  refine ⟨75591488600574376301278253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50394325733716250867518835 75591488600574376301278253)
  ·
    refine ⟨28346808225215391112979345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75591488600574376301278253 28346808225215391112979345)
    ·
      refine ⟨21260106168911543334734509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28346808225215391112979345 21260106168911543334734509)
      ·
        refine ⟨7972539813341828750525441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21260106168911543334734509 7972539813341828750525441)
        ·
          refine ⟨5979404860006371562894081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972539813341828750525441 5979404860006371562894081)
          ·
            refine ⟨4484553645004778672170561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5979404860006371562894081 4484553645004778672170561)
            ·
              refine ⟨3363415233753584004127921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484553645004778672170561 3363415233753584004127921)
              ·
                refine ⟨2522561425315188003095941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363415233753584004127921 2522561425315188003095941)
                ·
                  refine ⟨472980267246597750580489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522561425315188003095941 472980267246597750580489)
                  ·
                    rfl

theorem cell21_2072533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_2072533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072533 prefixEnd_2072533 := by exact prefixLift 2072533
  have htrace : WordTrace (prefixWord ++ tailWord_2072533) baseStart_2072533 baseEnd_2072533 := by
    simpa [prefixWord, tailWord_2072533, baseEnd_2072533] using wordTrace_append hprefix tailTrace_2072533
  have hstable : (prefixWord ++ tailWord_2072533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072533).length < 2 ^ (prefixWord ++ tailWord_2072533).sum := by decide
  have hdescent : baseEnd_2072533 < baseStart_2072533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072544 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_2072544 : Nat := 118140960795 + 2072544 * 2 ^ 59
def prefixEnd_2072544 : Nat := 4983230072969 + 3 ^ 40 * 2072544 * 2
def baseEnd_2072544 : Nat := 472982777596464175897133

theorem tailTrace_2072544 : CollatzResearch.WordTrace tailWord_2072544 prefixEnd_2072544 472982777596464175897133 := by
  unfold tailWord_2072544
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795944901767262589964343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50394593202356350119952457 37795944901767262589964343)
  ·
    refine ⟨56693917352650893884946515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37795944901767262589964343 56693917352650893884946515)
    ·
      refine ⟨85040876028976340827419773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56693917352650893884946515 85040876028976340827419773)
      ·
        refine ⟨31890328510866127810282415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85040876028976340827419773 31890328510866127810282415)
        ·
          refine ⟨47835492766299191715423623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31890328510866127810282415 47835492766299191715423623)
          ·
            refine ⟨71753239149448787573135435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47835492766299191715423623 71753239149448787573135435)
            ·
              refine ⟨107629858724173181359703153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71753239149448787573135435 107629858724173181359703153)
              ·
                refine ⟨80722394043129886019777365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107629858724173181359703153 80722394043129886019777365)
                ·
                  refine ⟨472982777596464175897133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80722394043129886019777365 472982777596464175897133)
                  ·
                    rfl

theorem cell21_2072544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_2072544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072544 prefixEnd_2072544 := by exact prefixLift 2072544
  have htrace : WordTrace (prefixWord ++ tailWord_2072544) baseStart_2072544 baseEnd_2072544 := by
    simpa [prefixWord, tailWord_2072544, baseEnd_2072544] using wordTrace_append hprefix tailTrace_2072544
  have hstable : (prefixWord ++ tailWord_2072544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072544).length < 2 ^ (prefixWord ++ tailWord_2072544).sum := by decide
  have hdescent : baseEnd_2072544 < baseStart_2072544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072547 : List Nat := [1, 1, 1, 6, 1, 4, 1, 6]
def baseStart_2072547 : Nat := 118140960795 + 2072547 * 2 ^ 59
def prefixEnd_2072547 : Nat := 4983230072969 + 3 ^ 40 * 2072547 * 2
def baseEnd_2072547 : Nat := 157661154079112279115709

theorem tailTrace_2072547 : CollatzResearch.WordTrace tailWord_2072547 prefixEnd_2072547 157661154079112279115709 := by
  unfold tailWord_2072547
  simp only [CollatzResearch.WordTrace]
  refine ⟨75591999222523656692287895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50394666148349104461525263 75591999222523656692287895)
  ·
    refine ⟨113387998833785485038431843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75591999222523656692287895 113387998833785485038431843)
    ·
      refine ⟨170081998250678227557647765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113387998833785485038431843 170081998250678227557647765)
      ·
        refine ⟨7972593668000541916764739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170081998250678227557647765 7972593668000541916764739)
        ·
          refine ⟨11958890502000812875147109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972593668000541916764739 11958890502000812875147109)
          ·
            refine ⟨2242291969125152414090083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11958890502000812875147109 2242291969125152414090083)
            ·
              refine ⟨3363437953687728621135125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242291969125152414090083 3363437953687728621135125)
              ·
                refine ⟨157661154079112279115709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3363437953687728621135125 157661154079112279115709)
                ·
                  rfl

theorem cell21_2072547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_2072547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072547 prefixEnd_2072547 := by exact prefixLift 2072547
  have htrace : WordTrace (prefixWord ++ tailWord_2072547) baseStart_2072547 baseEnd_2072547 := by
    simpa [prefixWord, tailWord_2072547, baseEnd_2072547] using wordTrace_append hprefix tailTrace_2072547
  have hstable : (prefixWord ++ tailWord_2072547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072547).length < 2 ^ (prefixWord ++ tailWord_2072547).sum := by decide
  have hdescent : baseEnd_2072547 < baseStart_2072547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072620 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_2072620 : Nat := 118140960795 + 2072620 * 2 ^ 59
def prefixEnd_2072620 : Nat := 4983230072969 + 3 ^ 40 * 2072620 * 2
def baseEnd_2072620 : Nat := 473000121831904932630311

theorem tailTrace_2072620 : CollatzResearch.WordTrace tailWord_2072620 prefixEnd_2072620 473000121831904932630311 := by
  unfold tailWord_2072620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37797330875629595079847657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50396441167506126773130209 37797330875629595079847657)
  ·
    refine ⟨28347998156722196309885743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37797330875629595079847657 28347998156722196309885743)
    ·
      refine ⟨42521997235083294464828615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28347998156722196309885743 42521997235083294464828615)
      ·
        refine ⟨63782995852624941697242923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42521997235083294464828615 63782995852624941697242923)
        ·
          refine ⟨95674493778937412545864385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63782995852624941697242923 95674493778937412545864385)
          ·
            refine ⟨71755870334203059409398289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95674493778937412545864385 71755870334203059409398289)
            ·
              refine ⟨53816902750652294557048717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71755870334203059409398289 53816902750652294557048717)
              ·
                refine ⟨20181338531494610458893269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53816902750652294557048717 20181338531494610458893269)
                ·
                  refine ⟨473000121831904932630311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20181338531494610458893269 473000121831904932630311)
                  ·
                    rfl

theorem cell21_2072620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_2072620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072620 prefixEnd_2072620 := by exact prefixLift 2072620
  have htrace : WordTrace (prefixWord ++ tailWord_2072620) baseStart_2072620 baseEnd_2072620 := by
    simpa [prefixWord, tailWord_2072620, baseEnd_2072620] using wordTrace_append hprefix tailTrace_2072620
  have hstable : (prefixWord ++ tailWord_2072620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072620).length < 2 ^ (prefixWord ++ tailWord_2072620).sum := by decide
  have hdescent : baseEnd_2072620 < baseStart_2072620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072654 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2072654 : Nat := 118140960795 + 2072654 * 2 ^ 59
def prefixEnd_2072654 : Nat := 4983230072969 + 3 ^ 40 * 2072654 * 2
def baseEnd_2072654 : Nat := 473007881095128429063575

theorem tailTrace_2072654 : CollatzResearch.WordTrace tailWord_2072654 prefixEnd_2072654 473007881095128429063575 := by
  unfold tailWord_2072654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449487729142001745804127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50397267888757342644288677 9449487729142001745804127)
  ·
    refine ⟨14174231593713002618706191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9449487729142001745804127 14174231593713002618706191)
    ·
      refine ⟨21261347390569503928059287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14174231593713002618706191 21261347390569503928059287)
      ·
        refine ⟨31892021085854255892088931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21261347390569503928059287 31892021085854255892088931)
        ·
          refine ⟨47838031628781383838133397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31892021085854255892088931 47838031628781383838133397)
          ·
            refine ⟨2242407732599127367412503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47838031628781383838133397 2242407732599127367412503)
            ·
              refine ⟨3363611598898691051118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242407732599127367412503 3363611598898691051118755)
              ·
                refine ⟨5045417398348036576678133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363611598898691051118755 5045417398348036576678133)
                ·
                  refine ⟨473007881095128429063575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045417398348036576678133 473007881095128429063575)
                  ·
                    rfl

theorem cell21_2072654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2072654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072654 prefixEnd_2072654 := by exact prefixLift 2072654
  have htrace : WordTrace (prefixWord ++ tailWord_2072654) baseStart_2072654 baseEnd_2072654 := by
    simpa [prefixWord, tailWord_2072654, baseEnd_2072654] using wordTrace_append hprefix tailTrace_2072654
  have hstable : (prefixWord ++ tailWord_2072654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072654).length < 2 ^ (prefixWord ++ tailWord_2072654).sum := by decide
  have hdescent : baseEnd_2072654 < baseStart_2072654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072705 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 3]
def baseStart_2072705 : Nat := 118140960795 + 2072705 * 2 ^ 59
def prefixEnd_2072705 : Nat := 4983230072969 + 3 ^ 40 * 2072705 * 2
def baseEnd_2072705 : Nat := 473019519989963673713471

theorem tailTrace_2072705 : CollatzResearch.WordTrace tailWord_2072705 prefixEnd_2072705 473019519989963673713471 := by
  unfold tailWord_2072705
  simp only [CollatzResearch.WordTrace]
  refine ⟨75597761955951249676539569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50398507970634166451026379 75597761955951249676539569)
  ·
    refine ⟨56698321466963437257404677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75597761955951249676539569 56698321466963437257404677)
    ·
      refine ⟨10630935275055644485763377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56698321466963437257404677 10630935275055644485763377)
      ·
        refine ⟨7973201456291733364322533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10630935275055644485763377 7973201456291733364322533)
        ·
          refine ⟨1494975273054700005810475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7973201456291733364322533 1494975273054700005810475)
          ·
            refine ⟨2242462909582050008715713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494975273054700005810475 2242462909582050008715713)
            ·
              refine ⟨1681847182186537506536785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242462909582050008715713 1681847182186537506536785)
              ·
                refine ⟨1261385386639903129902589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681847182186537506536785 1261385386639903129902589)
                ·
                  refine ⟨473019519989963673713471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261385386639903129902589 473019519989963673713471)
                  ·
                    rfl

theorem cell21_2072705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_2072705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072705 prefixEnd_2072705 := by exact prefixLift 2072705
  have htrace : WordTrace (prefixWord ++ tailWord_2072705) baseStart_2072705 baseEnd_2072705 := by
    simpa [prefixWord, tailWord_2072705, baseEnd_2072705] using wordTrace_append hprefix tailTrace_2072705
  have hstable : (prefixWord ++ tailWord_2072705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072705).length < 2 ^ (prefixWord ++ tailWord_2072705).sum := by decide
  have hdescent : baseEnd_2072705 < baseStart_2072705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072730 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2072730 : Nat := 118140960795 + 2072730 * 2 ^ 59
def prefixEnd_2072730 : Nat := 4983230072969 + 3 ^ 40 * 2072730 * 2
def baseEnd_2072730 : Nat := 473025225330569185796753

theorem tailTrace_2072730 : CollatzResearch.WordTrace tailWord_2072730 prefixEnd_2072730 473025225330569185796753 := by
  unfold tailWord_2072730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18899668445215169736549911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50399115853907119297466429 18899668445215169736549911)
  ·
    refine ⟨28349502667822754604824867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18899668445215169736549911 28349502667822754604824867)
    ·
      refine ⟨42524254001734131907237301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28349502667822754604824867 42524254001734131907237301)
      ·
        refine ⟨3986648812662574866303497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42524254001734131907237301 3986648812662574866303497)
        ·
          refine ⟨2989986609496931149727623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986648812662574866303497 2989986609496931149727623)
          ·
            refine ⟨4484979914245396724591435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989986609496931149727623 4484979914245396724591435)
            ·
              refine ⟨6727469871368095086887153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484979914245396724591435 6727469871368095086887153)
              ·
                refine ⟨5045602403526071315165365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727469871368095086887153 5045602403526071315165365)
                ·
                  refine ⟨473025225330569185796753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045602403526071315165365 473025225330569185796753)
                  ·
                    rfl

theorem cell21_2072730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2072730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072730 prefixEnd_2072730 := by exact prefixLift 2072730
  have htrace : WordTrace (prefixWord ++ tailWord_2072730) baseStart_2072730 baseEnd_2072730 := by
    simpa [prefixWord, tailWord_2072730, baseEnd_2072730] using wordTrace_append hprefix tailTrace_2072730
  have hstable : (prefixWord ++ tailWord_2072730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072730).length < 2 ^ (prefixWord ++ tailWord_2072730).sum := by decide
  have hdescent : baseEnd_2072730 < baseStart_2072730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072817 : List Nat := [1, 2, 2, 2, 2, 1, 11]
def baseStart_2072817 : Nat := 118140960795 + 2072817 * 2 ^ 59
def prefixEnd_2072817 : Nat := 4983230072969 + 3 ^ 40 * 2072817 * 2
def baseEnd_2072817 : Nat := 52560564435097374205175

theorem tailTrace_2072817 : CollatzResearch.WordTrace tailWord_2072817 prefixEnd_2072817 52560564435097374205175 := by
  unfold tailWord_2072817
  simp only [CollatzResearch.WordTrace]
  refine ⟨75601846931545492804616705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50401231287696995203077803 75601846931545492804616705)
  ·
    refine ⟨56701385198659119603462529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75601846931545492804616705 56701385198659119603462529)
    ·
      refine ⟨42526038898994339702596897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56701385198659119603462529 42526038898994339702596897)
      ·
        refine ⟨31894529174245754776947673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42526038898994339702596897 31894529174245754776947673)
        ·
          refine ⟨23920896880684316082710755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31894529174245754776947673 23920896880684316082710755)
          ·
            refine ⟨35881345321026474124066133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23920896880684316082710755 35881345321026474124066133)
            ·
              refine ⟨52560564435097374205175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35881345321026474124066133 52560564435097374205175)
              ·
                rfl

theorem cell21_2072817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 11].length) (baseStart_2072817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072817 prefixEnd_2072817 := by exact prefixLift 2072817
  have htrace : WordTrace (prefixWord ++ tailWord_2072817) baseStart_2072817 baseEnd_2072817 := by
    simpa [prefixWord, tailWord_2072817, baseEnd_2072817] using wordTrace_append hprefix tailTrace_2072817
  have hstable : (prefixWord ++ tailWord_2072817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072817).length < 2 ^ (prefixWord ++ tailWord_2072817).sum := by decide
  have hdescent : baseEnd_2072817 < baseStart_2072817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072871 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 4]
def baseStart_2072871 : Nat := 118140960795 + 2072871 * 2 ^ 59
def prefixEnd_2072871 : Nat := 4983230072969 + 3 ^ 40 * 2072871 * 2
def baseEnd_2072871 : Nat := 473057403451584273946465

theorem tailTrace_2072871 : CollatzResearch.WordTrace tailWord_2072871 prefixEnd_2072871 473057403451584273946465 := by
  unfold tailWord_2072871
  simp only [CollatzResearch.WordTrace]
  refine ⟨75603816473349860027082467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50402544315566573351388311 75603816473349860027082467)
  ·
    refine ⟨113405724710024790040623701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75603816473349860027082467 113405724710024790040623701)
    ·
      refine ⟨1328973336445603008288559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 113405724710024790040623701 1328973336445603008288559)
      ·
        refine ⟨1993460004668404512432839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328973336445603008288559 1993460004668404512432839)
        ·
          refine ⟨2990190007002606768649259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993460004668404512432839 2990190007002606768649259)
          ·
            refine ⟨4485285010503910152973889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990190007002606768649259 4485285010503910152973889)
            ·
              refine ⟨3363963757877932614730417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485285010503910152973889 3363963757877932614730417)
              ·
                refine ⟨2522972818408449461047813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363963757877932614730417 2522972818408449461047813)
                ·
                  refine ⟨473057403451584273946465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522972818408449461047813 473057403451584273946465)
                  ·
                    rfl

theorem cell21_2072871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].length) (baseStart_2072871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072871 prefixEnd_2072871 := by exact prefixLift 2072871
  have htrace : WordTrace (prefixWord ++ tailWord_2072871) baseStart_2072871 baseEnd_2072871 := by
    simpa [prefixWord, tailWord_2072871, baseEnd_2072871] using wordTrace_append hprefix tailTrace_2072871
  have hstable : (prefixWord ++ tailWord_2072871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072871).length < 2 ^ (prefixWord ++ tailWord_2072871).sum := by decide
  have hdescent : baseEnd_2072871 < baseStart_2072871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072879 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_2072879 : Nat := 118140960795 + 2072879 * 2 ^ 59
def prefixEnd_2072879 : Nat := 4983230072969 + 3 ^ 40 * 2072879 * 2
def baseEnd_2072879 : Nat := 473059229160578037813115

theorem tailTrace_2072879 : CollatzResearch.WordTrace tailWord_2072879 prefixEnd_2072879 473059229160578037813115 := by
  unfold tailWord_2072879
  simp only [CollatzResearch.WordTrace]
  refine ⟨75604108257320877393373691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50402738838213918262249127 75604108257320877393373691)
  ·
    refine ⟨113406162385981316090060537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75604108257320877393373691 113406162385981316090060537)
    ·
      refine ⟨85054621789485987067545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113406162385981316090060537 85054621789485987067545403)
      ·
        refine ⟨127581932684228980601318105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85054621789485987067545403 127581932684228980601318105)
        ·
          refine ⟨95686449513171735450988579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127581932684228980601318105 95686449513171735450988579)
          ·
            refine ⟨143529674269757603176482869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95686449513171735450988579 143529674269757603176482869)
            ·
              refine ⟨13455906962789775297795269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143529674269757603176482869 13455906962789775297795269)
              ·
                refine ⟨2522982555523082868336613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13455906962789775297795269 2522982555523082868336613)
                ·
                  refine ⟨473059229160578037813115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522982555523082868336613 473059229160578037813115)
                  ·
                    rfl

theorem cell21_2072879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_2072879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072879 prefixEnd_2072879 := by exact prefixLift 2072879
  have htrace : WordTrace (prefixWord ++ tailWord_2072879) baseStart_2072879 baseEnd_2072879 := by
    simpa [prefixWord, tailWord_2072879, baseEnd_2072879] using wordTrace_append hprefix tailTrace_2072879
  have hstable : (prefixWord ++ tailWord_2072879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072879).length < 2 ^ (prefixWord ++ tailWord_2072879).sum := by decide
  have hdescent : baseEnd_2072879 < baseStart_2072879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072941 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2072941 : Nat := 118140960795 + 2072941 * 2 ^ 59
def prefixEnd_2072941 : Nat := 4983230072969 + 3 ^ 40 * 2072941 * 2
def baseEnd_2072941 : Nat := 473073378405279707779655

theorem tailTrace_2072941 : CollatzResearch.WordTrace tailWord_2072941 prefixEnd_2072941 473073378405279707779655 := by
  unfold tailWord_2072941
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606369583096261982130677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50404246388730841321420451 75606369583096261982130677)
  ·
    refine ⟨7088097148415274560824751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75606369583096261982130677 7088097148415274560824751)
    ·
      refine ⟨10632145722622911841237127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088097148415274560824751 10632145722622911841237127)
      ·
        refine ⟨15948218583934367761855691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632145722622911841237127 15948218583934367761855691)
        ·
          refine ⟨23922327875901551642783537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948218583934367761855691 23922327875901551642783537)
          ·
            refine ⟨17941745906926163732087653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23922327875901551642783537 17941745906926163732087653)
            ·
              refine ⟨3364077357548655699766435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17941745906926163732087653 3364077357548655699766435)
              ·
                refine ⟨5046116036322983549649653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364077357548655699766435 5046116036322983549649653)
                ·
                  refine ⟨473073378405279707779655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046116036322983549649653 473073378405279707779655)
                  ·
                    rfl

theorem cell21_2072941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2072941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072941 prefixEnd_2072941 := by exact prefixLift 2072941
  have htrace : WordTrace (prefixWord ++ tailWord_2072941) baseStart_2072941 baseEnd_2072941 := by
    simpa [prefixWord, tailWord_2072941, baseEnd_2072941] using wordTrace_append hprefix tailTrace_2072941
  have hstable : (prefixWord ++ tailWord_2072941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072941).length < 2 ^ (prefixWord ++ tailWord_2072941).sum := by decide
  have hdescent : baseEnd_2072941 < baseStart_2072941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072986 : List Nat := [3, 1, 1, 4, 1, 4, 7]
def baseStart_2072986 : Nat := 118140960795 + 2072986 * 2 ^ 59
def prefixEnd_2072986 : Nat := 4983230072969 + 3 ^ 40 * 2072986 * 2
def baseEnd_2072986 : Nat := 52564849779818847725507

theorem tailTrace_2072986 : CollatzResearch.WordTrace tailWord_2072986 prefixEnd_2072986 52564849779818847725507 := by
  unfold tailWord_2072986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902002716983308666879703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50405340578622156445012541 18902002716983308666879703)
  ·
    refine ⟨28353004075474963000319555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18902002716983308666879703 28353004075474963000319555)
    ·
      refine ⟨42529506113212444500479333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28353004075474963000319555 42529506113212444500479333)
      ·
        refine ⟨7974282396227333343839875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42529506113212444500479333 7974282396227333343839875)
        ·
          refine ⟨11961423594341000015759813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974282396227333343839875 11961423594341000015759813)
          ·
            refine ⟨2242766923938937502954965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11961423594341000015759813 2242766923938937502954965)
            ·
              refine ⟨52564849779818847725507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2242766923938937502954965 52564849779818847725507)
              ·
                rfl

theorem cell21_2072986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 7].length) (baseStart_2072986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2072986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2072986 prefixEnd_2072986 := by exact prefixLift 2072986
  have htrace : WordTrace (prefixWord ++ tailWord_2072986) baseStart_2072986 baseEnd_2072986 := by
    simpa [prefixWord, tailWord_2072986, baseEnd_2072986] using wordTrace_append hprefix tailTrace_2072986
  have hstable : (prefixWord ++ tailWord_2072986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072986).length < 2 ^ (prefixWord ++ tailWord_2072986).sum := by decide
  have hdescent : baseEnd_2072986 < baseStart_2072986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073045 : List Nat := [1, 3, 2, 3, 1, 11]
def baseStart_2073045 : Nat := 118140960795 + 2073045 * 2 ^ 59
def prefixEnd_2073045 : Nat := 4983230072969 + 3 ^ 40 * 2073045 * 2
def baseEnd_2073045 : Nat := 17522115282303653260967

theorem tailTrace_2073045 : CollatzResearch.WordTrace tailWord_2073045 prefixEnd_2073045 17522115282303653260967 := by
  unfold tailWord_2073045
  simp only [CollatzResearch.WordTrace]
  refine ⟨75610162774719487743916589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50406775183146325162611059 75610162774719487743916589)
  ·
    refine ⟨28353811040519807903968721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75610162774719487743916589 28353811040519807903968721)
    ·
      refine ⟨21265358280389855927976541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28353811040519807903968721 21265358280389855927976541)
      ·
        refine ⟨7974509355146195972991203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21265358280389855927976541 7974509355146195972991203)
        ·
          refine ⟨11961764032719293959486805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974509355146195972991203 11961764032719293959486805)
          ·
            refine ⟨17522115282303653260967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11961764032719293959486805 17522115282303653260967)
            ·
              rfl

theorem cell21_2073045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 11].length) (baseStart_2073045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073045 prefixEnd_2073045 := by exact prefixLift 2073045
  have htrace : WordTrace (prefixWord ++ tailWord_2073045) baseStart_2073045 baseEnd_2073045 := by
    simpa [prefixWord, tailWord_2073045, baseEnd_2073045] using wordTrace_append hprefix tailTrace_2073045
  have hstable : (prefixWord ++ tailWord_2073045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073045).length < 2 ^ (prefixWord ++ tailWord_2073045).sum := by decide
  have hdescent : baseEnd_2073045 < baseStart_2073045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073093 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2073093 : Nat := 118140960795 + 2073093 * 2 ^ 59
def prefixEnd_2073093 : Nat := 4983230072969 + 3 ^ 40 * 2073093 * 2
def baseEnd_2073093 : Nat := 473108066876161221246011

theorem tailTrace_2073093 : CollatzResearch.WordTrace tailWord_2073093 prefixEnd_2073093 473108066876161221246011 := by
  unfold tailWord_2073093
  simp only [CollatzResearch.WordTrace]
  refine ⟨75611913478545591941663933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50407942319030394627775955 75611913478545591941663933)
  ·
    refine ⟨28354467554454596978123975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75611913478545591941663933 28354467554454596978123975)
    ·
      refine ⟨42531701331681895467185963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354467554454596978123975 42531701331681895467185963)
      ·
        refine ⟨63797551997522843200778945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42531701331681895467185963 63797551997522843200778945)
        ·
          refine ⟨47848163998142132400584209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63797551997522843200778945 47848163998142132400584209)
          ·
            refine ⟨35886122998606599300438157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47848163998142132400584209 35886122998606599300438157)
            ·
              refine ⟨13457296124477474737664309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35886122998606599300438157 13457296124477474737664309)
              ·
                refine ⟨1261621511669763256656029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13457296124477474737664309 1261621511669763256656029)
                ·
                  refine ⟨473108066876161221246011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261621511669763256656029 473108066876161221246011)
                  ·
                    rfl

theorem cell21_2073093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2073093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073093 prefixEnd_2073093 := by exact prefixLift 2073093
  have htrace : WordTrace (prefixWord ++ tailWord_2073093) baseStart_2073093 baseEnd_2073093 := by
    simpa [prefixWord, tailWord_2073093, baseEnd_2073093] using wordTrace_append hprefix tailTrace_2073093
  have hstable : (prefixWord ++ tailWord_2073093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073093).length < 2 ^ (prefixWord ++ tailWord_2073093).sum := by decide
  have hdescent : baseEnd_2073093 < baseStart_2073093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073121 : List Nat := [1, 2, 3, 2, 2, 1, 2, 8]
def baseStart_2073121 : Nat := 118140960795 + 2073121 * 2 ^ 59
def prefixEnd_2073121 : Nat := 4983230072969 + 3 ^ 40 * 2073121 * 2
def baseEnd_2073121 : Nat := 157704818952546464926429

theorem tailTrace_2073121 : CollatzResearch.WordTrace tailWord_2073121 prefixEnd_2073121 157704818952546464926429 := by
  unfold tailWord_2073121
  simp only [CollatzResearch.WordTrace]
  refine ⟨75612934722444152723683217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50408623148296101815788811 75612934722444152723683217)
  ·
    refine ⟨56709701041833114542762413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75612934722444152723683217 56709701041833114542762413)
    ·
      refine ⟨21266137890687417953535905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56709701041833114542762413 21266137890687417953535905)
      ·
        refine ⟨15949603418015563465151929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21266137890687417953535905 15949603418015563465151929)
        ·
          refine ⟨11962202563511672598863947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949603418015563465151929 11962202563511672598863947)
          ·
            refine ⟨17943303845267508898295921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962202563511672598863947 17943303845267508898295921)
            ·
              refine ⟨13457477883950631673721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17943303845267508898295921 13457477883950631673721941)
              ·
                refine ⟨157704818952546464926429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13457477883950631673721941 157704818952546464926429)
                ·
                  rfl

theorem cell21_2073121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_2073121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073121 prefixEnd_2073121 := by exact prefixLift 2073121
  have htrace : WordTrace (prefixWord ++ tailWord_2073121) baseStart_2073121 baseEnd_2073121 := by
    simpa [prefixWord, tailWord_2073121, baseEnd_2073121] using wordTrace_append hprefix tailTrace_2073121
  have hstable : (prefixWord ++ tailWord_2073121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073121).length < 2 ^ (prefixWord ++ tailWord_2073121).sum := by decide
  have hdescent : baseEnd_2073121 < baseStart_2073121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073138 : List Nat := [3, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2073138 : Nat := 118140960795 + 2073138 * 2 ^ 59
def prefixEnd_2073138 : Nat := 4983230072969 + 3 ^ 40 * 2073138 * 2
def baseEnd_2073138 : Nat := 157706112163083714331973

theorem tailTrace_2073138 : CollatzResearch.WordTrace tailWord_2073138 prefixEnd_2073138 157706112163083714331973 := by
  unfold tailWord_2073138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903388690845641156763017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50409036508921709751368045 18903388690845641156763017)
  ·
    refine ⟨14177541518134230867572263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18903388690845641156763017 14177541518134230867572263)
    ·
      refine ⟨21266312277201346301358395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177541518134230867572263 21266312277201346301358395)
      ·
        refine ⟨31899468415802019452037593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21266312277201346301358395 31899468415802019452037593)
        ·
          refine ⟨23924601311851514589028195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31899468415802019452037593 23924601311851514589028195)
          ·
            refine ⟨35886901967777271883542293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23924601311851514589028195 35886901967777271883542293)
            ·
              refine ⟨1682198529739559619541045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35886901967777271883542293 1682198529739559619541045)
              ·
                refine ⟨157706112163083714331973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1682198529739559619541045 157706112163083714331973)
                ·
                  rfl

theorem cell21_2073138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2073138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073138 prefixEnd_2073138 := by exact prefixLift 2073138
  have htrace : WordTrace (prefixWord ++ tailWord_2073138) baseStart_2073138 baseEnd_2073138 := by
    simpa [prefixWord, tailWord_2073138, baseEnd_2073138] using wordTrace_append hprefix tailTrace_2073138
  have hstable : (prefixWord ++ tailWord_2073138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073138).length < 2 ^ (prefixWord ++ tailWord_2073138).sum := by decide
  have hdescent : baseEnd_2073138 < baseStart_2073138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073169 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_2073169 : Nat := 118140960795 + 2073169 * 2 ^ 59
def prefixEnd_2073169 : Nat := 4983230072969 + 3 ^ 40 * 2073169 * 2
def baseEnd_2073169 : Nat := 473125411111601977979189

theorem tailTrace_2073169 : CollatzResearch.WordTrace tailWord_2073169 prefixEnd_2073169 473125411111601977979189 := by
  unfold tailWord_2073169
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614685426270256921430561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50409790284180171280953707 75614685426270256921430561)
  ·
    refine ⟨56711014069702692691072921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75614685426270256921430561 56711014069702692691072921)
    ·
      refine ⟨42533260552277019518304691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56711014069702692691072921 42533260552277019518304691)
      ·
        refine ⟨63799890828415529277457037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42533260552277019518304691 63799890828415529277457037)
        ·
          refine ⟨23924959060655823479046389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63799890828415529277457037 23924959060655823479046389)
          ·
            refine ⟨2242964911936483451160599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23924959060655823479046389 2242964911936483451160599)
            ·
              refine ⟨3364447367904725176740899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242964911936483451160599 3364447367904725176740899)
              ·
                refine ⟨5046671051857087765111349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364447367904725176740899 5046671051857087765111349)
                ·
                  refine ⟨473125411111601977979189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046671051857087765111349 473125411111601977979189)
                  ·
                    rfl

theorem cell21_2073169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_2073169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073169 prefixEnd_2073169 := by exact prefixLift 2073169
  have htrace : WordTrace (prefixWord ++ tailWord_2073169) baseStart_2073169 baseEnd_2073169 := by
    simpa [prefixWord, tailWord_2073169, baseEnd_2073169] using wordTrace_append hprefix tailTrace_2073169
  have hstable : (prefixWord ++ tailWord_2073169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073169).length < 2 ^ (prefixWord ++ tailWord_2073169).sum := by decide
  have hdescent : baseEnd_2073169 < baseStart_2073169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073211 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_2073211 : Nat := 118140960795 + 2073211 * 2 ^ 59
def prefixEnd_2073211 : Nat := 4983230072969 + 3 ^ 40 * 2073211 * 2
def baseEnd_2073211 : Nat := 473134996083819238279103

theorem tailTrace_2073211 : CollatzResearch.WordTrace tailWord_2073211 prefixEnd_2073211 473134996083819238279103 := by
  unfold tailWord_2073211
  simp only [CollatzResearch.WordTrace]
  refine ⟨75616217292118098094459487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50410811528078732062972991 75616217292118098094459487)
  ·
    refine ⟨113424325938177147141689231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75616217292118098094459487 113424325938177147141689231)
    ·
      refine ⟨170136488907265720712533847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113424325938177147141689231 170136488907265720712533847)
      ·
        refine ⟨255204733360898581068800771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170136488907265720712533847 255204733360898581068800771)
        ·
          refine ⟨382807100041347871603201157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255204733360898581068800771 382807100041347871603201157)
          ·
            refine ⟨71776331257752725925600217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382807100041347871603201157 71776331257752725925600217)
            ·
              refine ⟨53832248443314544444200163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71776331257752725925600217 53832248443314544444200163)
              ·
                refine ⟨80748372664971816666300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53832248443314544444200163 80748372664971816666300245)
                ·
                  refine ⟨473134996083819238279103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80748372664971816666300245 473134996083819238279103)
                  ·
                    rfl

theorem cell21_2073211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_2073211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073211 prefixEnd_2073211 := by exact prefixLift 2073211
  have htrace : WordTrace (prefixWord ++ tailWord_2073211) baseStart_2073211 baseEnd_2073211 := by
    simpa [prefixWord, tailWord_2073211, baseEnd_2073211] using wordTrace_append hprefix tailTrace_2073211
  have hstable : (prefixWord ++ tailWord_2073211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073211).length < 2 ^ (prefixWord ++ tailWord_2073211).sum := by decide
  have hdescent : baseEnd_2073211 < baseStart_2073211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073304 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_2073304 : Nat := 118140960795 + 2073304 * 2 ^ 59
def prefixEnd_2073304 : Nat := 4983230072969 + 3 ^ 40 * 2073304 * 2
def baseEnd_2073304 : Nat := 473156219950871743228913

theorem tailTrace_2073304 : CollatzResearch.WordTrace tailWord_2073304 prefixEnd_2073304 473156219950871743228913 := by
  unfold tailWord_2073304
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809804640390587488797483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50413072853854116651729977 37809804640390587488797483)
  ·
    refine ⟨56714706960585881233196225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37809804640390587488797483 56714706960585881233196225)
    ·
      refine ⟨42536030220439410924897169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56714706960585881233196225 42536030220439410924897169)
      ·
        refine ⟨31902022665329558193672877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42536030220439410924897169 31902022665329558193672877)
        ·
          refine ⟨11963258499498584322627329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31902022665329558193672877 11963258499498584322627329)
          ·
            refine ⟨8972443874623938241970497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963258499498584322627329 8972443874623938241970497)
            ·
              refine ⟨6729332905967953681477873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972443874623938241970497 6729332905967953681477873)
              ·
                refine ⟨5046999679475965261108405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729332905967953681477873 5046999679475965261108405)
                ·
                  refine ⟨473156219950871743228913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046999679475965261108405 473156219950871743228913)
                  ·
                    rfl

theorem cell21_2073304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_2073304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073304 prefixEnd_2073304 := by exact prefixLift 2073304
  have htrace : WordTrace (prefixWord ++ tailWord_2073304) baseStart_2073304 baseEnd_2073304 := by
    simpa [prefixWord, tailWord_2073304, baseEnd_2073304] using wordTrace_append hprefix tailTrace_2073304
  have hstable : (prefixWord ++ tailWord_2073304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073304).length < 2 ^ (prefixWord ++ tailWord_2073304).sum := by decide
  have hdescent : baseEnd_2073304 < baseStart_2073304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073321 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 3]
def baseStart_2073321 : Nat := 118140960795 + 2073321 * 2 ^ 59
def prefixEnd_2073321 : Nat := 4983230072969 + 3 ^ 40 * 2073321 * 2
def baseEnd_2073321 : Nat := 473160099582483491445545

theorem tailTrace_2073321 : CollatzResearch.WordTrace tailWord_2073321 prefixEnd_2073321 473160099582483491445545 := by
  unfold tailWord_2073321
  simp only [CollatzResearch.WordTrace]
  refine ⟨75620229321719586880963817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50413486214479724587309211 75620229321719586880963817)
  ·
    refine ⟨56715171991289690160722863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75620229321719586880963817 56715171991289690160722863)
    ·
      refine ⟨85072757986934535241084295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56715171991289690160722863 85072757986934535241084295)
      ·
        refine ⟨127609136980401802861626443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85072757986934535241084295 127609136980401802861626443)
        ·
          refine ⟨191413705470602704292439665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127609136980401802861626443 191413705470602704292439665)
          ·
            refine ⟨143560279102952028219329749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191413705470602704292439665 143560279102952028219329749)
            ·
              refine ⟨3364694041475438161390541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143560279102952028219329749 3364694041475438161390541)
              ·
                refine ⟨1261760265553289310521453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3364694041475438161390541 1261760265553289310521453)
                ·
                  refine ⟨473160099582483491445545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261760265553289310521453 473160099582483491445545)
                  ·
                    rfl

theorem cell21_2073321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_2073321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073321 prefixEnd_2073321 := by exact prefixLift 2073321
  have htrace : WordTrace (prefixWord ++ tailWord_2073321) baseStart_2073321 baseEnd_2073321 := by
    simpa [prefixWord, tailWord_2073321, baseEnd_2073321] using wordTrace_append hprefix tailTrace_2073321
  have hstable : (prefixWord ++ tailWord_2073321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073321).length < 2 ^ (prefixWord ++ tailWord_2073321).sum := by decide
  have hdescent : baseEnd_2073321 < baseStart_2073321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073352 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_2073352 : Nat := 118140960795 + 2073352 * 2 ^ 59
def prefixEnd_2073352 : Nat := 4983230072969 + 3 ^ 40 * 2073352 * 2
def baseEnd_2073352 : Nat := 473167174204834326428815

theorem tailTrace_2073352 : CollatzResearch.WordTrace tailWord_2073352 prefixEnd_2073352 473167174204834326428815 := by
  unfold tailWord_2073352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37810679992303639587671155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50414239989738186116894873 37810679992303639587671155)
  ·
    refine ⟨56716019988455459381506733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37810679992303639587671155 56716019988455459381506733)
    ·
      refine ⟨21268507495670797268065025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56716019988455459381506733 21268507495670797268065025)
      ·
        refine ⟨15951380621753097951048769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21268507495670797268065025 15951380621753097951048769)
        ·
          refine ⟨11963535466314823463286577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15951380621753097951048769 11963535466314823463286577)
          ·
            refine ⟨8972651599736117597464933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963535466314823463286577 8972651599736117597464933)
            ·
              refine ⟨1682372174950522049524675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8972651599736117597464933 1682372174950522049524675)
              ·
                refine ⟨2523558262425783074287013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682372174950522049524675 2523558262425783074287013)
                ·
                  refine ⟨473167174204834326428815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523558262425783074287013 473167174204834326428815)
                  ·
                    rfl

theorem cell21_2073352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_2073352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073352 prefixEnd_2073352 := by exact prefixLift 2073352
  have htrace : WordTrace (prefixWord ++ tailWord_2073352) baseStart_2073352 baseEnd_2073352 := by
    simpa [prefixWord, tailWord_2073352, baseEnd_2073352] using wordTrace_append hprefix tailTrace_2073352
  have hstable : (prefixWord ++ tailWord_2073352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073352).length < 2 ^ (prefixWord ++ tailWord_2073352).sum := by decide
  have hdescent : baseEnd_2073352 < baseStart_2073352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073363 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_2073363 : Nat := 118140960795 + 2073363 * 2 ^ 59
def prefixEnd_2073363 : Nat := 4983230072969 + 3 ^ 40 * 2073363 * 2
def baseEnd_2073363 : Nat := 473169684554700751745459

theorem tailTrace_2073363 : CollatzResearch.WordTrace tailWord_2073363 prefixEnd_2073363 473169684554700751745459 := by
  unfold tailWord_2073363
  simp only [CollatzResearch.WordTrace]
  refine ⟨75621761187567428053992743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50414507458378285369328495 75621761187567428053992743)
  ·
    refine ⟨113432641781351142080989115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75621761187567428053992743 113432641781351142080989115)
    ·
      refine ⟨170148962672026713121483673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113432641781351142080989115 170148962672026713121483673)
      ·
        refine ⟨127611722004020034841112755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170148962672026713121483673 127611722004020034841112755)
        ·
          refine ⟨191417583006030052261669133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127611722004020034841112755 191417583006030052261669133)
          ·
            refine ⟨71781593627261269598125925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191417583006030052261669133 71781593627261269598125925)
            ·
              refine ⟨13459048805111488049648611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71781593627261269598125925 13459048805111488049648611)
              ·
                refine ⟨20188573207667232074472917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459048805111488049648611 20188573207667232074472917)
                ·
                  refine ⟨473169684554700751745459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20188573207667232074472917 473169684554700751745459)
                  ·
                    rfl

theorem cell21_2073363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_2073363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073363 prefixEnd_2073363 := by exact prefixLift 2073363
  have htrace : WordTrace (prefixWord ++ tailWord_2073363) baseStart_2073363 baseEnd_2073363 := by
    simpa [prefixWord, tailWord_2073363, baseEnd_2073363] using wordTrace_append hprefix tailTrace_2073363
  have hstable : (prefixWord ++ tailWord_2073363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073363).length < 2 ^ (prefixWord ++ tailWord_2073363).sum := by decide
  have hdescent : baseEnd_2073363 < baseStart_2073363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073389 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2073389 : Nat := 118140960795 + 2073389 * 2 ^ 59
def prefixEnd_2073389 : Nat := 4983230072969 + 3 ^ 40 * 2073389 * 2
def baseEnd_2073389 : Nat := 473175618108930484312073

theorem tailTrace_2073389 : CollatzResearch.WordTrace tailWord_2073389 prefixEnd_2073389 473175618108930484312073 := by
  unfold tailWord_2073389
  simp only [CollatzResearch.WordTrace]
  refine ⟨75622709485473234494439221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50415139656982156329626147 75622709485473234494439221)
  ·
    refine ⟨7089629014263115733853677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75622709485473234494439221 7089629014263115733853677)
    ·
      refine ⟨2658610880348668400195129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7089629014263115733853677 2658610880348668400195129)
      ·
        refine ⟨1993958160261501300146347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2658610880348668400195129 1993958160261501300146347)
        ·
          refine ⟨2990937240392251950219521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993958160261501300146347 2990937240392251950219521)
          ·
            refine ⟨2243202930294188962664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990937240392251950219521 2243202930294188962664641)
            ·
              refine ⟨1682402197720641721998481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243202930294188962664641 1682402197720641721998481)
              ·
                refine ⟨1261801648290481291498861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682402197720641721998481 1261801648290481291498861)
                ·
                  refine ⟨473175618108930484312073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261801648290481291498861 473175618108930484312073)
                  ·
                    rfl

theorem cell21_2073389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2073389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073389 prefixEnd_2073389 := by exact prefixLift 2073389
  have htrace : WordTrace (prefixWord ++ tailWord_2073389) baseStart_2073389 baseEnd_2073389 := by
    simpa [prefixWord, tailWord_2073389, baseEnd_2073389] using wordTrace_append hprefix tailTrace_2073389
  have hstable : (prefixWord ++ tailWord_2073389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073389).length < 2 ^ (prefixWord ++ tailWord_2073389).sum := by decide
  have hdescent : baseEnd_2073389 < baseStart_2073389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073439 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_2073439 : Nat := 118140960795 + 2073439 * 2 ^ 59
def prefixEnd_2073439 : Nat := 4983230072969 + 3 ^ 40 * 2073439 * 2
def baseEnd_2073439 : Nat := 473187028790141508478637

theorem tailTrace_2073439 : CollatzResearch.WordTrace tailWord_2073439 prefixEnd_2073439 473187028790141508478637 := by
  unfold tailWord_2073439
  simp only [CollatzResearch.WordTrace]
  refine ⟨75624533135292093033759371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50416355423528062022506247 75624533135292093033759371)
  ·
    refine ⟨113436799702938139550639057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75624533135292093033759371 113436799702938139550639057)
    ·
      refine ⟨85077599777203604662979293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113436799702938139550639057 85077599777203604662979293)
      ·
        refine ⟨31904099916451351748617235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85077599777203604662979293 31904099916451351748617235)
        ·
          refine ⟨47856149874677027622925853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31904099916451351748617235 47856149874677027622925853)
          ·
            refine ⟨17946056203003885358597195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47856149874677027622925853 17946056203003885358597195)
            ·
              refine ⟨26919084304505828037895793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17946056203003885358597195 26919084304505828037895793)
              ·
                refine ⟨20189313228379371028421845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26919084304505828037895793 20189313228379371028421845)
                ·
                  refine ⟨473187028790141508478637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20189313228379371028421845 473187028790141508478637)
                  ·
                    rfl

theorem cell21_2073439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_2073439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073439 prefixEnd_2073439 := by exact prefixLift 2073439
  have htrace : WordTrace (prefixWord ++ tailWord_2073439) baseStart_2073439 baseEnd_2073439 := by
    simpa [prefixWord, tailWord_2073439, baseEnd_2073439] using wordTrace_append hprefix tailTrace_2073439
  have hstable : (prefixWord ++ tailWord_2073439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073439).length < 2 ^ (prefixWord ++ tailWord_2073439).sum := by decide
  have hdescent : baseEnd_2073439 < baseStart_2073439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073442 : List Nat := [3, 3, 2, 1, 3, 1, 8]
def baseStart_2073442 : Nat := 118140960795 + 2073442 * 2 ^ 59
def prefixEnd_2073442 : Nat := 4983230072969 + 3 ^ 40 * 2073442 * 2
def baseEnd_2073442 : Nat := 52576412603446018880959

theorem tailTrace_2073442 : CollatzResearch.WordTrace tailWord_2073442 prefixEnd_2073442 52576412603446018880959 := by
  unfold tailWord_2073442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906160638570306136529645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50416428369520816364079053 18906160638570306136529645)
  ·
    refine ⟨7089810239463864801198617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18906160638570306136529645 7089810239463864801198617)
    ·
      refine ⟨5317357679597898600898963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7089810239463864801198617 5317357679597898600898963)
      ·
        refine ⟨7976036519396847901348445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317357679597898600898963 7976036519396847901348445)
        ·
          refine ⟨2991013694773817963005667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7976036519396847901348445 2991013694773817963005667)
          ·
            refine ⟨4486520542160726944508501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991013694773817963005667 4486520542160726944508501)
            ·
              refine ⟨52576412603446018880959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4486520542160726944508501 52576412603446018880959)
              ·
                rfl

theorem cell21_2073442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 8].length) (baseStart_2073442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073442 prefixEnd_2073442 := by exact prefixLift 2073442
  have htrace : WordTrace (prefixWord ++ tailWord_2073442) baseStart_2073442 baseEnd_2073442 := by
    simpa [prefixWord, tailWord_2073442, baseEnd_2073442] using wordTrace_append hprefix tailTrace_2073442
  have hstable : (prefixWord ++ tailWord_2073442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073442).length < 2 ^ (prefixWord ++ tailWord_2073442).sum := by decide
  have hdescent : baseEnd_2073442 < baseStart_2073442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073521 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 4]
def baseStart_2073521 : Nat := 118140960795 + 2073521 * 2 ^ 59
def prefixEnd_2073521 : Nat := 4983230072969 + 3 ^ 40 * 2073521 * 2
def baseEnd_2073521 : Nat := 473205742307327588111803

theorem tailTrace_2073521 : CollatzResearch.WordTrace tailWord_2073521 prefixEnd_2073521 473205742307327588111803 := by
  unfold tailWord_2073521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75627523920995021038244417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50418349280663347358829611 75627523920995021038244417)
  ·
    refine ⟨56720642940746265778683313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75627523920995021038244417 56720642940746265778683313)
    ·
      refine ⟨42540482205559699334012485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56720642940746265778683313 42540482205559699334012485)
      ·
        refine ⟨7976340413542443625127341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42540482205559699334012485 7976340413542443625127341)
        ·
          refine ⟨2991127655078416359422753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7976340413542443625127341 2991127655078416359422753)
          ·
            refine ⟨2243345741308812269567065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991127655078416359422753 2243345741308812269567065)
            ·
              refine ⟨1682509305981609202175299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243345741308812269567065 1682509305981609202175299)
              ·
                refine ⟨2523763958972413803262949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682509305981609202175299 2523763958972413803262949)
                ·
                  refine ⟨473205742307327588111803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523763958972413803262949 473205742307327588111803)
                  ·
                    rfl

theorem cell21_2073521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_2073521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073521 prefixEnd_2073521 := by exact prefixLift 2073521
  have htrace : WordTrace (prefixWord ++ tailWord_2073521) baseStart_2073521 baseEnd_2073521 := by
    simpa [prefixWord, tailWord_2073521, baseEnd_2073521] using wordTrace_append hprefix tailTrace_2073521
  have hstable : (prefixWord ++ tailWord_2073521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073521).length < 2 ^ (prefixWord ++ tailWord_2073521).sum := by decide
  have hdescent : baseEnd_2073521 < baseStart_2073521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073560 : List Nat := [2, 1, 2, 2, 2, 12]
def baseStart_2073560 : Nat := 118140960795 + 2073560 * 2 ^ 59
def prefixEnd_2073560 : Nat := 4983230072969 + 3 ^ 40 * 2073560 * 2
def baseEnd_2073560 : Nat := 17526468245876747665249

theorem tailTrace_2073560 : CollatzResearch.WordTrace tailWord_2073560 prefixEnd_2073560 17526468245876747665249 := by
  unfold tailWord_2073560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37814473183926865349457067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50419297578569153799276089 37814473183926865349457067)
  ·
    refine ⟨56721709775890298024185601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37814473183926865349457067 56721709775890298024185601)
    ·
      refine ⟨42541282331917723518139201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56721709775890298024185601 42541282331917723518139201)
      ·
        refine ⟨31905961748938292638604401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42541282331917723518139201 31905961748938292638604401)
        ·
          refine ⟨23929471311703719478953301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31905961748938292638604401 23929471311703719478953301)
          ·
            refine ⟨17526468245876747665249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23929471311703719478953301 17526468245876747665249)
            ·
              rfl

theorem cell21_2073560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 12].length) (baseStart_2073560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073560 prefixEnd_2073560 := by exact prefixLift 2073560
  have htrace : WordTrace (prefixWord ++ tailWord_2073560) baseStart_2073560 baseEnd_2073560 := by
    simpa [prefixWord, tailWord_2073560, baseEnd_2073560] using wordTrace_append hprefix tailTrace_2073560
  have hstable : (prefixWord ++ tailWord_2073560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073560).length < 2 ^ (prefixWord ++ tailWord_2073560).sum := by decide
  have hdescent : baseEnd_2073560 < baseStart_2073560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073670 : List Nat := [6, 1, 1, 1, 1, 2, 9]
def baseStart_2073670 : Nat := 118140960795 + 2073670 * 2 ^ 59
def prefixEnd_2073670 : Nat := 4983230072969 + 3 ^ 40 * 2073670 * 2
def baseEnd_2073670 : Nat := 52582194015259604458685

theorem tailTrace_2073670 : CollatzResearch.WordTrace tailWord_2073670 prefixEnd_2073670 52582194015259604458685 := by
  unfold tailWord_2073670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363529949920475608919327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50421972264970146323612309 2363529949920475608919327)
  ·
    refine ⟨3545294924880713413378991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363529949920475608919327 3545294924880713413378991)
    ·
      refine ⟨5317942387321070120068487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545294924880713413378991 5317942387321070120068487)
      ·
        refine ⟨7976913580981605180102731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317942387321070120068487 7976913580981605180102731)
        ·
          refine ⟨11965370371472407770154097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976913580981605180102731 11965370371472407770154097)
          ·
            refine ⟨8974027778604305827615573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11965370371472407770154097 8974027778604305827615573)
            ·
              refine ⟨52582194015259604458685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8974027778604305827615573 52582194015259604458685)
              ·
                rfl

theorem cell21_2073670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 9].length) (baseStart_2073670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073670 prefixEnd_2073670 := by exact prefixLift 2073670
  have htrace : WordTrace (prefixWord ++ tailWord_2073670) baseStart_2073670 baseEnd_2073670 := by
    simpa [prefixWord, tailWord_2073670, baseEnd_2073670] using wordTrace_append hprefix tailTrace_2073670
  have hstable : (prefixWord ++ tailWord_2073670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073670).length < 2 ^ (prefixWord ++ tailWord_2073670).sum := by decide
  have hdescent : baseEnd_2073670 < baseStart_2073670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073684 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2073684 : Nat := 118140960795 + 2073684 * 2 ^ 59
def prefixEnd_2073684 : Nat := 4983230072969 + 3 ^ 40 * 2073684 * 2
def baseEnd_2073684 : Nat := 473242941128075526894803

theorem tailTrace_2073684 : CollatzResearch.WordTrace tailWord_2073684 prefixEnd_2073684 473242941128075526894803 := by
  unfold tailWord_2073684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816734509702249938214053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50422312679602999917618737 37816734509702249938214053)
  ·
    refine ⟨7090637720569171863415135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37816734509702249938214053 7090637720569171863415135)
    ·
      refine ⟨10635956580853757795122703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7090637720569171863415135 10635956580853757795122703)
      ·
        refine ⟨15953934871280636692684055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635956580853757795122703 15953934871280636692684055)
        ·
          refine ⟨23930902306920955039026083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953934871280636692684055 23930902306920955039026083)
          ·
            refine ⟨35896353460381432558539125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23930902306920955039026083 35896353460381432558539125)
            ·
              refine ⟨3365283136910759302363043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35896353460381432558539125 3365283136910759302363043)
              ·
                refine ⟨5047924705366138953544565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365283136910759302363043 5047924705366138953544565)
                ·
                  refine ⟨473242941128075526894803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5047924705366138953544565 473242941128075526894803)
                  ·
                    rfl

theorem cell21_2073684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2073684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073684 prefixEnd_2073684 := by exact prefixLift 2073684
  have htrace : WordTrace (prefixWord ++ tailWord_2073684) baseStart_2073684 baseEnd_2073684 := by
    simpa [prefixWord, tailWord_2073684, baseEnd_2073684] using wordTrace_append hprefix tailTrace_2073684
  have hstable : (prefixWord ++ tailWord_2073684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073684).length < 2 ^ (prefixWord ++ tailWord_2073684).sum := by decide
  have hdescent : baseEnd_2073684 < baseStart_2073684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073712 : List Nat := [2, 1, 1, 1, 5, 1, 1, 9]
def baseStart_2073712 : Nat := 118140960795 + 2073712 * 2 ^ 59
def prefixEnd_2073712 : Nat := 4983230072969 + 3 ^ 40 * 2073712 * 2
def baseEnd_2073712 : Nat := 157749777036517900142693

theorem tailTrace_2073712 : CollatzResearch.WordTrace tailWord_2073712 prefixEnd_2073712 157749777036517900142693 := by
  unfold tailWord_2073712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817245131651530329223695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50422993508868707105631593 37817245131651530329223695)
  ·
    refine ⟨56725867697477295493835543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37817245131651530329223695 56725867697477295493835543)
    ·
      refine ⟨85088801546215943240753315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56725867697477295493835543 85088801546215943240753315)
      ·
        refine ⟨127633202319323914861129973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85088801546215943240753315 127633202319323914861129973)
        ·
          refine ⟨11965612717436617018230935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127633202319323914861129973 11965612717436617018230935)
          ·
            refine ⟨17948419076154925527346403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965612717436617018230935 17948419076154925527346403)
            ·
              refine ⟨26922628614232388291019605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17948419076154925527346403 26922628614232388291019605)
              ·
                refine ⟨157749777036517900142693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26922628614232388291019605 157749777036517900142693)
                ·
                  rfl

theorem cell21_2073712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_2073712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073712 prefixEnd_2073712 := by exact prefixLift 2073712
  have htrace : WordTrace (prefixWord ++ tailWord_2073712) baseStart_2073712 baseEnd_2073712 := by
    simpa [prefixWord, tailWord_2073712, baseEnd_2073712] using wordTrace_append hprefix tailTrace_2073712
  have hstable : (prefixWord ++ tailWord_2073712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073712).length < 2 ^ (prefixWord ++ tailWord_2073712).sum := by decide
  have hdescent : baseEnd_2073712 < baseStart_2073712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073746 : List Nat := [3, 2, 3, 1, 1, 4, 1, 6]
def baseStart_2073746 : Nat := 118140960795 + 2073746 * 2 ^ 59
def prefixEnd_2073746 : Nat := 4983230072969 + 3 ^ 40 * 2073746 * 2
def baseEnd_2073746 : Nat := 157752363457592398953781

theorem tailTrace_2073746 : CollatzResearch.WordTrace tailWord_2073746 prefixEnd_2073746 157752363457592398953781 := by
  unfold tailWord_2073746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908932586294971116296273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50423820230119922976790061 18908932586294971116296273)
  ·
    refine ⟨14181699439721228337222205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18908932586294971116296273 14181699439721228337222205)
    ·
      refine ⟨5318137289895460626458327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14181699439721228337222205 5318137289895460626458327)
      ·
        refine ⟨7977205934843190939687491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318137289895460626458327 7977205934843190939687491)
        ·
          refine ⟨11965808902264786409531237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977205934843190939687491 11965808902264786409531237)
          ·
            refine ⟨2243589169174647451787107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11965808902264786409531237 2243589169174647451787107)
            ·
              refine ⟨3365383753761971177680661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243589169174647451787107 3365383753761971177680661)
              ·
                refine ⟨157752363457592398953781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3365383753761971177680661 157752363457592398953781)
                ·
                  rfl

theorem cell21_2073746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_2073746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073746 prefixEnd_2073746 := by exact prefixLift 2073746
  have htrace : WordTrace (prefixWord ++ tailWord_2073746) baseStart_2073746 baseEnd_2073746 := by
    simpa [prefixWord, tailWord_2073746, baseEnd_2073746] using wordTrace_append hprefix tailTrace_2073746
  have hstable : (prefixWord ++ tailWord_2073746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073746).length < 2 ^ (prefixWord ++ tailWord_2073746).sum := by decide
  have hdescent : baseEnd_2073746 < baseStart_2073746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073777 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 3]
def baseStart_2073777 : Nat := 118140960795 + 2073777 * 2 ^ 59
def prefixEnd_2073777 : Nat := 4983230072969 + 3 ^ 40 * 2073777 * 2
def baseEnd_2073777 : Nat := 473264164995128031844613

theorem tailTrace_2073777 : CollatzResearch.WordTrace tailWord_2073777 prefixEnd_2073777 473264164995128031844613 := by
  unfold tailWord_2073777
  simp only [CollatzResearch.WordTrace]
  refine ⟨75636861008067576759563585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50424574005378384506375723 75636861008067576759563585)
  ·
    refine ⟨56727645756050682569672689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75636861008067576759563585 56727645756050682569672689)
    ·
      refine ⟨42545734317038011927254517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56727645756050682569672689 42545734317038011927254517)
      ·
        refine ⟨3988662592222313618180111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42545734317038011927254517 3988662592222313618180111)
        ·
          refine ⟨5982993888333470427270167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988662592222313618180111 5982993888333470427270167)
          ·
            refine ⟨8974490832500205640905251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982993888333470427270167 8974490832500205640905251)
            ·
              refine ⟨13461736248750308461357877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974490832500205640905251 13461736248750308461357877)
              ·
                refine ⟨1262037773320341418252301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13461736248750308461357877 1262037773320341418252301)
                ·
                  refine ⟨473264164995128031844613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262037773320341418252301 473264164995128031844613)
                  ·
                    rfl

theorem cell21_2073777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_2073777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073777 prefixEnd_2073777 := by exact prefixLift 2073777
  have htrace : WordTrace (prefixWord ++ tailWord_2073777) baseStart_2073777 baseEnd_2073777 := by
    simpa [prefixWord, tailWord_2073777, baseEnd_2073777] using wordTrace_append hprefix tailTrace_2073777
  have hstable : (prefixWord ++ tailWord_2073777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073777).length < 2 ^ (prefixWord ++ tailWord_2073777).sum := by decide
  have hdescent : baseEnd_2073777 < baseStart_2073777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073850 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_2073850 : Nat := 118140960795 + 2073850 * 2 ^ 59
def prefixEnd_2073850 : Nat := 4983230072969 + 3 ^ 40 * 2073850 * 2
def baseEnd_2073850 : Nat := 473280824589696127127797

theorem tailTrace_2073850 : CollatzResearch.WordTrace tailWord_2073850 prefixEnd_2073850 473280824589696127127797 := by
  unfold tailWord_2073850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909880884200777556742751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50426349024535406817980669 18909880884200777556742751)
  ·
    refine ⟨28364821326301166335114127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18909880884200777556742751 28364821326301166335114127)
    ·
      refine ⟨42547231989451749502671191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28364821326301166335114127 42547231989451749502671191)
      ·
        refine ⟨63820847984177624254006787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42547231989451749502671191 63820847984177624254006787)
        ·
          refine ⟨95731271976266436381010181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63820847984177624254006787 95731271976266436381010181)
          ·
            refine ⟨17949613495549956821439409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95731271976266436381010181 17949613495549956821439409)
            ·
              refine ⟨13462210121662467616079557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17949613495549956821439409 13462210121662467616079557)
              ·
                refine ⟨2524164397811712678014917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13462210121662467616079557 2524164397811712678014917)
                ·
                  refine ⟨473280824589696127127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524164397811712678014917 473280824589696127127797)
                  ·
                    rfl

theorem cell21_2073850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_2073850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073850 prefixEnd_2073850 := by exact prefixLift 2073850
  have htrace : WordTrace (prefixWord ++ tailWord_2073850) baseStart_2073850 baseEnd_2073850 := by
    simpa [prefixWord, tailWord_2073850, baseEnd_2073850] using wordTrace_append hprefix tailTrace_2073850
  have hstable : (prefixWord ++ tailWord_2073850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073850).length < 2 ^ (prefixWord ++ tailWord_2073850).sum := by decide
  have hdescent : baseEnd_2073850 < baseStart_2073850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073867 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 4]
def baseStart_2073867 : Nat := 118140960795 + 2073867 * 2 ^ 59
def prefixEnd_2073867 : Nat := 4983230072969 + 3 ^ 40 * 2073867 * 2
def baseEnd_2073867 : Nat := 473284704221307875344429

theorem tailTrace_2073867 : CollatzResearch.WordTrace tailWord_2073867 prefixEnd_2073867 473284704221307875344429 := by
  unfold tailWord_2073867
  simp only [CollatzResearch.WordTrace]
  refine ⟨75640143577741522130339855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50426762385161014753559903 75640143577741522130339855)
  ·
    refine ⟨113460215366612283195509783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75640143577741522130339855 113460215366612283195509783)
    ·
      refine ⟨170190323049918424793264675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113460215366612283195509783 170190323049918424793264675)
      ·
        refine ⟨255285484574877637189897013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170190323049918424793264675 255285484574877637189897013)
        ·
          refine ⟨23933014178894778486552845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255285484574877637189897013 23933014178894778486552845)
          ·
            refine ⟨8974880317085541932457317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23933014178894778486552845 8974880317085541932457317)
            ·
              refine ⟨1682790059453539112335747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8974880317085541932457317 1682790059453539112335747)
              ·
                refine ⟨2524185089180308668503621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682790059453539112335747 2524185089180308668503621)
                ·
                  refine ⟨473284704221307875344429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524185089180308668503621 473284704221307875344429)
                  ·
                    rfl

theorem cell21_2073867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_2073867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073867 prefixEnd_2073867 := by exact prefixLift 2073867
  have htrace : WordTrace (prefixWord ++ tailWord_2073867) baseStart_2073867 baseEnd_2073867 := by
    simpa [prefixWord, tailWord_2073867, baseEnd_2073867] using wordTrace_append hprefix tailTrace_2073867
  have hstable : (prefixWord ++ tailWord_2073867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073867).length < 2 ^ (prefixWord ++ tailWord_2073867).sum := by decide
  have hdescent : baseEnd_2073867 < baseStart_2073867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073960 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_2073960 : Nat := 118140960795 + 2073960 * 2 ^ 59
def prefixEnd_2073960 : Nat := 4983230072969 + 3 ^ 40 * 2073960 * 2
def baseEnd_2073960 : Nat := 473305928088360380294239

theorem tailTrace_2073960 : CollatzResearch.WordTrace tailWord_2073960 prefixEnd_2073960 473305928088360380294239 := by
  unfold tailWord_2073960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37821767783202299506737667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50429023710936399342316889 37821767783202299506737667)
  ·
    refine ⟨56732651674803449260106501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37821767783202299506737667 56732651674803449260106501)
    ·
      refine ⟨10637372189025646736269969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56732651674803449260106501 10637372189025646736269969)
      ·
        refine ⟨7978029141769235052202477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10637372189025646736269969 7978029141769235052202477)
        ·
          refine ⟨2991760928163463144575929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7978029141769235052202477 2991760928163463144575929)
          ·
            refine ⟨2243820696122597358431947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991760928163463144575929 2243820696122597358431947)
            ·
              refine ⟨3365731044183896037647921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243820696122597358431947 3365731044183896037647921)
              ·
                refine ⟨2524298283137922028235941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365731044183896037647921 2524298283137922028235941)
                ·
                  refine ⟨473305928088360380294239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524298283137922028235941 473305928088360380294239)
                  ·
                    rfl

theorem cell21_2073960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_2073960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2073960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2073960 prefixEnd_2073960 := by exact prefixLift 2073960
  have htrace : WordTrace (prefixWord ++ tailWord_2073960) baseStart_2073960 baseEnd_2073960 := by
    simpa [prefixWord, tailWord_2073960, baseEnd_2073960] using wordTrace_append hprefix tailTrace_2073960
  have hstable : (prefixWord ++ tailWord_2073960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073960).length < 2 ^ (prefixWord ++ tailWord_2073960).sum := by decide
  have hdescent : baseEnd_2073960 < baseStart_2073960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074081 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 3]
def baseStart_2074081 : Nat := 118140960795 + 2074081 * 2 ^ 59
def prefixEnd_2074081 : Nat := 4983230072969 + 3 ^ 40 * 2074081 * 2
def baseEnd_2074081 : Nat := 473333541936891058777325

theorem tailTrace_2074081 : CollatzResearch.WordTrace tailWord_2074081 prefixEnd_2074081 473333541936891058777325 := by
  unfold tailWord_2074081
  simp only [CollatzResearch.WordTrace]
  refine ⟨75647948798966236678630097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50431965865977491119086731 75647948798966236678630097)
  ·
    refine ⟨56735961599224677508972573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75647948798966236678630097 56735961599224677508972573)
    ·
      refine ⟨21275985599709254065864715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56735961599224677508972573 21275985599709254065864715)
      ·
        refine ⟨31913978399563881098797073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21275985599709254065864715 31913978399563881098797073)
        ·
          refine ⟨23935483799672910824097805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31913978399563881098797073 23935483799672910824097805)
          ·
            refine ⟨8975806424877341559036677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23935483799672910824097805 8975806424877341559036677)
            ·
              refine ⟨1682963704664501542319377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8975806424877341559036677 1682963704664501542319377)
              ·
                refine ⟨1262222778498376156739533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682963704664501542319377 1262222778498376156739533)
                ·
                  refine ⟨473333541936891058777325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262222778498376156739533 473333541936891058777325)
                  ·
                    rfl

theorem cell21_2074081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_2074081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074081 prefixEnd_2074081 := by exact prefixLift 2074081
  have htrace : WordTrace (prefixWord ++ tailWord_2074081) baseStart_2074081 baseEnd_2074081 := by
    simpa [prefixWord, tailWord_2074081, baseEnd_2074081] using wordTrace_append hprefix tailTrace_2074081
  have hstable : (prefixWord ++ tailWord_2074081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074081).length < 2 ^ (prefixWord ++ tailWord_2074081).sum := by decide
  have hdescent : baseEnd_2074081 < baseStart_2074081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074109 : List Nat := [1, 4, 1, 1, 1, 5, 3, 5]
def baseStart_2074109 : Nat := 118140960795 + 2074109 * 2 ^ 59
def prefixEnd_2074109 : Nat := 4983230072969 + 3 ^ 40 * 2074109 * 2
def baseEnd_2074109 : Nat := 157779977306123077436867

theorem tailTrace_2074109 : CollatzResearch.WordTrace tailWord_2074109 prefixEnd_2074109 157779977306123077436867 := by
  unfold tailWord_2074109
  simp only [CollatzResearch.WordTrace]
  refine ⟨75648970042864797460649381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50432646695243198307099587 75648970042864797460649381)
  ·
    refine ⟨14184181883037149523871759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75648970042864797460649381 14184181883037149523871759)
    ·
      refine ⟨21276272824555724285807639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14184181883037149523871759 21276272824555724285807639)
      ·
        refine ⟨31914409236833586428711459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276272824555724285807639 31914409236833586428711459)
        ·
          refine ⟨47871613855250379643067189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31914409236833586428711459 47871613855250379643067189)
          ·
            refine ⟨4487963798929723091537549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47871613855250379643067189 4487963798929723091537549)
            ·
              refine ⟨1682986424598646159326581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4487963798929723091537549 1682986424598646159326581)
              ·
                refine ⟨157779977306123077436867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1682986424598646159326581 157779977306123077436867)
                ·
                  rfl

theorem cell21_2074109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].length) (baseStart_2074109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074109 prefixEnd_2074109 := by exact prefixLift 2074109
  have htrace : WordTrace (prefixWord ++ tailWord_2074109) baseStart_2074109 baseEnd_2074109 := by
    simpa [prefixWord, tailWord_2074109, baseEnd_2074109] using wordTrace_append hprefix tailTrace_2074109
  have hstable : (prefixWord ++ tailWord_2074109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074109).length < 2 ^ (prefixWord ++ tailWord_2074109).sum := by decide
  have hdescent : baseEnd_2074109 < baseStart_2074109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074140 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2074140 : Nat := 118140960795 + 2074140 * 2 ^ 59
def prefixEnd_2074140 : Nat := 4983230072969 + 3 ^ 40 * 2074140 * 2
def baseEnd_2074140 : Nat := 473347006540720067293871

theorem tailTrace_2074140 : CollatzResearch.WordTrace tailWord_2074140 prefixEnd_2074140 473347006540720067293871 := by
  unfold tailWord_2074140
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825050352876244877513937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50433400470501659836685249 37825050352876244877513937)
  ·
    refine ⟨28368787764657183658135453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37825050352876244877513937 28368787764657183658135453)
    ·
      refine ⟨10638295411746443871800795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28368787764657183658135453 10638295411746443871800795)
      ·
        refine ⟨15957443117619665807701193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638295411746443871800795 15957443117619665807701193)
        ·
          refine ⟨11968082338214749355775895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15957443117619665807701193 11968082338214749355775895)
          ·
            refine ⟨17952123507322124033663843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968082338214749355775895 17952123507322124033663843)
            ·
              refine ⟨26928185260983186050495765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952123507322124033663843 26928185260983186050495765)
              ·
                refine ⟨1262258684108586846116989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26928185260983186050495765 1262258684108586846116989)
                ·
                  refine ⟨473347006540720067293871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262258684108586846116989 473347006540720067293871)
                  ·
                    rfl

theorem cell21_2074140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2074140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074140 prefixEnd_2074140 := by exact prefixLift 2074140
  have htrace : WordTrace (prefixWord ++ tailWord_2074140) baseStart_2074140 baseEnd_2074140 := by
    simpa [prefixWord, tailWord_2074140, baseEnd_2074140] using wordTrace_append hprefix tailTrace_2074140
  have hstable : (prefixWord ++ tailWord_2074140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074140).length < 2 ^ (prefixWord ++ tailWord_2074140).sum := by decide
  have hdescent : baseEnd_2074140 < baseStart_2074140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074168 : List Nat := [2, 1, 2, 1, 4, 3, 1, 7]
def baseStart_2074168 : Nat := 118140960795 + 2074168 * 2 ^ 59
def prefixEnd_2074168 : Nat := 4983230072969 + 3 ^ 40 * 2074168 * 2
def baseEnd_2074168 : Nat := 157784465507399413609049

theorem tailTrace_2074168 : CollatzResearch.WordTrace tailWord_2074168 prefixEnd_2074168 157784465507399413609049 := by
  unfold tailWord_2074168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825560974825525268523579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50434081299767367024698105 37825560974825525268523579)
  ·
    refine ⟨56738341462238287902785369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37825560974825525268523579 56738341462238287902785369)
    ·
      refine ⟨42553756096678715927089027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56738341462238287902785369 42553756096678715927089027)
      ·
        refine ⟨63830634145018073890633541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42553756096678715927089027 63830634145018073890633541)
        ·
          refine ⟨11968243902190888854493789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63830634145018073890633541 11968243902190888854493789)
          ·
            refine ⟨4488091463321583320435171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11968243902190888854493789 4488091463321583320435171)
            ·
              refine ⟨6732137194982374980652757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488091463321583320435171 6732137194982374980652757)
              ·
                refine ⟨157784465507399413609049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6732137194982374980652757 157784465507399413609049)
                ·
                  rfl

theorem cell21_2074168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_2074168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074168 prefixEnd_2074168 := by exact prefixLift 2074168
  have htrace : WordTrace (prefixWord ++ tailWord_2074168) baseStart_2074168 baseEnd_2074168 := by
    simpa [prefixWord, tailWord_2074168, baseEnd_2074168] using wordTrace_append hprefix tailTrace_2074168
  have hstable : (prefixWord ++ tailWord_2074168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074168).length < 2 ^ (prefixWord ++ tailWord_2074168).sum := by decide
  have hdescent : baseEnd_2074168 < baseStart_2074168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074199 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_2074199 : Nat := 118140960795 + 2074199 * 2 ^ 59
def prefixEnd_2074199 : Nat := 4983230072969 + 3 ^ 40 * 2074199 * 2
def baseEnd_2074199 : Nat := 473360471144549075810417

theorem tailTrace_2074199 : CollatzResearch.WordTrace tailWord_2074199 prefixEnd_2074199 473360471144549075810417 := by
  unfold tailWord_2074199
  simp only [CollatzResearch.WordTrace]
  refine ⟨75652252612538742831425651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50434835075025828554283767 75652252612538742831425651)
  ·
    refine ⟨113478378918808114247138477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75652252612538742831425651 113478378918808114247138477)
    ·
      refine ⟨42554392094553042842676929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113478378918808114247138477 42554392094553042842676929)
      ·
        refine ⟨31915794070914782132007697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42554392094553042842676929 31915794070914782132007697)
        ·
          refine ⟨23936845553186086599005773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31915794070914782132007697 23936845553186086599005773)
          ·
            refine ⟨8976317082444782474627165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23936845553186086599005773 8976317082444782474627165)
            ·
              refine ⟨3366118905916793427985187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8976317082444782474627165 3366118905916793427985187)
              ·
                refine ⟨5049178358875190141977781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366118905916793427985187 5049178358875190141977781)
                ·
                  refine ⟨473360471144549075810417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5049178358875190141977781 473360471144549075810417)
                  ·
                    rfl

theorem cell21_2074199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_2074199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074199 prefixEnd_2074199 := by exact prefixLift 2074199
  have htrace : WordTrace (prefixWord ++ tailWord_2074199) baseStart_2074199 baseEnd_2074199 := by
    simpa [prefixWord, tailWord_2074199, baseEnd_2074199] using wordTrace_append hprefix tailTrace_2074199
  have hstable : (prefixWord ++ tailWord_2074199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074199).length < 2 ^ (prefixWord ++ tailWord_2074199).sum := by decide
  have hdescent : baseEnd_2074199 < baseStart_2074199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074244 : List Nat := [2, 3, 2, 1, 4, 9]
def baseStart_2074244 : Nat := 118140960795 + 2074244 * 2 ^ 59
def prefixEnd_2074244 : Nat := 4983230072969 + 3 ^ 40 * 2074244 * 2
def baseEnd_2074244 : Nat := 17532249657690333242975

theorem tailTrace_2074244 : CollatzResearch.WordTrace tailWord_2074244 prefixEnd_2074244 17532249657690333242975 := by
  unfold tailWord_2074244
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826946948687857758406893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50435929264917143677875857 37826946948687857758406893)
  ·
    refine ⟨14185105105757946659402585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37826946948687857758406893 14185105105757946659402585)
    ·
      refine ⟨10638828829318459994551939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14185105105757946659402585 10638828829318459994551939)
      ·
        refine ⟨15958243243977689991827909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638828829318459994551939 15958243243977689991827909)
        ·
          refine ⟨2992170608245816873467733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15958243243977689991827909 2992170608245816873467733)
          ·
            refine ⟨17532249657690333242975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2992170608245816873467733 17532249657690333242975)
            ·
              rfl

theorem cell21_2074244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 9].length) (baseStart_2074244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074244 prefixEnd_2074244 := by exact prefixLift 2074244
  have htrace : WordTrace (prefixWord ++ tailWord_2074244) baseStart_2074244 baseEnd_2074244 := by
    simpa [prefixWord, tailWord_2074244, baseEnd_2074244] using wordTrace_append hprefix tailTrace_2074244
  have hstable : (prefixWord ++ tailWord_2074244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074244).length < 2 ^ (prefixWord ++ tailWord_2074244).sum := by decide
  have hdescent : baseEnd_2074244 < baseStart_2074244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074250 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_2074250 : Nat := 118140960795 + 2074250 * 2 ^ 59
def prefixEnd_2074250 : Nat := 4983230072969 + 3 ^ 40 * 2074250 * 2
def baseEnd_2074250 : Nat := 473372110039384320460313

theorem tailTrace_2074250 : CollatzResearch.WordTrace tailWord_2074250 prefixEnd_2074250 473372110039384320460313 := by
  unfold tailWord_2074250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18913528183838494635383051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50436075156902652361021469 18913528183838494635383051)
  ·
    refine ⟨28370292275757741953074577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18913528183838494635383051 28370292275757741953074577)
    ·
      refine ⟨21277719206818306464805933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28370292275757741953074577 21277719206818306464805933)
      ·
        refine ⟨7979144702556864924302225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21277719206818306464805933 7979144702556864924302225)
        ·
          refine ⟨5984358526917648693226669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979144702556864924302225 5984358526917648693226669)
          ·
            refine ⟨2244134447594118259960001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5984358526917648693226669 2244134447594118259960001)
            ·
              refine ⟨1683100835695588694970001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244134447594118259960001 1683100835695588694970001)
              ·
                refine ⟨1262325626771691521227501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683100835695588694970001 1262325626771691521227501)
                ·
                  refine ⟨473372110039384320460313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262325626771691521227501 473372110039384320460313)
                  ·
                    rfl

theorem cell21_2074250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_2074250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074250 prefixEnd_2074250 := by exact prefixLift 2074250
  have htrace : WordTrace (prefixWord ++ tailWord_2074250) baseStart_2074250 baseEnd_2074250 := by
    simpa [prefixWord, tailWord_2074250, baseEnd_2074250] using wordTrace_append hprefix tailTrace_2074250
  have hstable : (prefixWord ++ tailWord_2074250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074250).length < 2 ^ (prefixWord ++ tailWord_2074250).sum := by decide
  have hdescent : baseEnd_2074250 < baseStart_2074250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074303 : List Nat := [1, 1, 2, 2, 2, 3, 10]
def baseStart_2074303 : Nat := 118140960795 + 2074303 * 2 ^ 59
def prefixEnd_2074303 : Nat := 4983230072969 + 3 ^ 40 * 2074303 * 2
def baseEnd_2074303 : Nat := 52598245040163111786319

theorem tailTrace_2074303 : CollatzResearch.WordTrace tailWord_2074303 prefixEnd_2074303 52598245040163111786319 := by
  unfold tailWord_2074303
  simp only [CollatzResearch.WordTrace]
  refine ⟨75656045804161968593211563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50437363869441312395474375 75656045804161968593211563)
  ·
    refine ⟨113484068706242952889817345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75656045804161968593211563 113484068706242952889817345)
    ·
      refine ⟨85113051529682214667363009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113484068706242952889817345 85113051529682214667363009)
      ·
        refine ⟨63834788647261661000522257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85113051529682214667363009 63834788647261661000522257)
        ·
          refine ⟨47876091485446245750391693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63834788647261661000522257 47876091485446245750391693)
          ·
            refine ⟨17953534307042342156396885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47876091485446245750391693 17953534307042342156396885)
            ·
              refine ⟨52598245040163111786319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17953534307042342156396885 52598245040163111786319)
              ·
                rfl

theorem cell21_2074303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_2074303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074303 prefixEnd_2074303 := by exact prefixLift 2074303
  have htrace : WordTrace (prefixWord ++ tailWord_2074303) baseStart_2074303 baseEnd_2074303 := by
    simpa [prefixWord, tailWord_2074303, baseEnd_2074303] using wordTrace_append hprefix tailTrace_2074303
  have hstable : (prefixWord ++ tailWord_2074303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074303).length < 2 ^ (prefixWord ++ tailWord_2074303).sum := by decide
  have hdescent : baseEnd_2074303 < baseStart_2074303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074343 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 3]
def baseStart_2074343 : Nat := 118140960795 + 2074343 * 2 ^ 59
def prefixEnd_2074343 : Nat := 4983230072969 + 3 ^ 40 * 2074343 * 2
def baseEnd_2074343 : Nat := 473393333906436825410123

theorem tailTrace_2074343 : CollatzResearch.WordTrace tailWord_2074343 prefixEnd_2074343 473393333906436825410123 := by
  unfold tailWord_2074343
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657504724017055424667683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50438336482678036949778455 75657504724017055424667683)
  ·
    refine ⟨113486257086025583137001525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75657504724017055424667683 113486257086025583137001525)
    ·
      refine ⟨10639336601814898419093893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113486257086025583137001525 10639336601814898419093893)
      ·
        refine ⟨1994875612840293453580105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10639336601814898419093893 1994875612840293453580105)
        ·
          refine ⟨1496156709630220090185079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994875612840293453580105 1496156709630220090185079)
          ·
            refine ⟨2244235064445330135277619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496156709630220090185079 2244235064445330135277619)
            ·
              refine ⟨3366352596667995202916429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244235064445330135277619 3366352596667995202916429)
              ·
                refine ⟨1262382223750498201093661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3366352596667995202916429 1262382223750498201093661)
                ·
                  refine ⟨473393333906436825410123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262382223750498201093661 473393333906436825410123)
                  ·
                    rfl

theorem cell21_2074343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].length) (baseStart_2074343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074343 prefixEnd_2074343 := by exact prefixLift 2074343
  have htrace : WordTrace (prefixWord ++ tailWord_2074343) baseStart_2074343 baseEnd_2074343 := by
    simpa [prefixWord, tailWord_2074343, baseEnd_2074343] using wordTrace_append hprefix tailTrace_2074343
  have hstable : (prefixWord ++ tailWord_2074343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074343).length < 2 ^ (prefixWord ++ tailWord_2074343).sum := by decide
  have hdescent : baseEnd_2074343 < baseStart_2074343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074379 : List Nat := [1, 1, 1, 1, 5, 1, 3, 8]
def baseStart_2074379 : Nat := 118140960795 + 2074379 * 2 ^ 59
def prefixEnd_2074379 : Nat := 4983230072969 + 3 ^ 40 * 2074379 * 2
def baseEnd_2074379 : Nat := 157800516532302920936683

theorem tailTrace_2074379 : CollatzResearch.WordTrace tailWord_2074379 prefixEnd_2074379 157800516532302920936683 := by
  unfold tailWord_2074379
  simp only [CollatzResearch.WordTrace]
  refine ⟨75658817751886633572978191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50439211834591089048652127 75658817751886633572978191)
  ·
    refine ⟨113488226627829950359467287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75658817751886633572978191 113488226627829950359467287)
    ·
      refine ⟨170232339941744925539200931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113488226627829950359467287 170232339941744925539200931)
      ·
        refine ⟨255348509912617388308801397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170232339941744925539200931 255348509912617388308801397)
        ·
          refine ⟨23938922804307880153950131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255348509912617388308801397 23938922804307880153950131)
          ·
            refine ⟨35908384206461820230925197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23938922804307880153950131 35908384206461820230925197)
            ·
              refine ⟨13465644077423182586596949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35908384206461820230925197 13465644077423182586596949)
              ·
                refine ⟨157800516532302920936683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13465644077423182586596949 157800516532302920936683)
                ·
                  rfl

theorem cell21_2074379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_2074379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074379 prefixEnd_2074379 := by exact prefixLift 2074379
  have htrace : WordTrace (prefixWord ++ tailWord_2074379) baseStart_2074379 baseEnd_2074379 := by
    simpa [prefixWord, tailWord_2074379, baseEnd_2074379] using wordTrace_append hprefix tailTrace_2074379
  have hstable : (prefixWord ++ tailWord_2074379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074379).length < 2 ^ (prefixWord ++ tailWord_2074379).sum := by decide
  have hdescent : baseEnd_2074379 < baseStart_2074379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074441 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_2074441 : Nat := 118140960795 + 2074441 * 2 ^ 59
def prefixEnd_2074441 : Nat := 4983230072969 + 3 ^ 40 * 2074441 * 2
def baseEnd_2074441 : Nat := 473415698841610432776589

theorem tailTrace_2074441 : CollatzResearch.WordTrace tailWord_2074441 prefixEnd_2074441 473415698841610432776589 := by
  unfold tailWord_2074441
  simp only [CollatzResearch.WordTrace]
  refine ⟨75661079077662018161735177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50440719385108012107823451 75661079077662018161735177)
  ·
    refine ⟨56745809308246513621301383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75661079077662018161735177 56745809308246513621301383)
    ·
      refine ⟨85118713962369770431952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56745809308246513621301383 85118713962369770431952075)
      ·
        refine ⟨127678070943554655647928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85118713962369770431952075 127678070943554655647928113)
        ·
          refine ⟨95758553207665991735946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127678070943554655647928113 95758553207665991735946085)
          ·
            refine ⟨17954728726437373450489891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95758553207665991735946085 17954728726437373450489891)
            ·
              refine ⟨26932093089656060175734837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17954728726437373450489891 26932093089656060175734837)
              ·
                refine ⟨2524883727155255641475141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26932093089656060175734837 2524883727155255641475141)
                ·
                  refine ⟨473415698841610432776589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524883727155255641475141 473415698841610432776589)
                  ·
                    rfl

theorem cell21_2074441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_2074441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074441 prefixEnd_2074441 := by exact prefixLift 2074441
  have htrace : WordTrace (prefixWord ++ tailWord_2074441) baseStart_2074441 baseEnd_2074441 := by
    simpa [prefixWord, tailWord_2074441, baseEnd_2074441] using wordTrace_append hprefix tailTrace_2074441
  have hstable : (prefixWord ++ tailWord_2074441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074441).length < 2 ^ (prefixWord ++ tailWord_2074441).sum := by decide
  have hdescent : baseEnd_2074441 < baseStart_2074441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074506 : List Nat := [3, 1, 2, 4, 2, 2, 2, 5]
def baseStart_2074506 : Nat := 118140960795 + 2074506 * 2 ^ 59
def prefixEnd_2074506 : Nat := 4983230072969 + 3 ^ 40 * 2074506 * 2
def baseEnd_2074506 : Nat := 157810177575728254731041

theorem tailTrace_2074506 : CollatzResearch.WordTrace tailWord_2074506 prefixEnd_2074506 157810177575728254731041 := by
  unfold tailWord_2074506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915862455606633565712843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50442299881617689508567581 18915862455606633565712843)
  ·
    refine ⟨28373793683409950348569265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915862455606633565712843 28373793683409950348569265)
    ·
      refine ⟨21280345262557462761426949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28373793683409950348569265 21280345262557462761426949)
      ·
        refine ⟨3990064736729524267767553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21280345262557462761426949 3990064736729524267767553)
        ·
          refine ⟨2992548552547143200825665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990064736729524267767553 2992548552547143200825665)
          ·
            refine ⟨2244411414410357400619249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992548552547143200825665 2244411414410357400619249)
            ·
              refine ⟨1683308560807768050464437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244411414410357400619249 1683308560807768050464437)
              ·
                refine ⟨157810177575728254731041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1683308560807768050464437 157810177575728254731041)
                ·
                  rfl

theorem cell21_2074506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_2074506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074506 prefixEnd_2074506 := by exact prefixLift 2074506
  have htrace : WordTrace (prefixWord ++ tailWord_2074506) baseStart_2074506 baseEnd_2074506 := by
    simpa [prefixWord, tailWord_2074506, baseEnd_2074506] using wordTrace_append hprefix tailTrace_2074506
  have hstable : (prefixWord ++ tailWord_2074506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074506).length < 2 ^ (prefixWord ++ tailWord_2074506).sum := by decide
  have hdescent : baseEnd_2074506 < baseStart_2074506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074576 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_2074576 : Nat := 118140960795 + 2074576 * 2 ^ 59
def prefixEnd_2074576 : Nat := 4983230072969 + 3 ^ 40 * 2074576 * 2
def baseEnd_2074576 : Nat := 473446507680880198026313

theorem tailTrace_2074576 : CollatzResearch.WordTrace tailWord_2074576 prefixEnd_2074576 473446507680880198026313 := by
  unfold tailWord_2074576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833001466086468108949791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50444001954781957478599721 37833001466086468108949791)
  ·
    refine ⟨56749502199129702163424687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37833001466086468108949791 56749502199129702163424687)
    ·
      refine ⟨85124253298694553245137031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56749502199129702163424687 85124253298694553245137031)
      ·
        refine ⟨127686379948041829867705547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85124253298694553245137031 127686379948041829867705547)
        ·
          refine ⟨191529569922062744801558321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127686379948041829867705547 191529569922062744801558321)
          ·
            refine ⟨143647177441547058601168741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191529569922062744801558321 143647177441547058601168741)
            ·
              refine ⟨26933845770290073487719139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143647177441547058601168741 26933845770290073487719139)
              ·
                refine ⟨40400768655435110231578709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933845770290073487719139 40400768655435110231578709)
                ·
                  refine ⟨473446507680880198026313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40400768655435110231578709 473446507680880198026313)
                  ·
                    rfl

theorem cell21_2074576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_2074576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074576 prefixEnd_2074576 := by exact prefixLift 2074576
  have htrace : WordTrace (prefixWord ++ tailWord_2074576) baseStart_2074576 baseEnd_2074576 := by
    simpa [prefixWord, tailWord_2074576, baseEnd_2074576] using wordTrace_append hprefix tailTrace_2074576
  have hstable : (prefixWord ++ tailWord_2074576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074576).length < 2 ^ (prefixWord ++ tailWord_2074576).sum := by decide
  have hdescent : baseEnd_2074576 < baseStart_2074576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074588 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_2074588 : Nat := 118140960795 + 2074588 * 2 ^ 59
def prefixEnd_2074588 : Nat := 4983230072969 + 3 ^ 40 * 2074588 * 2
def baseEnd_2074588 : Nat := 473449246244370843826289

theorem tailTrace_2074588 : CollatzResearch.WordTrace tailWord_2074588 prefixEnd_2074588 473449246244370843826289 := by
  unfold tailWord_2074588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833220304064731133668209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50444293738752974844890945 37833220304064731133668209)
  ·
    refine ⟨28374915228048548350251157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37833220304064731133668209 28374915228048548350251157)
    ·
      refine ⟨1330074151314775703918023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28374915228048548350251157 1330074151314775703918023)
      ·
        refine ⟨1995111226972163555877035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330074151314775703918023 1995111226972163555877035)
        ·
          refine ⟨2992666840458245333815553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995111226972163555877035 2992666840458245333815553)
          ·
            refine ⟨2244500130343684000361665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992666840458245333815553 2244500130343684000361665)
            ·
              refine ⟨1683375097757763000271249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244500130343684000361665 1683375097757763000271249)
              ·
                refine ⟨1262531323318322250203437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683375097757763000271249 1262531323318322250203437)
                ·
                  refine ⟨473449246244370843826289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262531323318322250203437 473449246244370843826289)
                  ·
                    rfl

theorem cell21_2074588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_2074588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074588 prefixEnd_2074588 := by exact prefixLift 2074588
  have htrace : WordTrace (prefixWord ++ tailWord_2074588) baseStart_2074588 baseEnd_2074588 := by
    simpa [prefixWord, tailWord_2074588, baseEnd_2074588] using wordTrace_append hprefix tailTrace_2074588
  have hstable : (prefixWord ++ tailWord_2074588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074588).length < 2 ^ (prefixWord ++ tailWord_2074588).sum := by decide
  have hdescent : baseEnd_2074588 < baseStart_2074588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074593 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2074593 : Nat := 118140960795 + 2074593 * 2 ^ 59
def prefixEnd_2074593 : Nat := 4983230072969 + 3 ^ 40 * 2074593 * 2
def baseEnd_2074593 : Nat := 473450387312491946242945

theorem tailTrace_2074593 : CollatzResearch.WordTrace tailWord_2074593 prefixEnd_2074593 473450387312491946242945 := by
  unfold tailWord_2074593
  simp only [CollatzResearch.WordTrace]
  refine ⟨75666622973111348121268433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50444415315407565414178955 75666622973111348121268433)
  ·
    refine ⟨56749967229833511090951325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75666622973111348121268433 56749967229833511090951325)
    ·
      refine ⟨21281237711187566659106747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56749967229833511090951325 21281237711187566659106747)
      ·
        refine ⟨31921856566781349988660121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21281237711187566659106747 31921856566781349988660121)
        ·
          refine ⟨23941392425086012491495091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31921856566781349988660121 23941392425086012491495091)
          ·
            refine ⟨35912088637629018737242637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23941392425086012491495091 35912088637629018737242637)
            ·
              refine ⟨13467033239110882026465989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35912088637629018737242637 13467033239110882026465989)
              ·
                refine ⟨2525068732333290379962373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13467033239110882026465989 2525068732333290379962373)
                ·
                  refine ⟨473450387312491946242945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525068732333290379962373 473450387312491946242945)
                  ·
                    rfl

theorem cell21_2074593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2074593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074593 prefixEnd_2074593 := by exact prefixLift 2074593
  have htrace : WordTrace (prefixWord ++ tailWord_2074593) baseStart_2074593 baseEnd_2074593 := by
    simpa [prefixWord, tailWord_2074593, baseEnd_2074593] using wordTrace_append hprefix tailTrace_2074593
  have hstable : (prefixWord ++ tailWord_2074593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074593).length < 2 ^ (prefixWord ++ tailWord_2074593).sum := by decide
  have hdescent : baseEnd_2074593 < baseStart_2074593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074638 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2074638 : Nat := 118140960795 + 2074638 * 2 ^ 59
def prefixEnd_2074638 : Nat := 4983230072969 + 3 ^ 40 * 2074638 * 2
def baseEnd_2074638 : Nat := 473460656925581867992853

theorem tailTrace_2074638 : CollatzResearch.WordTrace tailWord_2074638 prefixEnd_2074638 473460656925581867992853 := by
  unfold tailWord_2074638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458533032243540100832071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50445509505298880537771045 9458533032243540100832071)
  ·
    refine ⟨14187799548365310151248107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9458533032243540100832071 14187799548365310151248107)
    ·
      refine ⟨21281699322547965226872161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14187799548365310151248107 21281699322547965226872161)
      ·
        refine ⟨15961274491910973920154121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21281699322547965226872161 15961274491910973920154121)
        ·
          refine ⟨11970955868933230440115591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15961274491910973920154121 11970955868933230440115591)
          ·
            refine ⟨17956433803399845660173387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970955868933230440115591 17956433803399845660173387)
            ·
              refine ⟨26934650705099768490260081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17956433803399845660173387 26934650705099768490260081)
              ·
                refine ⟨20200988028824826367695061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26934650705099768490260081 20200988028824826367695061)
                ·
                  refine ⟨473460656925581867992853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20200988028824826367695061 473460656925581867992853)
                  ·
                    rfl

theorem cell21_2074638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2074638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074638 prefixEnd_2074638 := by exact prefixLift 2074638
  have htrace : WordTrace (prefixWord ++ tailWord_2074638) baseStart_2074638 baseEnd_2074638 := by
    simpa [prefixWord, tailWord_2074638, baseEnd_2074638] using wordTrace_append hprefix tailTrace_2074638
  have hstable : (prefixWord ++ tailWord_2074638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074638).length < 2 ^ (prefixWord ++ tailWord_2074638).sum := by decide
  have hdescent : baseEnd_2074638 < baseStart_2074638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074655 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 3]
def baseStart_2074655 : Nat := 118140960795 + 2074655 * 2 ^ 59
def prefixEnd_2074655 : Nat := 4983230072969 + 3 ^ 40 * 2074655 * 2
def baseEnd_2074655 : Nat := 473464536557193616209485

theorem tailTrace_2074655 : CollatzResearch.WordTrace tailWord_2074655 prefixEnd_2074655 473464536557193616209485 := by
  unfold tailWord_2074655
  simp only [CollatzResearch.WordTrace]
  refine ⟨75668884298886732710025419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50445922865924488473350279 75668884298886732710025419)
  ·
    refine ⟨113503326448330099065038129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75668884298886732710025419 113503326448330099065038129)
    ·
      refine ⟨85127494836247574298778597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113503326448330099065038129 85127494836247574298778597)
      ·
        refine ⟨15961405281796420181020987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85127494836247574298778597 15961405281796420181020987)
        ·
          refine ⟨23942107922694630271531481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961405281796420181020987 23942107922694630271531481)
          ·
            refine ⟨17956580942020972703648611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23942107922694630271531481 17956580942020972703648611)
            ·
              refine ⟨26934871413031459055472917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17956580942020972703648611 26934871413031459055472917)
              ·
                refine ⟨1262572097485849643225293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26934871413031459055472917 1262572097485849643225293)
                ·
                  refine ⟨473464536557193616209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262572097485849643225293 473464536557193616209485)
                  ·
                    rfl

theorem cell21_2074655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].length) (baseStart_2074655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074655 prefixEnd_2074655 := by exact prefixLift 2074655
  have htrace : WordTrace (prefixWord ++ tailWord_2074655) baseStart_2074655 baseEnd_2074655 := by
    simpa [prefixWord, tailWord_2074655, baseEnd_2074655] using wordTrace_append hprefix tailTrace_2074655
  have hstable : (prefixWord ++ tailWord_2074655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074655).length < 2 ^ (prefixWord ++ tailWord_2074655).sum := by decide
  have hdescent : baseEnd_2074655 < baseStart_2074655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074689 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 3]
def baseStart_2074689 : Nat := 118140960795 + 2074689 * 2 ^ 59
def prefixEnd_2074689 : Nat := 4983230072969 + 3 ^ 40 * 2074689 * 2
def baseEnd_2074689 : Nat := 473472295820417112642749

theorem tailTrace_2074689 : CollatzResearch.WordTrace tailWord_2074689 prefixEnd_2074689 473472295820417112642749 := by
  unfold tailWord_2074689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75670124380763556516763121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50446749587175704344508747 75670124380763556516763121)
  ·
    refine ⟨56752593285572667387572341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75670124380763556516763121 56752593285572667387572341)
    ·
      refine ⟨5320555620522437567584907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56752593285572667387572341 5320555620522437567584907)
      ·
        refine ⟨7980833430783656351377361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320555620522437567584907 7980833430783656351377361)
        ·
          refine ⟨5985625073087742263533021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980833430783656351377361 5985625073087742263533021)
          ·
            refine ⟨2244609402407903348824883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5985625073087742263533021 2244609402407903348824883)
            ·
              refine ⟨3366914103611855023237325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244609402407903348824883 3366914103611855023237325)
              ·
                refine ⟨1262592788854445633713997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3366914103611855023237325 1262592788854445633713997)
                ·
                  refine ⟨473472295820417112642749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262592788854445633713997 473472295820417112642749)
                  ·
                    rfl

theorem cell21_2074689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_2074689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074689 prefixEnd_2074689 := by exact prefixLift 2074689
  have htrace : WordTrace (prefixWord ++ tailWord_2074689) baseStart_2074689 baseEnd_2074689 := by
    simpa [prefixWord, tailWord_2074689, baseEnd_2074689] using wordTrace_append hprefix tailTrace_2074689
  have hstable : (prefixWord ++ tailWord_2074689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074689).length < 2 ^ (prefixWord ++ tailWord_2074689).sum := by decide
  have hdescent : baseEnd_2074689 < baseStart_2074689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074717 : List Nat := [1, 4, 4, 1, 1, 2, 2, 6]
def baseStart_2074717 : Nat := 118140960795 + 2074717 * 2 ^ 59
def prefixEnd_2074717 : Nat := 4983230072969 + 3 ^ 40 * 2074717 * 2
def baseEnd_2074717 : Nat := 157826228600631762058675

theorem tailTrace_2074717 : CollatzResearch.WordTrace tailWord_2074717 prefixEnd_2074717 157826228600631762058675 := by
  unfold tailWord_2074717
  simp only [CollatzResearch.WordTrace]
  refine ⟨75671145624662117298782405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50447430416441411532521603 75671145624662117298782405)
  ·
    refine ⟨14188339804624146993521701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75671145624662117298782405 14188339804624146993521701)
    ·
      refine ⟨2660313713367027561285319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14188339804624146993521701 2660313713367027561285319)
      ·
        refine ⟨3990470570050541341927979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660313713367027561285319 3990470570050541341927979)
        ·
          refine ⟨5985705855075812012891969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990470570050541341927979 5985705855075812012891969)
          ·
            refine ⟨4489279391306859009668977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5985705855075812012891969 4489279391306859009668977)
            ·
              refine ⟨3366959543480144257251733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489279391306859009668977 3366959543480144257251733)
              ·
                refine ⟨157826228600631762058675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3366959543480144257251733 157826228600631762058675)
                ·
                  rfl

theorem cell21_2074717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_2074717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074717 prefixEnd_2074717 := by exact prefixLift 2074717
  have htrace : WordTrace (prefixWord ++ tailWord_2074717) baseStart_2074717 baseEnd_2074717 := by
    simpa [prefixWord, tailWord_2074717, baseEnd_2074717] using wordTrace_append hprefix tailTrace_2074717
  have hstable : (prefixWord ++ tailWord_2074717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074717).length < 2 ^ (prefixWord ++ tailWord_2074717).sum := by decide
  have hdescent : baseEnd_2074717 < baseStart_2074717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074762 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_2074762 : Nat := 118140960795 + 2074762 * 2 ^ 59
def prefixEnd_2074762 : Nat := 4983230072969 + 3 ^ 40 * 2074762 * 2
def baseEnd_2074762 : Nat := 473488955414985207925933

theorem tailTrace_2074762 : CollatzResearch.WordTrace tailWord_2074762 prefixEnd_2074762 473488955414985207925933 := by
  unfold tailWord_2074762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918196727374772496042635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50448524606332726656113693 18918196727374772496042635)
  ·
    refine ⟨28377295091062158744063953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918196727374772496042635 28377295091062158744063953)
    ·
      refine ⟨21282971318296619058047965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28377295091062158744063953 21282971318296619058047965)
      ·
        refine ⟨7981114244361232146767987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21282971318296619058047965 7981114244361232146767987)
        ·
          refine ⟨11971671366541848220151981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981114244361232146767987 11971671366541848220151981)
          ·
            refine ⟨4489376762453193082556993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11971671366541848220151981 4489376762453193082556993)
            ·
              refine ⟨3367032571839894811917745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489376762453193082556993 3367032571839894811917745)
              ·
                refine ⟨2525274428879921108938309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367032571839894811917745 2525274428879921108938309)
                ·
                  refine ⟨473488955414985207925933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525274428879921108938309 473488955414985207925933)
                  ·
                    rfl

theorem cell21_2074762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_2074762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074762 prefixEnd_2074762 := by exact prefixLift 2074762
  have htrace : WordTrace (prefixWord ++ tailWord_2074762) baseStart_2074762 baseEnd_2074762 := by
    simpa [prefixWord, tailWord_2074762, baseEnd_2074762] using wordTrace_append hprefix tailTrace_2074762
  have hstable : (prefixWord ++ tailWord_2074762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074762).length < 2 ^ (prefixWord ++ tailWord_2074762).sum := by decide
  have hdescent : baseEnd_2074762 < baseStart_2074762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074807 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 3]
def baseStart_2074807 : Nat := 118140960795 + 2074807 * 2 ^ 59
def prefixEnd_2074807 : Nat := 4983230072969 + 3 ^ 40 * 2074807 * 2
def baseEnd_2074807 : Nat := 473499225028075129675841

theorem tailTrace_2074807 : CollatzResearch.WordTrace tailWord_2074807 prefixEnd_2074807 473499225028075129675841 := by
  unfold tailWord_2074807
  simp only [CollatzResearch.WordTrace]
  refine ⟨75674428194336062669558675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50449618796224041779705783 75674428194336062669558675)
  ·
    refine ⟨113511642291504094004338013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75674428194336062669558675 113511642291504094004338013)
    ·
      refine ⟨42566865859314035251626755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113511642291504094004338013 42566865859314035251626755)
      ·
        refine ⟨63850298788971052877440133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42566865859314035251626755 63850298788971052877440133)
        ·
          refine ⟨11971931022932072414520025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63850298788971052877440133 11971931022932072414520025)
          ·
            refine ⟨8978948267199054310890019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11971931022932072414520025 8978948267199054310890019)
            ·
              refine ⟨13468422400798581466335029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978948267199054310890019 13468422400798581466335029)
              ·
                refine ⟨1262664600074867012468909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13468422400798581466335029 1262664600074867012468909)
                ·
                  refine ⟨473499225028075129675841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262664600074867012468909 473499225028075129675841)
                  ·
                    rfl

theorem cell21_2074807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].length) (baseStart_2074807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074807 prefixEnd_2074807 := by exact prefixLift 2074807
  have htrace : WordTrace (prefixWord ++ tailWord_2074807) baseStart_2074807 baseEnd_2074807 := by
    simpa [prefixWord, tailWord_2074807, baseEnd_2074807] using wordTrace_append hprefix tailTrace_2074807
  have hstable : (prefixWord ++ tailWord_2074807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074807).length < 2 ^ (prefixWord ++ tailWord_2074807).sum := by decide
  have hdescent : baseEnd_2074807 < baseStart_2074807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074821 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2074821 : Nat := 118140960795 + 2074821 * 2 ^ 59
def prefixEnd_2074821 : Nat := 4983230072969 + 3 ^ 40 * 2074821 * 2
def baseEnd_2074821 : Nat := 473502420018814216442479

theorem tailTrace_2074821 : CollatzResearch.WordTrace tailWord_2074821 prefixEnd_2074821 473502420018814216442479 := by
  unfold tailWord_2074821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75674938816285343060568317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50449959210856895373712211 75674938816285343060568317)
  ·
    refine ⟨28378102056107003647713119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75674938816285343060568317 28378102056107003647713119)
    ·
      refine ⟨42567153084160505471569679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28378102056107003647713119 42567153084160505471569679)
      ·
        refine ⟨63850729626240758207354519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42567153084160505471569679 63850729626240758207354519)
        ·
          refine ⟨95776094439361137311031779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63850729626240758207354519 95776094439361137311031779)
          ·
            refine ⟨143664141659041705966547669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95776094439361137311031779 143664141659041705966547669)
            ·
              refine ⟨3367128320133789983590961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143664141659041705966547669 3367128320133789983590961)
              ·
                refine ⟨2525346240100342487693221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367128320133789983590961 2525346240100342487693221)
                ·
                  refine ⟨473502420018814216442479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525346240100342487693221 473502420018814216442479)
                  ·
                    rfl

theorem cell21_2074821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2074821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074821 prefixEnd_2074821 := by exact prefixLift 2074821
  have htrace : WordTrace (prefixWord ++ tailWord_2074821) baseStart_2074821 baseEnd_2074821 := by
    simpa [prefixWord, tailWord_2074821, baseEnd_2074821] using wordTrace_append hprefix tailTrace_2074821
  have hstable : (prefixWord ++ tailWord_2074821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074821).length < 2 ^ (prefixWord ++ tailWord_2074821).sum := by decide
  have hdescent : baseEnd_2074821 < baseStart_2074821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074880 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_2074880 : Nat := 118140960795 + 2074880 * 2 ^ 59
def prefixEnd_2074880 : Nat := 4983230072969 + 3 ^ 40 * 2074880 * 2
def baseEnd_2074880 : Nat := 473515884622643224959025

theorem tailTrace_2074880 : CollatzResearch.WordTrace tailWord_2074880 prefixEnd_2074880 473515884622643224959025 := by
  unfold tailWord_2074880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37838545361535798068483047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50451393815381064091310729 37838545361535798068483047)
  ·
    refine ⟨56757818042303697102724571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37838545361535798068483047 56757818042303697102724571)
    ·
      refine ⟨85136727063455545654086857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56757818042303697102724571 85136727063455545654086857)
      ·
        refine ⟨63852545297591659240565143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85136727063455545654086857 63852545297591659240565143)
        ·
          refine ⟨95778817946387488860847715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63852545297591659240565143 95778817946387488860847715)
          ·
            refine ⟨143668226919581233291271573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95778817946387488860847715 143668226919581233291271573)
            ·
              refine ⟨6734448136855370310528355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143668226919581233291271573 6734448136855370310528355)
              ·
                refine ⟨10101672205283055465792533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734448136855370310528355 10101672205283055465792533)
                ·
                  refine ⟨473515884622643224959025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10101672205283055465792533 473515884622643224959025)
                  ·
                    rfl

theorem cell21_2074880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_2074880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074880 prefixEnd_2074880 := by exact prefixLift 2074880
  have htrace : WordTrace (prefixWord ++ tailWord_2074880) baseStart_2074880 baseEnd_2074880 := by
    simpa [prefixWord, tailWord_2074880, baseEnd_2074880] using wordTrace_append hprefix tailTrace_2074880
  have hstable : (prefixWord ++ tailWord_2074880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074880).length < 2 ^ (prefixWord ++ tailWord_2074880).sum := by decide
  have hdescent : baseEnd_2074880 < baseStart_2074880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074897 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_2074897 : Nat := 118140960795 + 2074897 * 2 ^ 59
def prefixEnd_2074897 : Nat := 4983230072969 + 3 ^ 40 * 2074897 * 2
def baseEnd_2074897 : Nat := 473519764254254973175657

theorem tailTrace_2074897 : CollatzResearch.WordTrace tailWord_2074897 prefixEnd_2074897 473519764254254973175657 := by
  unfold tailWord_2074897
  simp only [CollatzResearch.WordTrace]
  refine ⟨75677710764010008040334945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50451807176006672026889963 75677710764010008040334945)
  ·
    refine ⟨56758283073007506030251209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75677710764010008040334945 56758283073007506030251209)
    ·
      refine ⟨42568712304755629522688407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56758283073007506030251209 42568712304755629522688407)
      ·
        refine ⟨63853068457133444284032611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42568712304755629522688407 63853068457133444284032611)
        ·
          refine ⟨95779602685700166426048917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63853068457133444284032611 95779602685700166426048917)
          ·
            refine ⟨4489668875892195301221043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95779602685700166426048917 4489668875892195301221043)
            ·
              refine ⟨6734503313838292951831565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489668875892195301221043 6734503313838292951831565)
              ·
                refine ⟨2525438742689359856936837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734503313838292951831565 2525438742689359856936837)
                ·
                  refine ⟨473519764254254973175657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525438742689359856936837 473519764254254973175657)
                  ·
                    rfl

theorem cell21_2074897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_2074897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074897 prefixEnd_2074897 := by exact prefixLift 2074897
  have htrace : WordTrace (prefixWord ++ tailWord_2074897) baseStart_2074897 baseEnd_2074897 := by
    simpa [prefixWord, tailWord_2074897, baseEnd_2074897] using wordTrace_append hprefix tailTrace_2074897
  have hstable : (prefixWord ++ tailWord_2074897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074897).length < 2 ^ (prefixWord ++ tailWord_2074897).sum := by decide
  have hdescent : baseEnd_2074897 < baseStart_2074897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074911 : List Nat := [1, 1, 2, 4, 3, 1, 2, 7]
def baseStart_2074911 : Nat := 118140960795 + 2074911 * 2 ^ 59
def prefixEnd_2074911 : Nat := 4983230072969 + 3 ^ 40 * 2074911 * 2
def baseEnd_2074911 : Nat := 157840986414998019980765

theorem tailTrace_2074911 : CollatzResearch.WordTrace tailWord_2074911 prefixEnd_2074911 157840986414998019980765 := by
  unfold tailWord_2074911
  simp only [CollatzResearch.WordTrace]
  refine ⟨75678221385959288431344587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50452147590639525620896391 75678221385959288431344587)
  ·
    refine ⟨113517332078938932647016881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75678221385959288431344587 113517332078938932647016881)
    ·
      refine ⟨85137999059204199485262661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113517332078938932647016881 85137999059204199485262661)
      ·
        refine ⟨15963374823600787403486749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85137999059204199485262661 15963374823600787403486749)
        ·
          refine ⟨5986265558850295276307531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15963374823600787403486749 5986265558850295276307531)
          ·
            refine ⟨8979398338275442914461297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986265558850295276307531 8979398338275442914461297)
            ·
              refine ⟨6734548753706582185845973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979398338275442914461297 6734548753706582185845973)
              ·
                refine ⟨157840986414998019980765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6734548753706582185845973 157840986414998019980765)
                ·
                  rfl

theorem cell21_2074911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_2074911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074911 prefixEnd_2074911 := by exact prefixLift 2074911
  have htrace : WordTrace (prefixWord ++ tailWord_2074911) baseStart_2074911 baseEnd_2074911 := by
    simpa [prefixWord, tailWord_2074911, baseEnd_2074911] using wordTrace_append hprefix tailTrace_2074911
  have hstable : (prefixWord ++ tailWord_2074911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074911).length < 2 ^ (prefixWord ++ tailWord_2074911).sum := by decide
  have hdescent : baseEnd_2074911 < baseStart_2074911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074945 : List Nat := [1, 2, 5, 2, 2, 2, 1, 6]
def baseStart_2074945 : Nat := 118140960795 + 2074945 * 2 ^ 59
def prefixEnd_2074945 : Nat := 4983230072969 + 3 ^ 40 * 2074945 * 2
def baseEnd_2074945 : Nat := 157843572836072518791853

theorem tailTrace_2074945 : CollatzResearch.WordTrace tailWord_2074945 prefixEnd_2074945 157843572836072518791853 := by
  unfold tailWord_2074945
  simp only [CollatzResearch.WordTrace]
  refine ⟨75679461467836112238082289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50452974311890741492054859 75679461467836112238082289)
  ·
    refine ⟨56759596100877084178561717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75679461467836112238082289 56759596100877084178561717)
    ·
      refine ⟨5321212134457226641740161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56759596100877084178561717 5321212134457226641740161)
      ·
        refine ⟨3990909100842919981305121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5321212134457226641740161 3990909100842919981305121)
        ·
          refine ⟨2993181825632189985978841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990909100842919981305121 2993181825632189985978841)
          ·
            refine ⟨2244886369224142489484131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993181825632189985978841 2244886369224142489484131)
            ·
              refine ⟨3367329553836213734226197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244886369224142489484131 3367329553836213734226197)
              ·
                refine ⟨157843572836072518791853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367329553836213734226197 157843572836072518791853)
                ·
                  rfl

theorem cell21_2074945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_2074945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074945 prefixEnd_2074945 := by exact prefixLift 2074945
  have htrace : WordTrace (prefixWord ++ tailWord_2074945) baseStart_2074945 baseEnd_2074945 := by
    simpa [prefixWord, tailWord_2074945, baseEnd_2074945] using wordTrace_append hprefix tailTrace_2074945
  have hstable : (prefixWord ++ tailWord_2074945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074945).length < 2 ^ (prefixWord ++ tailWord_2074945).sum := by decide
  have hdescent : baseEnd_2074945 < baseStart_2074945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074976 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_2074976 : Nat := 118140960795 + 2074976 * 2 ^ 59
def prefixEnd_2074976 : Nat := 4983230072969 + 3 ^ 40 * 2074976 * 2
def baseEnd_2074976 : Nat := 473537793130568391358829

theorem tailTrace_2074976 : CollatzResearch.WordTrace tailWord_2074976 prefixEnd_2074976 473537793130568391358829 := by
  unfold tailWord_2074976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37840296065361902266230391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50453728087149203021640521 37840296065361902266230391)
  ·
    refine ⟨56760444098042853399345587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37840296065361902266230391 56760444098042853399345587)
    ·
      refine ⟨85140666147064280099018381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56760444098042853399345587 85140666147064280099018381)
      ·
        refine ⟨31927749805149105037131893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85140666147064280099018381 31927749805149105037131893)
        ·
          refine ⟨2993226544232728597231115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31927749805149105037131893 2993226544232728597231115)
          ·
            refine ⟨4489839816349092895846673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993226544232728597231115 4489839816349092895846673)
            ·
              refine ⟨3367379862261819671885005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489839816349092895846673 3367379862261819671885005)
              ·
                refine ⟨1262767448348182376956877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3367379862261819671885005 1262767448348182376956877)
                ·
                  refine ⟨473537793130568391358829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262767448348182376956877 473537793130568391358829)
                  ·
                    rfl

theorem cell21_2074976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_2074976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2074976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2074976 prefixEnd_2074976 := by exact prefixLift 2074976
  have htrace : WordTrace (prefixWord ++ tailWord_2074976) baseStart_2074976 baseEnd_2074976 := by
    simpa [prefixWord, tailWord_2074976, baseEnd_2074976] using wordTrace_append hprefix tailTrace_2074976
  have hstable : (prefixWord ++ tailWord_2074976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074976).length < 2 ^ (prefixWord ++ tailWord_2074976).sum := by decide
  have hdescent : baseEnd_2074976 < baseStart_2074976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075063 : List Nat := [1, 1, 3, 1, 3, 4, 2, 6]
def baseStart_2075063 : Nat := 118140960795 + 2075063 * 2 ^ 59
def prefixEnd_2075063 : Nat := 4983230072969 + 3 ^ 40 * 2075063 * 2
def baseEnd_2075063 : Nat := 157852549238625191136217

theorem tailTrace_2075063 : CollatzResearch.WordTrace tailWord_2075063 prefixEnd_2075063 157852549238625191136217 := by
  unfold tailWord_2075063
  simp only [CollatzResearch.WordTrace]
  refine ⟨75683765281408618390877843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50455843520939078927251895 75683765281408618390877843)
  ·
    refine ⟨113525647922112927586316765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75683765281408618390877843 113525647922112927586316765)
    ·
      refine ⟨42572117970792347844868787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113525647922112927586316765 42572117970792347844868787)
      ·
        refine ⟨63858176956188521767303181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42572117970792347844868787 63858176956188521767303181)
        ·
          refine ⟨23946816358570695662738693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63858176956188521767303181 23946816358570695662738693)
          ·
            refine ⟨4490028067232005436763505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23946816358570695662738693 4490028067232005436763505)
            ·
              refine ⟨3367521050424004077572629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490028067232005436763505 3367521050424004077572629)
              ·
                refine ⟨157852549238625191136217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367521050424004077572629 157852549238625191136217)
                ·
                  rfl

theorem cell21_2075063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_2075063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075063 prefixEnd_2075063 := by exact prefixLift 2075063
  have htrace : WordTrace (prefixWord ++ tailWord_2075063) baseStart_2075063 baseEnd_2075063 := by
    simpa [prefixWord, tailWord_2075063, baseEnd_2075063] using wordTrace_append hprefix tailTrace_2075063
  have hstable : (prefixWord ++ tailWord_2075063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075063).length < 2 ^ (prefixWord ++ tailWord_2075063).sum := by decide
  have hdescent : baseEnd_2075063 < baseStart_2075063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075111 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 3]
def baseStart_2075111 : Nat := 118140960795 + 2075111 * 2 ^ 59
def prefixEnd_2075111 : Nat := 4983230072969 + 3 ^ 40 * 2075111 * 2
def baseEnd_2075111 : Nat := 473568601969838156608553

theorem tailTrace_2075111 : CollatzResearch.WordTrace tailWord_2075111 prefixEnd_2075111 473568601969838156608553 := by
  unfold tailWord_2075111
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685515985234722588625187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457010656823148392416791 75685515985234722588625187)
  ·
    refine ⟨113528273977852083882937781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75685515985234722588625187 113528273977852083882937781)
    ·
      refine ⟨10643275685423632864025417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113528273977852083882937781 10643275685423632864025417)
      ·
        refine ⟨7982456764067724648019063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10643275685423632864025417 7982456764067724648019063)
        ·
          refine ⟨11973685146101586972028595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982456764067724648019063 11973685146101586972028595)
          ·
            refine ⟨17960527719152380458042893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973685146101586972028595 17960527719152380458042893)
            ·
              refine ⟨6735197894682142671766085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17960527719152380458042893 6735197894682142671766085)
              ·
                refine ⟨1262849605252901750956141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6735197894682142671766085 1262849605252901750956141)
                ·
                  refine ⟨473568601969838156608553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262849605252901750956141 473568601969838156608553)
                  ·
                    rfl

theorem cell21_2075111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].length) (baseStart_2075111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075111 prefixEnd_2075111 := by exact prefixLift 2075111
  have htrace : WordTrace (prefixWord ++ tailWord_2075111) baseStart_2075111 baseEnd_2075111 := by
    simpa [prefixWord, tailWord_2075111, baseEnd_2075111] using wordTrace_append hprefix tailTrace_2075111
  have hstable : (prefixWord ++ tailWord_2075111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075111).length < 2 ^ (prefixWord ++ tailWord_2075111).sum := by decide
  have hdescent : baseEnd_2075111 < baseStart_2075111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075139 : List Nat := [1, 1, 1, 3, 2, 1, 7, 5]
def baseStart_2075139 : Nat := 118140960795 + 2075139 * 2 ^ 59
def prefixEnd_2075139 : Nat := 4983230072969 + 3 ^ 40 * 2075139 * 2
def baseEnd_2075139 : Nat := 157858330650438776713943

theorem tailTrace_2075139 : CollatzResearch.WordTrace tailWord_2075139 prefixEnd_2075139 157858330650438776713943 := by
  unfold tailWord_2075139
  simp only [CollatzResearch.WordTrace]
  refine ⟨75686537229133283370644471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457691486088855580429647 75686537229133283370644471)
  ·
    refine ⟨113529805843699925055966707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75686537229133283370644471 113529805843699925055966707)
    ·
      refine ⟨170294708765549887583950061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113529805843699925055966707 170294708765549887583950061)
      ·
        refine ⟨63860515787081207843981273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170294708765549887583950061 63860515787081207843981273)
        ·
          refine ⟨47895386840310905882985955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63860515787081207843981273 47895386840310905882985955)
          ·
            refine ⟨71843080260466358824478933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47895386840310905882985955 71843080260466358824478933)
            ·
              refine ⟨1683822193604680284948725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71843080260466358824478933 1683822193604680284948725)
              ·
                refine ⟨157858330650438776713943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1683822193604680284948725 157858330650438776713943)
                ·
                  rfl

theorem cell21_2075139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].length) (baseStart_2075139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075139 prefixEnd_2075139 := by exact prefixLift 2075139
  have htrace : WordTrace (prefixWord ++ tailWord_2075139) baseStart_2075139 baseEnd_2075139 := by
    simpa [prefixWord, tailWord_2075139, baseEnd_2075139] using wordTrace_append hprefix tailTrace_2075139
  have hstable : (prefixWord ++ tailWord_2075139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075139).length < 2 ^ (prefixWord ++ tailWord_2075139).sum := by decide
  have hdescent : baseEnd_2075139 < baseStart_2075139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075156 : List Nat := [2, 4, 3, 1, 1, 2, 8]
def baseStart_2075156 : Nat := 118140960795 + 2075156 * 2 ^ 59
def prefixEnd_2075156 : Nat := 4983230072969 + 3 ^ 40 * 2075156 * 2
def baseEnd_2075156 : Nat := 52619874620325342039829

theorem tailTrace_2075156 : CollatzResearch.WordTrace tailWord_2075156 prefixEnd_2075156 52619874620325342039829 := by
  unfold tailWord_2075156
  simp only [CollatzResearch.WordTrace]
  refine ⟨37843578635035847637006661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50458104846714463516008881 37843578635035847637006661)
  ·
    refine ⟨7095670994069221431938749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37843578635035847637006661 7095670994069221431938749)
    ·
      refine ⟨2660876622775958036977031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7095670994069221431938749 2660876622775958036977031)
      ·
        refine ⟨3991314934163937055465547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660876622775958036977031 3991314934163937055465547)
        ·
          refine ⟨5986972401245905583198321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991314934163937055465547 5986972401245905583198321)
          ·
            refine ⟨4490229300934429187398741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986972401245905583198321 4490229300934429187398741)
            ·
              refine ⟨52619874620325342039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4490229300934429187398741 52619874620325342039829)
              ·
                rfl

theorem cell21_2075156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 8].length) (baseStart_2075156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075156 prefixEnd_2075156 := by exact prefixLift 2075156
  have htrace : WordTrace (prefixWord ++ tailWord_2075156) baseStart_2075156 baseEnd_2075156 := by
    simpa [prefixWord, tailWord_2075156, baseEnd_2075156] using wordTrace_append hprefix tailTrace_2075156
  have hstable : (prefixWord ++ tailWord_2075156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075156).length < 2 ^ (prefixWord ++ tailWord_2075156).sum := by decide
  have hdescent : baseEnd_2075156 < baseStart_2075156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075159 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_2075159 : Nat := 118140960795 + 2075159 * 2 ^ 59
def prefixEnd_2075159 : Nat := 4983230072969 + 3 ^ 40 * 2075159 * 2
def baseEnd_2075159 : Nat := 473579556223800739808455

theorem tailTrace_2075159 : CollatzResearch.WordTrace tailWord_2075159 prefixEnd_2075159 473579556223800739808455 := by
  unfold tailWord_2075159
  simp only [CollatzResearch.WordTrace]
  refine ⟨75687266689060826786372531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50458177792707217857581687 75687266689060826786372531)
  ·
    refine ⟨113530900033591240179558797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75687266689060826786372531 113530900033591240179558797)
    ·
      refine ⟨42574087512596715067334549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113530900033591240179558797 42574087512596715067334549)
      ·
        refine ⟨1995660352152971018781307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42574087512596715067334549 1995660352152971018781307)
        ·
          refine ⟨2993490528229456528171961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995660352152971018781307 2993490528229456528171961)
          ·
            refine ⟨2245117896172092396128971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993490528229456528171961 2245117896172092396128971)
            ·
              refine ⟨3367676844258138594193457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245117896172092396128971 3367676844258138594193457)
              ·
                refine ⟨2525757633193603945645093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367676844258138594193457 2525757633193603945645093)
                ·
                  refine ⟨473579556223800739808455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525757633193603945645093 473579556223800739808455)
                  ·
                    rfl

theorem cell21_2075159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_2075159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075159 prefixEnd_2075159 := by exact prefixLift 2075159
  have htrace : WordTrace (prefixWord ++ tailWord_2075159) baseStart_2075159 baseEnd_2075159 := by
    simpa [prefixWord, tailWord_2075159, baseEnd_2075159] using wordTrace_append hprefix tailTrace_2075159
  have hstable : (prefixWord ++ tailWord_2075159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075159).length < 2 ^ (prefixWord ++ tailWord_2075159).sum := by decide
  have hdescent : baseEnd_2075159 < baseStart_2075159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075184 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_2075184 : Nat := 118140960795 + 2075184 * 2 ^ 59
def prefixEnd_2075184 : Nat := 4983230072969 + 3 ^ 40 * 2075184 * 2
def baseEnd_2075184 : Nat := 473585261564406251891737

theorem tailTrace_2075184 : CollatzResearch.WordTrace tailWord_2075184 prefixEnd_2075184 473585261564406251891737 := by
  unfold tailWord_2075184
  simp only [CollatzResearch.WordTrace]
  refine ⟨37844089256985128028016303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50458785675980170704021737 37844089256985128028016303)
  ·
    refine ⟨56766133885477692042024455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37844089256985128028016303 56766133885477692042024455)
    ·
      refine ⟨85149200828216538063036683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56766133885477692042024455 85149200828216538063036683)
      ·
        refine ⟨127723801242324807094555025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85149200828216538063036683 127723801242324807094555025)
        ·
          refine ⟨95792850931743605320916269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127723801242324807094555025 95792850931743605320916269)
          ·
            refine ⟨35922319099403851995343601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95792850931743605320916269 35922319099403851995343601)
            ·
              refine ⟨26941739324552888996507701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35922319099403851995343601 26941739324552888996507701)
              ·
                refine ⟨2525788061676833343422597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26941739324552888996507701 2525788061676833343422597)
                ·
                  refine ⟨473585261564406251891737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525788061676833343422597 473585261564406251891737)
                  ·
                    rfl

theorem cell21_2075184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_2075184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075184 prefixEnd_2075184 := by exact prefixLift 2075184
  have htrace : WordTrace (prefixWord ++ tailWord_2075184) baseStart_2075184 baseEnd_2075184 := by
    simpa [prefixWord, tailWord_2075184, baseEnd_2075184] using wordTrace_append hprefix tailTrace_2075184
  have hstable : (prefixWord ++ tailWord_2075184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075184).length < 2 ^ (prefixWord ++ tailWord_2075184).sum := by decide
  have hdescent : baseEnd_2075184 < baseStart_2075184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075243 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_2075243 : Nat := 118140960795 + 2075243 * 2 ^ 59
def prefixEnd_2075243 : Nat := 4983230072969 + 3 ^ 40 * 2075243 * 2
def baseEnd_2075243 : Nat := 473598726168235260408283

theorem tailTrace_2075243 : CollatzResearch.WordTrace tailWord_2075243 prefixEnd_2075243 473598726168235260408283 := by
  unfold tailWord_2075243
  simp only [CollatzResearch.WordTrace]
  refine ⟨75690330420756509132430383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50460220280504339421620255 75690330420756509132430383)
  ·
    refine ⟨113535495631134763698645575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75690330420756509132430383 113535495631134763698645575)
    ·
      refine ⟨170303243446702145547968363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113535495631134763698645575 170303243446702145547968363)
      ·
        refine ⟨255454865170053218321952545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170303243446702145547968363 255454865170053218321952545)
        ·
          refine ⟨191591148877539913741464409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255454865170053218321952545 191591148877539913741464409)
          ·
            refine ⟨143693361658154935306098307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191591148877539913741464409 143693361658154935306098307)
            ·
              refine ⟨215540042487232402959147461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143693361658154935306098307 215540042487232402959147461)
              ·
                refine ⟨40413757966356075554840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215540042487232402959147461 40413757966356075554840149)
                ·
                  refine ⟨473598726168235260408283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40413757966356075554840149 473598726168235260408283)
                  ·
                    rfl

theorem cell21_2075243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_2075243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075243 prefixEnd_2075243 := by exact prefixLift 2075243
  have htrace : WordTrace (prefixWord ++ tailWord_2075243) baseStart_2075243 baseEnd_2075243 := by
    simpa [prefixWord, tailWord_2075243, baseEnd_2075243] using wordTrace_append hprefix tailTrace_2075243
  have hstable : (prefixWord ++ tailWord_2075243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075243).length < 2 ^ (prefixWord ++ tailWord_2075243).sum := by decide
  have hdescent : baseEnd_2075243 < baseStart_2075243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075266 : List Nat := [3, 4, 3, 1, 2, 8]
def baseStart_2075266 : Nat := 118140960795 + 2075266 * 2 ^ 59
def prefixEnd_2075266 : Nat := 4983230072969 + 3 ^ 40 * 2075266 * 2
def baseEnd_2075266 : Nat := 17540887965984901167589

theorem tailTrace_2075266 : CollatzResearch.WordTrace tailWord_2075266 prefixEnd_2075266 17540887965984901167589 := by
  unfold tailWord_2075266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922792324918296015129413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50460779533115456040345101 18922792324918296015129413)
  ·
    refine ⟨3548023560922180502836765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18922792324918296015129413 3548023560922180502836765)
    ·
      refine ⟨1330508835345817688563787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3548023560922180502836765 1330508835345817688563787)
      ·
        refine ⟨1995763253018726532845681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330508835345817688563787 1995763253018726532845681)
        ·
          refine ⟨1496822439764044899634261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1995763253018726532845681 1496822439764044899634261)
          ·
            refine ⟨17540887965984901167589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1496822439764044899634261 17540887965984901167589)
            ·
              rfl

theorem cell21_2075266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 8].length) (baseStart_2075266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075266 prefixEnd_2075266 := by exact prefixLift 2075266
  have htrace : WordTrace (prefixWord ++ tailWord_2075266) baseStart_2075266 baseEnd_2075266 := by
    simpa [prefixWord, tailWord_2075266, baseEnd_2075266] using wordTrace_append hprefix tailTrace_2075266
  have hstable : (prefixWord ++ tailWord_2075266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075266).length < 2 ^ (prefixWord ++ tailWord_2075266).sum := by decide
  have hdescent : baseEnd_2075266 < baseStart_2075266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075274 : List Nat := [3, 1, 2, 3, 12]
def baseStart_2075274 : Nat := 118140960795 + 2075274 * 2 ^ 59
def prefixEnd_2075274 : Nat := 4983230072969 + 3 ^ 40 * 2075274 * 2
def baseEnd_2075274 : Nat := 5846985194945507350513

theorem tailTrace_2075274 : CollatzResearch.WordTrace tailWord_2075274 prefixEnd_2075274 5846985194945507350513 := by
  unfold tailWord_2075274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922865270911050356702219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50460974055762800951205917 18922865270911050356702219)
  ·
    refine ⟨28384297906366575535053329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922865270911050356702219 28384297906366575535053329)
    ·
      refine ⟨21288223429774931651289997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28384297906366575535053329 21288223429774931651289997)
      ·
        refine ⟨7983083786165599369233749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21288223429774931651289997 7983083786165599369233749)
        ·
          refine ⟨5846985194945507350513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7983083786165599369233749 5846985194945507350513)
          ·
            rfl

theorem cell21_2075274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 12].length) (baseStart_2075274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075274 prefixEnd_2075274 := by exact prefixLift 2075274
  have htrace : WordTrace (prefixWord ++ tailWord_2075274) baseStart_2075274 baseEnd_2075274 := by
    simpa [prefixWord, tailWord_2075274, baseEnd_2075274] using wordTrace_append hprefix tailTrace_2075274
  have hstable : (prefixWord ++ tailWord_2075274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075274).length < 2 ^ (prefixWord ++ tailWord_2075274).sum := by decide
  have hdescent : baseEnd_2075274 < baseStart_2075274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075336 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_2075336 : Nat := 118140960795 + 2075336 * 2 ^ 59
def prefixEnd_2075336 : Nat := 4983230072969 + 3 ^ 40 * 2075336 * 2
def baseEnd_2075336 : Nat := 473619950035287765358093

theorem tailTrace_2075336 : CollatzResearch.WordTrace tailWord_2075336 prefixEnd_2075336 473619950035287765358093 := by
  unfold tailWord_2075336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37846861204709793007782931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50462481606279724010377241 37846861204709793007782931)
  ·
    refine ⟨56770291807064689511674397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37846861204709793007782931 56770291807064689511674397)
    ·
      refine ⟨21288859427649258566877899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56770291807064689511674397 21288859427649258566877899)
      ·
        refine ⟨31933289141473887850316849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21288859427649258566877899 31933289141473887850316849)
        ·
          refine ⟨23949966856105415887737637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31933289141473887850316849 23949966856105415887737637)
          ·
            refine ⟨4490618785519765478950807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23949966856105415887737637 4490618785519765478950807)
            ·
              refine ⟨6735928178279648218426211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490618785519765478950807 6735928178279648218426211)
              ·
                refine ⟨10103892267419472327639317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735928178279648218426211 10103892267419472327639317)
                ·
                  refine ⟨473619950035287765358093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10103892267419472327639317 473619950035287765358093)
                  ·
                    rfl

theorem cell21_2075336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_2075336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075336 prefixEnd_2075336 := by exact prefixLift 2075336
  have htrace : WordTrace (prefixWord ++ tailWord_2075336) baseStart_2075336 baseEnd_2075336 := by
    simpa [prefixWord, tailWord_2075336, baseEnd_2075336] using wordTrace_append hprefix tailTrace_2075336
  have hstable : (prefixWord ++ tailWord_2075336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075336).length < 2 ^ (prefixWord ++ tailWord_2075336).sum := by decide
  have hdescent : baseEnd_2075336 < baseStart_2075336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075353 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 4]
def baseStart_2075353 : Nat := 118140960795 + 2075353 * 2 ^ 59
def prefixEnd_2075353 : Nat := 4983230072969 + 3 ^ 40 * 2075353 * 2
def baseEnd_2075353 : Nat := 473623829666899513574725

theorem tailTrace_2075353 : CollatzResearch.WordTrace tailWord_2075353 prefixEnd_2075353 473623829666899513574725 := by
  unfold tailWord_2075353
  simp only [CollatzResearch.WordTrace]
  refine ⟨75694342450357997918934713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50462894966905331945956475 75694342450357997918934713)
  ·
    refine ⟨56770756837768498439201035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75694342450357997918934713 56770756837768498439201035)
    ·
      refine ⟨85156135256652747658801553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56770756837768498439201035 85156135256652747658801553)
      ·
        refine ⟨63867101442489560744101165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85156135256652747658801553 63867101442489560744101165)
        ·
          refine ⟨23950163040933585279037937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63867101442489560744101165 23950163040933585279037937)
          ·
            refine ⟨17962622280700188959278453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23950163040933585279037937 17962622280700188959278453)
            ·
              refine ⟨1683995838815642714932355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17962622280700188959278453 1683995838815642714932355)
              ·
                refine ⟨2525993758223464072398533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683995838815642714932355 2525993758223464072398533)
                ·
                  refine ⟨473623829666899513574725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2525993758223464072398533 473623829666899513574725)
                  ·
                    rfl

theorem cell21_2075353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_2075353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075353 prefixEnd_2075353 := by exact prefixLift 2075353
  have htrace : WordTrace (prefixWord ++ tailWord_2075353) baseStart_2075353 baseEnd_2075353 := by
    simpa [prefixWord, tailWord_2075353, baseEnd_2075353] using wordTrace_append hprefix tailTrace_2075353
  have hstable : (prefixWord ++ tailWord_2075353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075353).length < 2 ^ (prefixWord ++ tailWord_2075353).sum := by decide
  have hdescent : baseEnd_2075353 < baseStart_2075353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075491 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 3]
def baseStart_2075491 : Nat := 118140960795 + 2075491 * 2 ^ 59
def prefixEnd_2075491 : Nat := 4983230072969 + 3 ^ 40 * 2075491 * 2
def baseEnd_2075491 : Nat := 473655323147041940274443

theorem tailTrace_2075491 : CollatzResearch.WordTrace tailWord_2075491 prefixEnd_2075491 473655323147041940274443 := by
  unfold tailWord_2075491
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699375723858047487458327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466250482572031658305551 75699375723858047487458327)
  ·
    refine ⟨113549063585787071231187491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75699375723858047487458327 113549063585787071231187491)
    ·
      refine ⟨170323595378680606846781237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113549063585787071231187491 170323595378680606846781237)
      ·
        refine ⟨15967837066751306891885741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170323595378680606846781237 15967837066751306891885741)
        ·
          refine ⟨5987938900031740084457153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15967837066751306891885741 5987938900031740084457153)
          ·
            refine ⟨4490954175023805063342865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987938900031740084457153 4490954175023805063342865)
            ·
              refine ⟨3368215631267853797507149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490954175023805063342865 3368215631267853797507149)
              ·
                refine ⟨1263080861725445174065181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3368215631267853797507149 1263080861725445174065181)
                ·
                  refine ⟨473655323147041940274443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263080861725445174065181 473655323147041940274443)
                  ·
                    rfl

theorem cell21_2075491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].length) (baseStart_2075491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075491 prefixEnd_2075491 := by exact prefixLift 2075491
  have htrace : WordTrace (prefixWord ++ tailWord_2075491) baseStart_2075491 baseEnd_2075491 := by
    simpa [prefixWord, tailWord_2075491, baseEnd_2075491] using wordTrace_append hprefix tailTrace_2075491
  have hstable : (prefixWord ++ tailWord_2075491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075491).length < 2 ^ (prefixWord ++ tailWord_2075491).sum := by decide
  have hdescent : baseEnd_2075491 < baseStart_2075491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075505 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2075505 : Nat := 118140960795 + 2075505 * 2 ^ 59
def prefixEnd_2075505 : Nat := 4983230072969 + 3 ^ 40 * 2075505 * 2
def baseEnd_2075505 : Nat := 473658518137781027041081

theorem tailTrace_2075505 : CollatzResearch.WordTrace tailWord_2075505 prefixEnd_2075505 473658518137781027041081 := by
  unfold tailWord_2075505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699886345807327878467969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466590897204885252311979 75699886345807327878467969)
  ·
    refine ⟨56774914759355495908850977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75699886345807327878467969 56774914759355495908850977)
    ·
      refine ⟨42581186069516621931638233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56774914759355495908850977 42581186069516621931638233)
      ·
        refine ⟨31935889552137466448728675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42581186069516621931638233 31935889552137466448728675)
        ·
          refine ⟨47903834328206199673093013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31935889552137466448728675 47903834328206199673093013)
          ·
            refine ⟨2245492234134665609676235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47903834328206199673093013 2245492234134665609676235)
            ·
              refine ⟨3368238351201998414514353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245492234134665609676235 3368238351201998414514353)
              ·
                refine ⟨2526178763401498810885765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368238351201998414514353 2526178763401498810885765)
                ·
                  refine ⟨473658518137781027041081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526178763401498810885765 473658518137781027041081)
                  ·
                    rfl

theorem cell21_2075505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2075505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075505 prefixEnd_2075505 := by exact prefixLift 2075505
  have htrace : WordTrace (prefixWord ++ tailWord_2075505) baseStart_2075505 baseEnd_2075505 := by
    simpa [prefixWord, tailWord_2075505, baseEnd_2075505] using wordTrace_append hprefix tailTrace_2075505
  have hstable : (prefixWord ++ tailWord_2075505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075505).length < 2 ^ (prefixWord ++ tailWord_2075505).sum := by decide
  have hdescent : baseEnd_2075505 < baseStart_2075505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075542 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2075542 : Nat := 118140960795 + 2075542 * 2 ^ 59
def prefixEnd_2075542 : Nat := 4983230072969 + 3 ^ 40 * 2075542 * 2
def baseEnd_2075542 : Nat := 473666962041877184924339

theorem tailTrace_2075542 : CollatzResearch.WordTrace tailWord_2075542 prefixEnd_2075542 473666962041877184924339 := by
  unfold tailWord_2075542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731327240417080199847805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50467490564448855465043253 4731327240417080199847805)
  ·
    refine ⟨1774247715156405074942927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4731327240417080199847805 1774247715156405074942927)
    ·
      refine ⟨2661371572734607612414391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774247715156405074942927 2661371572734607612414391)
      ·
        refine ⟨3992057359101911418621587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661371572734607612414391 3992057359101911418621587)
        ·
          refine ⟨5988086038652867127932381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992057359101911418621587 5988086038652867127932381)
          ·
            refine ⟨2245532264494825172974643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5988086038652867127932381 2245532264494825172974643)
            ·
              refine ⟨3368298396742237759461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245532264494825172974643 3368298396742237759461965)
              ·
                refine ⟨1263111898778339159798237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3368298396742237759461965 1263111898778339159798237)
                ·
                  refine ⟨473666962041877184924339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263111898778339159798237 473666962041877184924339)
                  ·
                    rfl

theorem cell21_2075542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2075542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075542 prefixEnd_2075542 := by exact prefixLift 2075542
  have htrace : WordTrace (prefixWord ++ tailWord_2075542) baseStart_2075542 baseEnd_2075542 := by
    simpa [prefixWord, tailWord_2075542, baseEnd_2075542] using wordTrace_append hprefix tailTrace_2075542
  have hstable : (prefixWord ++ tailWord_2075542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075542).length < 2 ^ (prefixWord ++ tailWord_2075542).sum := by decide
  have hdescent : baseEnd_2075542 < baseStart_2075542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075578 : List Nat := [3, 1, 1, 1, 2, 1, 6, 6]
def baseStart_2075578 : Nat := 118140960795 + 2075578 * 2 ^ 59
def prefixEnd_2075578 : Nat := 4983230072969 + 3 ^ 40 * 2075578 * 2
def baseEnd_2075578 : Nat := 157891725910783040774755

theorem tailTrace_2075578 : CollatzResearch.WordTrace tailWord_2075578 prefixEnd_2075578 157891725910783040774755 := by
  unfold tailWord_2075578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925637218635715336468847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50468365916361907563916925 18925637218635715336468847)
  ·
    refine ⟨28388455827953573004703271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18925637218635715336468847 28388455827953573004703271)
    ·
      refine ⟨42582683741930359507054907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28388455827953573004703271 42582683741930359507054907)
      ·
        refine ⟨63874025612895539260582361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42582683741930359507054907 63874025612895539260582361)
        ·
          refine ⟨47905519209671654445436771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63874025612895539260582361 47905519209671654445436771)
          ·
            refine ⟨71858278814507481668155157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47905519209671654445436771 71858278814507481668155157)
            ·
              refine ⟨3368356819430038203194773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71858278814507481668155157 3368356819430038203194773)
              ·
                refine ⟨157891725910783040774755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3368356819430038203194773 157891725910783040774755)
                ·
                  rfl

theorem cell21_2075578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_2075578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075578 prefixEnd_2075578 := by exact prefixLift 2075578
  have htrace : WordTrace (prefixWord ++ tailWord_2075578) baseStart_2075578 baseEnd_2075578 := by
    simpa [prefixWord, tailWord_2075578, baseEnd_2075578] using wordTrace_append hprefix tailTrace_2075578
  have hstable : (prefixWord ++ tailWord_2075578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075578).length < 2 ^ (prefixWord ++ tailWord_2075578).sum := by decide
  have hdescent : baseEnd_2075578 < baseStart_2075578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075581 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2075581 : Nat := 118140960795 + 2075581 * 2 ^ 59
def prefixEnd_2075581 : Nat := 4983230072969 + 3 ^ 40 * 2075581 * 2
def baseEnd_2075581 : Nat := 473675862373221783774259

theorem tailTrace_2075581 : CollatzResearch.WordTrace tailWord_2075581 prefixEnd_2075581 473675862373221783774259 := by
  unfold tailWord_2075581
  simp only [CollatzResearch.WordTrace]
  refine ⟨75702658293531992858234597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50468438862354661905489731 75702658293531992858234597)
  ·
    refine ⟨14194248430037248660918987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75702658293531992858234597 14194248430037248660918987)
    ·
      refine ⟨21291372645055872991378481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14194248430037248660918987 21291372645055872991378481)
      ·
        refine ⟨15968529483791904743533861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291372645055872991378481 15968529483791904743533861)
        ·
          refine ⟨2994099278210982139412599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15968529483791904743533861 2994099278210982139412599)
          ·
            refine ⟨4491148917316473209118899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994099278210982139412599 4491148917316473209118899)
            ·
              refine ⟨6736723375974709813678349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491148917316473209118899 6736723375974709813678349)
              ·
                refine ⟨2526271265990516180129381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6736723375974709813678349 2526271265990516180129381)
                ·
                  refine ⟨473675862373221783774259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526271265990516180129381 473675862373221783774259)
                  ·
                    rfl

theorem cell21_2075581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2075581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075581 prefixEnd_2075581 := by exact prefixLift 2075581
  have htrace : WordTrace (prefixWord ++ tailWord_2075581) baseStart_2075581 baseEnd_2075581 := by
    simpa [prefixWord, tailWord_2075581, baseEnd_2075581] using wordTrace_append hprefix tailTrace_2075581
  have hstable : (prefixWord ++ tailWord_2075581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075581).length < 2 ^ (prefixWord ++ tailWord_2075581).sum := by decide
  have hdescent : baseEnd_2075581 < baseStart_2075581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075685 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2075685 : Nat := 118140960795 + 2075685 * 2 ^ 59
def prefixEnd_2075685 : Nat := 4983230072969 + 3 ^ 40 * 2075685 * 2
def baseEnd_2075685 : Nat := 473699596590140714040713

theorem tailTrace_2075685 : CollatzResearch.WordTrace tailWord_2075685 prefixEnd_2075685 473699596590140714040713 := by
  unfold tailWord_2075685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75706451485155218620020509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50470967656770145746680339 75706451485155218620020509)
  ·
    refine ⟨28389919306933206982507691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75706451485155218620020509 28389919306933206982507691)
    ·
      refine ⟨42584878960399810473761537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389919306933206982507691 42584878960399810473761537)
      ·
        refine ⟨31938659220299857855321153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42584878960399810473761537 31938659220299857855321153)
        ·
          refine ⟨23953994415224893391490865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31938659220299857855321153 23953994415224893391490865)
          ·
            refine ⟨17965495811418670043618149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23953994415224893391490865 17965495811418670043618149)
            ·
              refine ⟨3368530464641000633178403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17965495811418670043618149 3368530464641000633178403)
              ·
                refine ⟨5052795696961500949767605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368530464641000633178403 5052795696961500949767605)
                ·
                  refine ⟨473699596590140714040713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5052795696961500949767605 473699596590140714040713)
                  ·
                    rfl

theorem cell21_2075685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2075685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075685 prefixEnd_2075685 := by exact prefixLift 2075685
  have htrace : WordTrace (prefixWord ++ tailWord_2075685) baseStart_2075685 baseEnd_2075685 := by
    simpa [prefixWord, tailWord_2075685, baseEnd_2075685] using wordTrace_append hprefix tailTrace_2075685
  have hstable : (prefixWord ++ tailWord_2075685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075685).length < 2 ^ (prefixWord ++ tailWord_2075685).sum := by decide
  have hdescent : baseEnd_2075685 < baseStart_2075685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075702 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2075702 : Nat := 118140960795 + 2075702 * 2 ^ 59
def prefixEnd_2075702 : Nat := 4983230072969 + 3 ^ 40 * 2075702 * 2
def baseEnd_2075702 : Nat := 473703476221752462257345

theorem tailTrace_2075702 : CollatzResearch.WordTrace tailWord_2075702 prefixEnd_2075702 473703476221752462257345 := by
  unfold tailWord_2075702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731691970380851907711835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50471381017395753682259573 4731691970380851907711835)
  ·
    refine ⟨7097537955571277861567753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4731691970380851907711835 7097537955571277861567753)
    ·
      refine ⟨5323153466678458396175815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7097537955571277861567753 5323153466678458396175815)
      ·
        refine ⟨7984730200017687594263723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323153466678458396175815 7984730200017687594263723)
        ·
          refine ⟨11977095300026531391395585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984730200017687594263723 11977095300026531391395585)
          ·
            refine ⟨8982821475019898543546689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11977095300026531391395585 8982821475019898543546689)
            ·
              refine ⟨6737116106264923907660017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982821475019898543546689 6737116106264923907660017)
              ·
                refine ⟨5052837079698692930745013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737116106264923907660017 5052837079698692930745013)
                ·
                  refine ⟨473703476221752462257345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5052837079698692930745013 473703476221752462257345)
                  ·
                    rfl

theorem cell21_2075702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2075702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075702 prefixEnd_2075702 := by exact prefixLift 2075702
  have htrace : WordTrace (prefixWord ++ tailWord_2075702) baseStart_2075702 baseEnd_2075702 := by
    simpa [prefixWord, tailWord_2075702, baseEnd_2075702] using wordTrace_append hprefix tailTrace_2075702
  have hstable : (prefixWord ++ tailWord_2075702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075702).length < 2 ^ (prefixWord ++ tailWord_2075702).sum := by decide
  have hdescent : baseEnd_2075702 < baseStart_2075702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075719 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 3]
def baseStart_2075719 : Nat := 118140960795 + 2075719 * 2 ^ 59
def prefixEnd_2075719 : Nat := 4983230072969 + 3 ^ 40 * 2075719 * 2
def baseEnd_2075719 : Nat := 473707355853364210473977

theorem tailTrace_2075719 : CollatzResearch.WordTrace tailWord_2075719 prefixEnd_2075719 473707355853364210473977 := by
  unfold tailWord_2075719
  simp only [CollatzResearch.WordTrace]
  refine ⟨75707691567032042426758211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50471794378021361617838807 75707691567032042426758211)
  ·
    refine ⟨113561537350548063640137317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75707691567032042426758211 113561537350548063640137317)
    ·
      refine ⟨21292788253227761932525747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113561537350548063640137317 21292788253227761932525747)
      ·
        refine ⟨31939182379841642898788621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292788253227761932525747 31939182379841642898788621)
        ·
          refine ⟨11977193392440616087045733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31939182379841642898788621 11977193392440616087045733)
          ·
            refine ⟨2245723761082615516321075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11977193392440616087045733 2245723761082615516321075)
            ·
              refine ⟨3368585641623923274481613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245723761082615516321075 3368585641623923274481613)
              ·
                refine ⟨1263219615608971227930605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3368585641623923274481613 1263219615608971227930605)
                ·
                  refine ⟨473707355853364210473977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263219615608971227930605 473707355853364210473977)
                  ·
                    rfl

theorem cell21_2075719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].length) (baseStart_2075719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075719 prefixEnd_2075719 := by exact prefixLift 2075719
  have htrace : WordTrace (prefixWord ++ tailWord_2075719) baseStart_2075719 baseEnd_2075719 := by
    simpa [prefixWord, tailWord_2075719, baseEnd_2075719] using wordTrace_append hprefix tailTrace_2075719
  have hstable : (prefixWord ++ tailWord_2075719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075719).length < 2 ^ (prefixWord ++ tailWord_2075719).sum := by decide
  have hdescent : baseEnd_2075719 < baseStart_2075719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075730 : List Nat := [3, 2, 2, 1, 3, 1, 9]
def baseStart_2075730 : Nat := 118140960795 + 2075730 * 2 ^ 59
def prefixEnd_2075730 : Nat := 4983230072969 + 3 ^ 40 * 2075730 * 2
def baseEnd_2075730 : Nat := 52634429578136737310069

theorem tailTrace_2075730 : CollatzResearch.WordTrace tailWord_2075730 prefixEnd_2075730 52634429578136737310069 := by
  unfold tailWord_2075730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18927023192498047826352161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50472061846661460870272429 18927023192498047826352161)
  ·
    refine ⟨14195267394373535869764121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18927023192498047826352161 14195267394373535869764121)
    ·
      refine ⟨10646450545780151902323091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14195267394373535869764121 10646450545780151902323091)
      ·
        refine ⟨15969675818670227853484637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10646450545780151902323091 15969675818670227853484637)
        ·
          refine ⟨5988628432001335445056739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15969675818670227853484637 5988628432001335445056739)
          ·
            refine ⟨8982942648002003167585109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988628432001335445056739 8982942648002003167585109)
            ·
              refine ⟨52634429578136737310069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8982942648002003167585109 52634429578136737310069)
              ·
                rfl

theorem cell21_2075730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 9].length) (baseStart_2075730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075730 prefixEnd_2075730 := by exact prefixLift 2075730
  have htrace : WordTrace (prefixWord ++ tailWord_2075730) baseStart_2075730 baseEnd_2075730 := by
    simpa [prefixWord, tailWord_2075730, baseEnd_2075730] using wordTrace_append hprefix tailTrace_2075730
  have hstable : (prefixWord ++ tailWord_2075730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075730).length < 2 ^ (prefixWord ++ tailWord_2075730).sum := by decide
  have hdescent : baseEnd_2075730 < baseStart_2075730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075851 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_2075851 : Nat := 118140960795 + 2075851 * 2 ^ 59
def prefixEnd_2075851 : Nat := 4983230072969 + 3 ^ 40 * 2075851 * 2
def baseEnd_2075851 : Nat := 473737480051761314273707

theorem tailTrace_2075851 : CollatzResearch.WordTrace tailWord_2075851 prefixEnd_2075851 473737480051761314273707 := by
  unfold tailWord_2075851
  simp only [CollatzResearch.WordTrace]
  refine ⟨75712506002553828970563407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50475004001702552647042271 75712506002553828970563407)
  ·
    refine ⟨113568759003830743455845111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75712506002553828970563407 113568759003830743455845111)
    ·
      refine ⟨170353138505746115183767667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113568759003830743455845111 170353138505746115183767667)
      ·
        refine ⟨255529707758619172775651501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170353138505746115183767667 255529707758619172775651501)
        ·
          refine ⟨95823640409482189790869313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255529707758619172775651501 95823640409482189790869313)
          ·
            refine ⟨71867730307111642343151985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95823640409482189790869313 71867730307111642343151985)
            ·
              refine ⟨53900797730333731757363989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71867730307111642343151985 53900797730333731757363989)
              ·
                refine ⟨2526599893609393676126437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53900797730333731757363989 2526599893609393676126437)
                ·
                  refine ⟨473737480051761314273707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526599893609393676126437 473737480051761314273707)
                  ·
                    rfl

theorem cell21_2075851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_2075851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075851 prefixEnd_2075851 := by exact prefixLift 2075851
  have htrace : WordTrace (prefixWord ++ tailWord_2075851) baseStart_2075851 baseEnd_2075851 := by
    simpa [prefixWord, tailWord_2075851, baseEnd_2075851] using wordTrace_append hprefix tailTrace_2075851
  have hstable : (prefixWord ++ tailWord_2075851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075851).length < 2 ^ (prefixWord ++ tailWord_2075851).sum := by decide
  have hdescent : baseEnd_2075851 < baseStart_2075851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075854 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2075854 : Nat := 118140960795 + 2075854 * 2 ^ 59
def prefixEnd_2075854 : Nat := 4983230072969 + 3 ^ 40 * 2075854 * 2
def baseEnd_2075854 : Nat := 473738164692633975723701

theorem tailTrace_2075854 : CollatzResearch.WordTrace tailWord_2075854 prefixEnd_2075854 473738164692633975723701 := by
  unfold tailWord_2075854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464076927692870060365327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50475076947695306988615077 9464076927692870060365327)
  ·
    refine ⟨14196115391539305090547991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464076927692870060365327 14196115391539305090547991)
    ·
      refine ⟨21294173087308957635821987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14196115391539305090547991 21294173087308957635821987)
      ·
        refine ⟨31941259630963436453732981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21294173087308957635821987 31941259630963436453732981)
        ·
          refine ⟨2994493090402822167537467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31941259630963436453732981 2994493090402822167537467)
          ·
            refine ⟨4491739635604233251306201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994493090402822167537467 4491739635604233251306201)
            ·
              refine ⟨3368804726703174938479651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491739635604233251306201 3368804726703174938479651)
              ·
                refine ⟨5053207090054762407719477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368804726703174938479651 5053207090054762407719477)
                ·
                  refine ⟨473738164692633975723701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053207090054762407719477 473738164692633975723701)
                  ·
                    rfl

theorem cell21_2075854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2075854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075854 prefixEnd_2075854 := by exact prefixLift 2075854
  have htrace : WordTrace (prefixWord ++ tailWord_2075854) baseStart_2075854 baseEnd_2075854 := by
    simpa [prefixWord, tailWord_2075854, baseEnd_2075854] using wordTrace_append hprefix tailTrace_2075854
  have hstable : (prefixWord ++ tailWord_2075854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075854).length < 2 ^ (prefixWord ++ tailWord_2075854).sum := by decide
  have hdescent : baseEnd_2075854 < baseStart_2075854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075865 : List Nat := [1, 2, 1, 2, 3, 1, 1, 10]
def baseStart_2075865 : Nat := 118140960795 + 2075865 * 2 ^ 59
def prefixEnd_2075865 : Nat := 4983230072969 + 3 ^ 40 * 2075865 * 2
def baseEnd_2075865 : Nat := 157913558347500133680115

theorem tailTrace_2075865 : CollatzResearch.WordTrace tailWord_2075865 prefixEnd_2075865 157913558347500133680115 := by
  unfold tailWord_2075865
  simp only [CollatzResearch.WordTrace]
  refine ⟨75713016624503109361573049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50475344416335406241048699 75713016624503109361573049)
  ·
    refine ⟨56784762468377332021179787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75713016624503109361573049 56784762468377332021179787)
    ·
      refine ⟨85177143702565998031769681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56784762468377332021179787 85177143702565998031769681)
      ·
        refine ⟨63882857776924498523827261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85177143702565998031769681 63882857776924498523827261)
        ·
          refine ⟨23956071666346686946435223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63882857776924498523827261 23956071666346686946435223)
          ·
            refine ⟨35934107499520030419652835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956071666346686946435223 35934107499520030419652835)
            ·
              refine ⟨53901161249280045629479253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35934107499520030419652835 53901161249280045629479253)
              ·
                refine ⟨157913558347500133680115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53901161249280045629479253 157913558347500133680115)
                ·
                  rfl

theorem cell21_2075865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_2075865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075865 prefixEnd_2075865 := by exact prefixLift 2075865
  have htrace : WordTrace (prefixWord ++ tailWord_2075865) baseStart_2075865 baseEnd_2075865 := by
    simpa [prefixWord, tailWord_2075865, baseEnd_2075865] using wordTrace_append hprefix tailTrace_2075865
  have hstable : (prefixWord ++ tailWord_2075865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075865).length < 2 ^ (prefixWord ++ tailWord_2075865).sum := by decide
  have hdescent : baseEnd_2075865 < baseStart_2075865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075882 : List Nat := [3, 1, 3, 1, 1, 4, 1, 7]
def baseStart_2075882 : Nat := 118140960795 + 2075882 * 2 ^ 59
def prefixEnd_2075882 : Nat := 4983230072969 + 3 ^ 40 * 2075882 * 2
def baseEnd_2075882 : Nat := 157914851558037383085659

theorem tailTrace_2075882 : CollatzResearch.WordTrace tailWord_2075882 prefixEnd_2075882 157914851558037383085659 := by
  unfold tailWord_2075882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928409166360380316235475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50475757776961014176627933 18928409166360380316235475)
  ·
    refine ⟨28392613749540570474353213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928409166360380316235475 28392613749540570474353213)
    ·
      refine ⟨10647230156077713927882455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28392613749540570474353213 10647230156077713927882455)
      ·
        refine ⟨15970845234116570891823683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647230156077713927882455 15970845234116570891823683)
        ·
          refine ⟨23956267851174856337735525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15970845234116570891823683 23956267851174856337735525)
          ·
            refine ⟨4491800222095285563325411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23956267851174856337735525 4491800222095285563325411)
            ·
              refine ⟨6737700333142928344988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491800222095285563325411 6737700333142928344988117)
              ·
                refine ⟨157914851558037383085659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6737700333142928344988117 157914851558037383085659)
                ·
                  rfl

theorem cell21_2075882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_2075882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075882 prefixEnd_2075882 := by exact prefixLift 2075882
  have htrace : WordTrace (prefixWord ++ tailWord_2075882) baseStart_2075882 baseEnd_2075882 := by
    simpa [prefixWord, tailWord_2075882, baseEnd_2075882] using wordTrace_append hprefix tailTrace_2075882
  have hstable : (prefixWord ++ tailWord_2075882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075882).length < 2 ^ (prefixWord ++ tailWord_2075882).sum := by decide
  have hdescent : baseEnd_2075882 < baseStart_2075882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075961 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2075961 : Nat := 118140960795 + 2075961 * 2 ^ 59
def prefixEnd_2075961 : Nat := 4983230072969 + 3 ^ 40 * 2075961 * 2
def baseEnd_2075961 : Nat := 473762583550425567440149

theorem tailTrace_2075961 : CollatzResearch.WordTrace tailWord_2075961 prefixEnd_2075961 473762583550425567440149 := by
  unfold tailWord_2075961
  simp only [CollatzResearch.WordTrace]
  refine ⟨75716518032155317757067737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50477678688103545171378491 75716518032155317757067737)
  ·
    refine ⟨56787388524116488317800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75716518032155317757067737 56787388524116488317800803)
    ·
      refine ⟨85181082786174732476701205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56787388524116488317800803 85181082786174732476701205)
      ·
        refine ⟨3992863255601940584845369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85181082786174732476701205 3992863255601940584845369)
        ·
          refine ⟨2994647441701455438634027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992863255601940584845369 2994647441701455438634027)
          ·
            refine ⟨4491971162552183157951041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994647441701455438634027 4491971162552183157951041)
            ·
              refine ⟨3368978371914137368463281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491971162552183157951041 3368978371914137368463281)
              ·
                refine ⟨2526733778935603026347461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368978371914137368463281 2526733778935603026347461)
                ·
                  refine ⟨473762583550425567440149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526733778935603026347461 473762583550425567440149)
                  ·
                    rfl

theorem cell21_2075961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2075961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075961 prefixEnd_2075961 := by exact prefixLift 2075961
  have htrace : WordTrace (prefixWord ++ tailWord_2075961) baseStart_2075961 baseEnd_2075961 := by
    simpa [prefixWord, tailWord_2075961, baseEnd_2075961] using wordTrace_append hprefix tailTrace_2075961
  have hstable : (prefixWord ++ tailWord_2075961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075961).length < 2 ^ (prefixWord ++ tailWord_2075961).sum := by decide
  have hdescent : baseEnd_2075961 < baseStart_2075961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075989 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_2075989 : Nat := 118140960795 + 2075989 * 2 ^ 59
def prefixEnd_2075989 : Nat := 4983230072969 + 3 ^ 40 * 2075989 * 2
def baseEnd_2075989 : Nat := 473768973531903740973425

theorem tailTrace_2075989 : CollatzResearch.WordTrace tailWord_2075989 prefixEnd_2075989 473768973531903740973425 := by
  unfold tailWord_2075989
  simp only [CollatzResearch.WordTrace]
  refine ⟨75717539276053878539087021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50478359517369252359391347 75717539276053878539087021)
  ·
    refine ⟨28394077228520204452157633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75717539276053878539087021 28394077228520204452157633)
    ·
      refine ⟨21295557921390153339118225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28394077228520204452157633 21295557921390153339118225)
      ·
        refine ⟨15971668441042615004338669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21295557921390153339118225 15971668441042615004338669)
        ·
          refine ⟨5989375665390980626627001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15971668441042615004338669 5989375665390980626627001)
          ·
            refine ⟨4492031749043235469970251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5989375665390980626627001 4492031749043235469970251)
            ·
              refine ⟨6738047623564853204955377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492031749043235469970251 6738047623564853204955377)
              ·
                refine ⟨5053535717673639903716533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738047623564853204955377 5053535717673639903716533)
                ·
                  refine ⟨473768973531903740973425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053535717673639903716533 473768973531903740973425)
                  ·
                    rfl

theorem cell21_2075989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_2075989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2075989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2075989 prefixEnd_2075989 := by exact prefixLift 2075989
  have htrace : WordTrace (prefixWord ++ tailWord_2075989) baseStart_2075989 baseEnd_2075989 := by
    simpa [prefixWord, tailWord_2075989, baseEnd_2075989] using wordTrace_append hprefix tailTrace_2075989
  have hstable : (prefixWord ++ tailWord_2075989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075989).length < 2 ^ (prefixWord ++ tailWord_2075989).sum := by decide
  have hdescent : baseEnd_2075989 < baseStart_2075989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076096 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_2076096 : Nat := 118140960795 + 2076096 * 2 ^ 59
def prefixEnd_2076096 : Nat := 4983230072969 + 3 ^ 40 * 2076096 * 2
def baseEnd_2076096 : Nat := 473793392389695332689873

theorem tailTrace_2076096 : CollatzResearch.WordTrace tailWord_2076096 prefixEnd_2076096 473793392389695332689873 := by
  unfold tailWord_2076096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860720943333117906616071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50480961257777490542154761 37860720943333117906616071)
  ·
    refine ⟨56791081414999676859924107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37860720943333117906616071 56791081414999676859924107)
    ·
      refine ⟨85186622122499515289886161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56791081414999676859924107 85186622122499515289886161)
      ·
        refine ⟨63889966591874636467414621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85186622122499515289886161 63889966591874636467414621)
        ·
          refine ⟨23958737471952988675280483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63889966591874636467414621 23958737471952988675280483)
          ·
            refine ⟨35938106207929483012920725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23958737471952988675280483 35938106207929483012920725)
            ·
              refine ⟨1684598728496694516230659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35938106207929483012920725 1684598728496694516230659)
              ·
                refine ⟨2526898092745041774345989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684598728496694516230659 2526898092745041774345989)
                ·
                  refine ⟨473793392389695332689873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526898092745041774345989 473793392389695332689873)
                  ·
                    rfl

theorem cell21_2076096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_2076096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076096 prefixEnd_2076096 := by exact prefixLift 2076096
  have htrace : WordTrace (prefixWord ++ tailWord_2076096) baseStart_2076096 baseEnd_2076096 := by
    simpa [prefixWord, tailWord_2076096, baseEnd_2076096] using wordTrace_append hprefix tailTrace_2076096
  have hstable : (prefixWord ++ tailWord_2076096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076096).length < 2 ^ (prefixWord ++ tailWord_2076096).sum := by decide
  have hdescent : baseEnd_2076096 < baseStart_2076096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076220 : List Nat := [2, 2, 2, 2, 5, 1, 2, 5]
def baseStart_2076220 : Nat := 118140960795 + 2076220 * 2 ^ 59
def prefixEnd_2076220 : Nat := 4983230072969 + 3 ^ 40 * 2076220 * 2
def baseEnd_2076220 : Nat := 157940563626366224207651

theorem tailTrace_2076220 : CollatzResearch.WordTrace tailWord_2076220 prefixEnd_2076220 157940563626366224207651 := by
  unfold tailWord_2076220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37862982269108502495373057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50483976358811336660497409 37862982269108502495373057)
  ·
    refine ⟨28397236701831376871529793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37862982269108502495373057 28397236701831376871529793)
    ·
      refine ⟨21297927526373532653647345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28397236701831376871529793 21297927526373532653647345)
      ·
        refine ⟨15973445644780149490235509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21297927526373532653647345 15973445644780149490235509)
        ·
          refine ⟨1497510529198139014709579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15973445644780149490235509 1497510529198139014709579)
          ·
            refine ⟨2246265793797208522064369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497510529198139014709579 2246265793797208522064369)
            ·
              refine ⟨1684699345347906391548277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246265793797208522064369 1684699345347906391548277)
              ·
                refine ⟨157940563626366224207651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1684699345347906391548277 157940563626366224207651)
                ·
                  rfl

theorem cell21_2076220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_2076220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076220 prefixEnd_2076220 := by exact prefixLift 2076220
  have htrace : WordTrace (prefixWord ++ tailWord_2076220) baseStart_2076220 baseEnd_2076220 := by
    simpa [prefixWord, tailWord_2076220, baseEnd_2076220] using wordTrace_append hprefix tailTrace_2076220
  have hstable : (prefixWord ++ tailWord_2076220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076220).length < 2 ^ (prefixWord ++ tailWord_2076220).sum := by decide
  have hdescent : baseEnd_2076220 < baseStart_2076220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076293 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 3]
def baseStart_2076293 : Nat := 118140960795 + 2076293 * 2 ^ 59
def prefixEnd_2076293 : Nat := 4983230072969 + 3 ^ 40 * 2076293 * 2
def baseEnd_2076293 : Nat := 473838350473666767906137

theorem tailTrace_2076293 : CollatzResearch.WordTrace tailWord_2076293 prefixEnd_2076293 473838350473666767906137 := by
  unfold tailWord_2076293
  simp only [CollatzResearch.WordTrace]
  refine ⟨75728627066952538458153533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50485751377968358972102355 75728627066952538458153533)
  ·
    refine ⟨28398235150107201921807575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75728627066952538458153533 28398235150107201921807575)
    ·
      refine ⟨42597352725160802882711363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398235150107201921807575 42597352725160802882711363)
      ·
        refine ⟨63896029087741204324067045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597352725160802882711363 63896029087741204324067045)
        ·
          refine ⟨11980505453951475810762571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63896029087741204324067045 11980505453951475810762571)
          ·
            refine ⟨17970758180927213716143857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980505453951475810762571 17970758180927213716143857)
            ·
              refine ⟨13478068635695410287107893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17970758180927213716143857 13478068635695410287107893)
              ·
                refine ⟨1263568934596444714416365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13478068635695410287107893 1263568934596444714416365)
                ·
                  refine ⟨473838350473666767906137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263568934596444714416365 473838350473666767906137)
                  ·
                    rfl

theorem cell21_2076293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_2076293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076293 prefixEnd_2076293 := by exact prefixLift 2076293
  have htrace : WordTrace (prefixWord ++ tailWord_2076293) baseStart_2076293 baseEnd_2076293 := by
    simpa [prefixWord, tailWord_2076293, baseEnd_2076293] using wordTrace_append hprefix tailTrace_2076293
  have hstable : (prefixWord ++ tailWord_2076293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076293).length < 2 ^ (prefixWord ++ tailWord_2076293).sum := by decide
  have hdescent : baseEnd_2076293 < baseStart_2076293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076358 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2076358 : Nat := 118140960795 + 2076358 * 2 ^ 59
def prefixEnd_2076358 : Nat := 4983230072969 + 3 ^ 40 * 2076358 * 2
def baseEnd_2076358 : Nat := 473853184359241099322671

theorem tailTrace_2076358 : CollatzResearch.WordTrace tailWord_2076358 prefixEnd_2076358 473853184359241099322671 := by
  unfold tailWord_2076358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366593681616157954977179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50487331874478036372846485 2366593681616157954977179)
  ·
    refine ⟨3549890522424236932465769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366593681616157954977179 3549890522424236932465769)
    ·
      refine ⟨2662417891818177699349327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549890522424236932465769 2662417891818177699349327)
      ·
        refine ⟨3993626837727266549023991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662417891818177699349327 3993626837727266549023991)
        ·
          refine ⟨5990440256590899823535987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993626837727266549023991 5990440256590899823535987)
          ·
            refine ⟨8985660384886349735303981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990440256590899823535987 8985660384886349735303981)
            ·
              refine ⟨3369622644332381150738993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8985660384886349735303981 3369622644332381150738993)
              ·
                refine ⟨2527216983249285863054245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369622644332381150738993 2527216983249285863054245)
                ·
                  refine ⟨473853184359241099322671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527216983249285863054245 473853184359241099322671)
                  ·
                    rfl

theorem cell21_2076358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2076358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076358 prefixEnd_2076358 := by exact prefixLift 2076358
  have htrace : WordTrace (prefixWord ++ tailWord_2076358) baseStart_2076358 baseEnd_2076358 := by
    simpa [prefixWord, tailWord_2076358, baseEnd_2076358] using wordTrace_append hprefix tailTrace_2076358
  have hstable : (prefixWord ++ tailWord_2076358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076358).length < 2 ^ (prefixWord ++ tailWord_2076358).sum := by decide
  have hdescent : baseEnd_2076358 < baseStart_2076358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076369 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 3]
def baseStart_2076369 : Nat := 118140960795 + 2076369 * 2 ^ 59
def prefixEnd_2076369 : Nat := 4983230072969 + 3 ^ 40 * 2076369 * 2
def baseEnd_2076369 : Nat := 473855694709107524639315

theorem tailTrace_2076369 : CollatzResearch.WordTrace tailWord_2076369 prefixEnd_2076369 473855694709107524639315 := by
  unfold tailWord_2076369
  simp only [CollatzResearch.WordTrace]
  refine ⟨75731399014677203437920161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50487599343118135625280107 75731399014677203437920161)
  ·
    refine ⟨56798549261007902578440121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75731399014677203437920161 56798549261007902578440121)
    ·
      refine ⟨42598911945755926933830091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56798549261007902578440121 42598911945755926933830091)
      ·
        refine ⟨63898367918633890400745137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42598911945755926933830091 63898367918633890400745137)
        ·
          refine ⟨47923775938975417800558853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63898367918633890400745137 47923775938975417800558853)
          ·
            refine ⟨8985707988557890837604785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47923775938975417800558853 8985707988557890837604785)
            ·
              refine ⟨6739280991418418128203589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985707988557890837604785 6739280991418418128203589)
              ·
                refine ⟨1263615185890953399038173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6739280991418418128203589 1263615185890953399038173)
                ·
                  refine ⟨473855694709107524639315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263615185890953399038173 473855694709107524639315)
                  ·
                    rfl

theorem cell21_2076369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_2076369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076369 prefixEnd_2076369 := by exact prefixLift 2076369
  have htrace : WordTrace (prefixWord ++ tailWord_2076369) baseStart_2076369 baseEnd_2076369 := by
    simpa [prefixWord, tailWord_2076369, baseEnd_2076369] using wordTrace_append hprefix tailTrace_2076369
  have hstable : (prefixWord ++ tailWord_2076369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076369).length < 2 ^ (prefixWord ++ tailWord_2076369).sum := by decide
  have hdescent : baseEnd_2076369 < baseStart_2076369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076428 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_2076428 : Nat := 118140960795 + 2076428 * 2 ^ 59
def prefixEnd_2076428 : Nat := 4983230072969 + 3 ^ 40 * 2076428 * 2
def baseEnd_2076428 : Nat := 473869159312936533155861

theorem tailTrace_2076428 : CollatzResearch.WordTrace tailWord_2076428 prefixEnd_2076428 473869159312936533155861 := by
  unfold tailWord_2076428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866775460731728257158969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50489033947642304342878625 37866775460731728257158969)
  ·
    refine ⟨28400081595548796192869227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37866775460731728257158969 28400081595548796192869227)
    ·
      refine ⟨42600122393323194289303841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28400081595548796192869227 42600122393323194289303841)
      ·
        refine ⟨31950091794992395716977881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42600122393323194289303841 31950091794992395716977881)
        ·
          refine ⟨23962568846244296787733411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31950091794992395716977881 23962568846244296787733411)
          ·
            refine ⟨35943853269366445181600117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23962568846244296787733411 35943853269366445181600117)
            ·
              refine ⟨3369736244003104235775011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35943853269366445181600117 3369736244003104235775011)
              ·
                refine ⟨5054604366004656353662517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369736244003104235775011 5054604366004656353662517)
                ·
                  refine ⟨473869159312936533155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5054604366004656353662517 473869159312936533155861)
                  ·
                    rfl

theorem cell21_2076428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_2076428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076428 prefixEnd_2076428 := by exact prefixLift 2076428
  have htrace : WordTrace (prefixWord ++ tailWord_2076428) baseStart_2076428 baseEnd_2076428 := by
    simpa [prefixWord, tailWord_2076428, baseEnd_2076428] using wordTrace_append hprefix tailTrace_2076428
  have hstable : (prefixWord ++ tailWord_2076428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076428).length < 2 ^ (prefixWord ++ tailWord_2076428).sum := by decide
  have hdescent : baseEnd_2076428 < baseStart_2076428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076434 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_2076434 : Nat := 118140960795 + 2076434 * 2 ^ 59
def prefixEnd_2076434 : Nat := 4983230072969 + 3 ^ 40 * 2076434 * 2
def baseEnd_2076434 : Nat := 473870528594681856055849

theorem tailTrace_2076434 : CollatzResearch.WordTrace tailWord_2076434 prefixEnd_2076434 473870528594681856055849 := by
  unfold tailWord_2076434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933442439860429884759089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50489179839627813026024237 18933442439860429884759089)
  ·
    refine ⟨14200081829895322413569317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18933442439860429884759089 14200081829895322413569317)
    ·
      refine ⟨2662515343105372952544247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14200081829895322413569317 2662515343105372952544247)
      ·
        refine ⟨3993773014658059428816371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662515343105372952544247 3993773014658059428816371)
        ·
          refine ⟨5990659521987089143224557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993773014658059428816371 5990659521987089143224557)
          ·
            refine ⟨2246497320745158428709209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5990659521987089143224557 2246497320745158428709209)
            ·
              refine ⟨1684872990558868821531907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246497320745158428709209 1684872990558868821531907)
              ·
                refine ⟨2527309485838303232297861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684872990558868821531907 2527309485838303232297861)
                ·
                  refine ⟨473870528594681856055849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527309485838303232297861 473870528594681856055849)
                  ·
                    rfl

theorem cell21_2076434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_2076434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076434 prefixEnd_2076434 := by exact prefixLift 2076434
  have htrace : WordTrace (prefixWord ++ tailWord_2076434) baseStart_2076434 baseEnd_2076434 := by
    simpa [prefixWord, tailWord_2076434, baseEnd_2076434] using wordTrace_append hprefix tailTrace_2076434
  have hstable : (prefixWord ++ tailWord_2076434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076434).length < 2 ^ (prefixWord ++ tailWord_2076434).sum := by decide
  have hdescent : baseEnd_2076434 < baseStart_2076434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076473 : List Nat := [1, 2, 1, 7, 10]
def baseStart_2076473 : Nat := 118140960795 + 2076473 * 2 ^ 59
def prefixEnd_2076473 : Nat := 4983230072969 + 3 ^ 40 * 2076473 * 2
def baseEnd_2076473 : Nat := 5850363320074400677849

theorem tailTrace_2076473 : CollatzResearch.WordTrace tailWord_2076473 prefixEnd_2076473 5850363320074400677849 := by
  unfold tailWord_2076473
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735192206300429199706073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50490128137533619466470715 75735192206300429199706073)
  ·
    refine ⟨56801394154725321899779555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75735192206300429199706073 56801394154725321899779555)
    ·
      refine ⟨85202091232087982849669333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56801394154725321899779555 85202091232087982849669333)
      ·
        refine ⟨1996924013252062098039125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85202091232087982849669333 1996924013252062098039125)
        ·
          refine ⟨5850363320074400677849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1996924013252062098039125 5850363320074400677849)
          ·
            rfl

theorem cell21_2076473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 10].length) (baseStart_2076473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076473 prefixEnd_2076473 := by exact prefixLift 2076473
  have htrace : WordTrace (prefixWord ++ tailWord_2076473) baseStart_2076473 baseEnd_2076473 := by
    simpa [prefixWord, tailWord_2076473, baseEnd_2076473] using wordTrace_append hprefix tailTrace_2076473
  have hstable : (prefixWord ++ tailWord_2076473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076473).length < 2 ^ (prefixWord ++ tailWord_2076473).sum := by decide
  have hdescent : baseEnd_2076473 < baseStart_2076473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076479 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 3]
def baseStart_2076479 : Nat := 118140960795 + 2076479 * 2 ^ 59
def prefixEnd_2076479 : Nat := 4983230072969 + 3 ^ 40 * 2076479 * 2
def baseEnd_2076479 : Nat := 473880798207771777805757

theorem tailTrace_2076479 : CollatzResearch.WordTrace tailWord_2076479 prefixEnd_2076479 473880798207771777805757 := by
  unfold tailWord_2076479
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735411044278692224424491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50490274029519128149616327 75735411044278692224424491)
  ·
    refine ⟨113603116566418038336636737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75735411044278692224424491 113603116566418038336636737)
    ·
      refine ⟨85202337424813528752477553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113603116566418038336636737 85202337424813528752477553)
      ·
        refine ⟨63901753068610146564358165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85202337424813528752477553 63901753068610146564358165)
        ·
          refine ⟨2995394675091100620204289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63901753068610146564358165 2995394675091100620204289)
          ·
            refine ⟨2246546006318325465153217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995394675091100620204289 2246546006318325465153217)
            ·
              refine ⟨1684909504738744098864913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246546006318325465153217 1684909504738744098864913)
              ·
                refine ⟨1263682128554058074148685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684909504738744098864913 1263682128554058074148685)
                ·
                  refine ⟨473880798207771777805757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263682128554058074148685 473880798207771777805757)
                  ·
                    rfl

theorem cell21_2076479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].length) (baseStart_2076479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076479 prefixEnd_2076479 := by exact prefixLift 2076479
  have htrace : WordTrace (prefixWord ++ tailWord_2076479) baseStart_2076479 baseEnd_2076479 := by
    simpa [prefixWord, tailWord_2076479, baseEnd_2076479] using wordTrace_append hprefix tailTrace_2076479
  have hstable : (prefixWord ++ tailWord_2076479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076479).length < 2 ^ (prefixWord ++ tailWord_2076479).sum := by decide
  have hdescent : baseEnd_2076479 < baseStart_2076479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076597 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2076597 : Nat := 118140960795 + 2076597 * 2 ^ 59
def prefixEnd_2076597 : Nat := 4983230072969 + 3 ^ 40 * 2076597 * 2
def baseEnd_2076597 : Nat := 473907727415429794838849

theorem tailTrace_2076597 : CollatzResearch.WordTrace tailWord_2076597 prefixEnd_2076597 473907727415429794838849 := by
  unfold tailWord_2076597
  simp only [CollatzResearch.WordTrace]
  refine ⟨75739714857851198377220045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50493143238567465584813363 75739714857851198377220045)
  ·
    refine ⟨28402393071694199391457517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75739714857851198377220045 28402393071694199391457517)
    ·
      refine ⟨10650897401885324771796569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28402393071694199391457517 10650897401885324771796569)
      ·
        refine ⟨7988173051413993578847427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10650897401885324771796569 7988173051413993578847427)
        ·
          refine ⟨11982259577120990368271141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988173051413993578847427 11982259577120990368271141)
          ·
            refine ⟨2246673670710185694050839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11982259577120990368271141 2246673670710185694050839)
            ·
              refine ⟨3370010506065278541076259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246673670710185694050839 3370010506065278541076259)
              ·
                refine ⟨5055015759097917811614389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370010506065278541076259 5055015759097917811614389)
                ·
                  refine ⟨473907727415429794838849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5055015759097917811614389 473907727415429794838849)
                  ·
                    rfl

theorem cell21_2076597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2076597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076597 prefixEnd_2076597 := by exact prefixLift 2076597
  have htrace : WordTrace (prefixWord ++ tailWord_2076597) baseStart_2076597 baseEnd_2076597 := by
    simpa [prefixWord, tailWord_2076597, baseEnd_2076597] using wordTrace_append hprefix tailTrace_2076597
  have hstable : (prefixWord ++ tailWord_2076597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076597).length < 2 ^ (prefixWord ++ tailWord_2076597).sum := by decide
  have hdescent : baseEnd_2076597 < baseStart_2076597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076642 : List Nat := [3, 3, 3, 1, 2, 9]
def baseStart_2076642 : Nat := 118140960795 + 2076642 * 2 ^ 59
def prefixEnd_2076642 : Nat := 4983230072969 + 3 ^ 40 * 2076642 * 2
def baseEnd_2076642 : Nat := 17552518408463693206991

theorem tailTrace_2076642 : CollatzResearch.WordTrace tailWord_2076642 prefixEnd_2076642 17552518408463693206991 := by
  unfold tailWord_2076642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935339035672042765652045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50494237428458780708405453 18935339035672042765652045)
  ·
    refine ⟨7100752138377016037119517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18935339035672042765652045 7100752138377016037119517)
    ·
      refine ⟨2662782051891381013919819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7100752138377016037119517 2662782051891381013919819)
      ·
        refine ⟨3994173077837071520879729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662782051891381013919819 3994173077837071520879729)
        ·
          refine ⟨2995629808377803640659797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994173077837071520879729 2995629808377803640659797)
          ·
            refine ⟨17552518408463693206991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2995629808377803640659797 17552518408463693206991)
            ·
              rfl

theorem cell21_2076642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 9].length) (baseStart_2076642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076642 prefixEnd_2076642 := by exact prefixLift 2076642
  have htrace : WordTrace (prefixWord ++ tailWord_2076642) baseStart_2076642 baseEnd_2076642 := by
    simpa [prefixWord, tailWord_2076642, baseEnd_2076642] using wordTrace_append hprefix tailTrace_2076642
  have hstable : (prefixWord ++ tailWord_2076642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076642).length < 2 ^ (prefixWord ++ tailWord_2076642).sum := by decide
  have hdescent : baseEnd_2076642 < baseStart_2076642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076701 : List Nat := [1, 4, 2, 2, 2, 2, 8]
def baseStart_2076701 : Nat := 118140960795 + 2076701 * 2 ^ 59
def prefixEnd_2076701 : Nat := 4983230072969 + 3 ^ 40 * 2076701 * 2
def baseEnd_2076701 : Nat := 52659051292483191678367

theorem tailTrace_2076701 : CollatzResearch.WordTrace tailWord_2076701 prefixEnd_2076701 52659051292483191678367 := by
  unfold tailWord_2076701
  simp only [CollatzResearch.WordTrace]
  refine ⟨75743508049474424139005957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50495672032982949426003971 75743508049474424139005957)
  ·
    refine ⟨14201907759276454526063617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75743508049474424139005957 14201907759276454526063617)
    ·
      refine ⟨10651430819457340894547713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14201907759276454526063617 10651430819457340894547713)
      ·
        refine ⟨7988573114593005670910785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10651430819457340894547713 7988573114593005670910785)
        ·
          refine ⟨5991429835944754253183089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7988573114593005670910785 5991429835944754253183089)
          ·
            refine ⟨4493572376958565689887317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5991429835944754253183089 4493572376958565689887317)
            ·
              refine ⟨52659051292483191678367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4493572376958565689887317 52659051292483191678367)
              ·
                rfl

theorem cell21_2076701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 8].length) (baseStart_2076701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076701 prefixEnd_2076701 := by exact prefixLift 2076701
  have htrace : WordTrace (prefixWord ++ tailWord_2076701) baseStart_2076701 baseEnd_2076701 := by
    simpa [prefixWord, tailWord_2076701, baseEnd_2076701] using wordTrace_append hprefix tailTrace_2076701
  have hstable : (prefixWord ++ tailWord_2076701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076701).length < 2 ^ (prefixWord ++ tailWord_2076701).sum := by decide
  have hdescent : baseEnd_2076701 < baseStart_2076701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076760 : List Nat := [2, 1, 2, 2, 1, 4, 9]
def baseStart_2076760 : Nat := 118140960795 + 2076760 * 2 ^ 59
def prefixEnd_2076760 : Nat := 4983230072969 + 3 ^ 40 * 2076760 * 2
def baseEnd_2076760 : Nat := 52660547359575303735761

theorem tailTrace_2076760 : CollatzResearch.WordTrace tailWord_2076760 prefixEnd_2076760 52660547359575303735761 := by
  unfold tailWord_2076760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872829978130338607701867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50497106637507118143602489 37872829978130338607701867)
  ·
    refine ⟨56809244967195507911552801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872829978130338607701867 56809244967195507911552801)
    ·
      refine ⟨42606933725396630933664601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56809244967195507911552801 42606933725396630933664601)
      ·
        refine ⟨31955200294047473200248451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42606933725396630933664601 31955200294047473200248451)
        ·
          refine ⟨47932800441071209800372677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31955200294047473200248451 47932800441071209800372677)
          ·
            refine ⟨8987400082700851837569877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47932800441071209800372677 8987400082700851837569877)
            ·
              refine ⟨52660547359575303735761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8987400082700851837569877 52660547359575303735761)
              ·
                rfl

theorem cell21_2076760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 9].length) (baseStart_2076760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076760 prefixEnd_2076760 := by exact prefixLift 2076760
  have htrace : WordTrace (prefixWord ++ tailWord_2076760) baseStart_2076760 baseEnd_2076760 := by
    simpa [prefixWord, tailWord_2076760, baseEnd_2076760] using wordTrace_append hprefix tailTrace_2076760
  have hstable : (prefixWord ++ tailWord_2076760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076760).length < 2 ^ (prefixWord ++ tailWord_2076760).sum := by decide
  have hdescent : baseEnd_2076760 < baseStart_2076760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076780 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2076780 : Nat := 118140960795 + 2076780 * 2 ^ 59
def prefixEnd_2076780 : Nat := 4983230072969 + 3 ^ 40 * 2076780 * 2
def baseEnd_2076780 : Nat := 473949490508662143288475

theorem tailTrace_2076780 : CollatzResearch.WordTrace tailWord_2076780 prefixEnd_2076780 473949490508662143288475 := by
  unfold tailWord_2076780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873194708094110315565897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50497592944125480420754529 37873194708094110315565897)
  ·
    refine ⟨28404896031070582736674423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37873194708094110315565897 28404896031070582736674423)
    ·
      refine ⟨42607344046605874105011635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28404896031070582736674423 42607344046605874105011635)
      ·
        refine ⟨63911016069908811157517453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42607344046605874105011635 63911016069908811157517453)
        ·
          refine ⟨23966631026215804184069045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63911016069908811157517453 23966631026215804184069045)
          ·
            refine ⟨2246871658707731642256473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23966631026215804184069045 2246871658707731642256473)
            ·
              refine ⟨1685153744030798731692355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246871658707731642256473 1685153744030798731692355)
              ·
                refine ⟨2527730616046198097538533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685153744030798731692355 2527730616046198097538533)
                ·
                  refine ⟨473949490508662143288475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527730616046198097538533 473949490508662143288475)
                  ·
                    rfl

theorem cell21_2076780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2076780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076780 prefixEnd_2076780 := by exact prefixLift 2076780
  have htrace : WordTrace (prefixWord ++ tailWord_2076780) baseStart_2076780 baseEnd_2076780 := by
    simpa [prefixWord, tailWord_2076780, baseEnd_2076780] using wordTrace_append hprefix tailTrace_2076780
  have hstable : (prefixWord ++ tailWord_2076780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076780).length < 2 ^ (prefixWord ++ tailWord_2076780).sum := by decide
  have hdescent : baseEnd_2076780 < baseStart_2076780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076935 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 3]
def baseStart_2076935 : Nat := 118140960795 + 2076935 * 2 ^ 59
def prefixEnd_2076935 : Nat := 4983230072969 + 3 ^ 40 * 2076935 * 2
def baseEnd_2076935 : Nat := 473984863620416318204825

theorem tailTrace_2076935 : CollatzResearch.WordTrace tailWord_2076935 prefixEnd_2076935 473984863620416318204825 := by
  unfold tailWord_2076935
  simp only [CollatzResearch.WordTrace]
  refine ⟨75752042730626682103024259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50501361820417788068682839 75752042730626682103024259)
  ·
    refine ⟨113628064095940023154536389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75752042730626682103024259 113628064095940023154536389)
    ·
      refine ⟨21305262017988754341475573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113628064095940023154536389 21305262017988754341475573)
      ·
        refine ⟨1997368314186445719513335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21305262017988754341475573 1997368314186445719513335)
        ·
          refine ⟨2996052471279668579270003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997368314186445719513335 2996052471279668579270003)
          ·
            refine ⟨4494078706919502868905005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996052471279668579270003 4494078706919502868905005)
            ·
              refine ⟨1685279515094813575839377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4494078706919502868905005 1685279515094813575839377)
              ·
                refine ⟨1263959636321110181879533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685279515094813575839377 1263959636321110181879533)
                ·
                  refine ⟨473984863620416318204825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263959636321110181879533 473984863620416318204825)
                  ·
                    rfl

theorem cell21_2076935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].length) (baseStart_2076935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2076935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2076935 prefixEnd_2076935 := by exact prefixLift 2076935
  have htrace : WordTrace (prefixWord ++ tailWord_2076935) baseStart_2076935 baseEnd_2076935 := by
    simpa [prefixWord, tailWord_2076935, baseEnd_2076935] using wordTrace_append hprefix tailTrace_2076935
  have hstable : (prefixWord ++ tailWord_2076935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076935).length < 2 ^ (prefixWord ++ tailWord_2076935).sum := by decide
  have hdescent : baseEnd_2076935 < baseStart_2076935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077033 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_2077033 : Nat := 118140960795 + 2077033 * 2 ^ 59
def prefixEnd_2077033 : Nat := 4983230072969 + 3 ^ 40 * 2077033 * 2
def baseEnd_2077033 : Nat := 474007228555589925571291

theorem tailTrace_2077033 : CollatzResearch.WordTrace tailWord_2077033 prefixEnd_2077033 474007228555589925571291 := by
  unfold tailWord_2077033
  simp only [CollatzResearch.WordTrace]
  refine ⟨75755617084271644840091753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50503744722847763226727835 75755617084271644840091753)
  ·
    refine ⟨56816712813203733630068815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75755617084271644840091753 56816712813203733630068815)
    ·
      refine ⟨85225069219805600445103223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816712813203733630068815 85225069219805600445103223)
      ·
        refine ⟨127837603829708400667654835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85225069219805600445103223 127837603829708400667654835)
        ·
          refine ⟨191756405744562601001482253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127837603829708400667654835 191756405744562601001482253)
          ·
            refine ⟨71908652154210975375555845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191756405744562601001482253 71908652154210975375555845)
            ·
              refine ⟨13482872278914557882916721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71908652154210975375555845 13482872278914557882916721)
              ·
                refine ⟨10112154209185918412187541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13482872278914557882916721 10112154209185918412187541)
                ·
                  refine ⟨474007228555589925571291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10112154209185918412187541 474007228555589925571291)
                  ·
                    rfl

theorem cell21_2077033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_2077033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077033 prefixEnd_2077033 := by exact prefixLift 2077033
  have htrace : WordTrace (prefixWord ++ tailWord_2077033) baseStart_2077033 baseEnd_2077033 := by
    simpa [prefixWord, tailWord_2077033, baseEnd_2077033] using wordTrace_append hprefix tailTrace_2077033
  have hstable : (prefixWord ++ tailWord_2077033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077033).length < 2 ^ (prefixWord ++ tailWord_2077033).sum := by decide
  have hdescent : baseEnd_2077033 < baseStart_2077033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077064 : List Nat := [2, 1, 3, 3, 1, 1, 2, 8]
def baseStart_2077064 : Nat := 118140960795 + 2077064 * 2 ^ 59
def prefixEnd_2077064 : Nat := 4983230072969 + 3 ^ 40 * 2077064 * 2
def baseEnd_2077064 : Nat := 158004767725980253518187

theorem tailTrace_2077064 : CollatzResearch.WordTrace tailWord_2077064 prefixEnd_2077064 158004767725980253518187 := by
  unfold tailWord_2077064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37878373873579668567235123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50504498498106224756313497 37878373873579668567235123)
  ·
    refine ⟨56817560810369502850852685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37878373873579668567235123 56817560810369502850852685)
    ·
      refine ⟨21306585303888563569069757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56817560810369502850852685 21306585303888563569069757)
      ·
        refine ⟨7989969488958211338401159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21306585303888563569069757 7989969488958211338401159)
        ·
          refine ⟨11984954233437317007601739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989969488958211338401159 11984954233437317007601739)
          ·
            refine ⟨17977431350155975511402609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984954233437317007601739 17977431350155975511402609)
            ·
              refine ⟨13483073512616981633551957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17977431350155975511402609 13483073512616981633551957)
              ·
                refine ⟨158004767725980253518187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13483073512616981633551957 158004767725980253518187)
                ·
                  rfl

theorem cell21_2077064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_2077064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077064 prefixEnd_2077064 := by exact prefixLift 2077064
  have htrace : WordTrace (prefixWord ++ tailWord_2077064) baseStart_2077064 baseEnd_2077064 := by
    simpa [prefixWord, tailWord_2077064, baseEnd_2077064] using wordTrace_append hprefix tailTrace_2077064
  have hstable : (prefixWord ++ tailWord_2077064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077064).length < 2 ^ (prefixWord ++ tailWord_2077064).sum := by decide
  have hdescent : baseEnd_2077064 < baseStart_2077064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077067 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 4]
def baseStart_2077067 : Nat := 118140960795 + 2077067 * 2 ^ 59
def prefixEnd_2077067 : Nat := 4983230072969 + 3 ^ 40 * 2077067 * 2
def baseEnd_2077067 : Nat := 474014987818813422004555

theorem tailTrace_2077067 : CollatzResearch.WordTrace tailWord_2077067 prefixEnd_2077067 474014987818813422004555 := by
  unfold tailWord_2077067
  simp only [CollatzResearch.WordTrace]
  refine ⟨75756857166148468646829455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50504571444098979097886303 75756857166148468646829455)
  ·
    refine ⟨113635285749222702970244183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75756857166148468646829455 113635285749222702970244183)
    ·
      refine ⟨170452928623834054455366275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113635285749222702970244183 170452928623834054455366275)
      ·
        refine ⟨255679392935751081683049413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170452928623834054455366275 255679392935751081683049413)
        ·
          refine ⟨47939886175453327815571765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255679392935751081683049413 47939886175453327815571765)
          ·
            refine ⟨4494364328948749482709853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47939886175453327815571765 4494364328948749482709853)
            ·
              refine ⟨1685386623355781056016195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4494364328948749482709853 1685386623355781056016195)
              ·
                refine ⟨2528079935033671584024293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685386623355781056016195 2528079935033671584024293)
                ·
                  refine ⟨474014987818813422004555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528079935033671584024293 474014987818813422004555)
                  ·
                    rfl

theorem cell21_2077067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_2077067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077067 prefixEnd_2077067 := by exact prefixLift 2077067
  have htrace : WordTrace (prefixWord ++ tailWord_2077067) baseStart_2077067 baseEnd_2077067 := by
    simpa [prefixWord, tailWord_2077067, baseEnd_2077067] using wordTrace_append hprefix tailTrace_2077067
  have hstable : (prefixWord ++ tailWord_2077067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077067).length < 2 ^ (prefixWord ++ tailWord_2077067).sum := by decide
  have hdescent : baseEnd_2077067 < baseStart_2077067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077157 : List Nat := [1, 3, 1, 5, 3, 8]
def baseStart_2077157 : Nat := 118140960795 + 2077157 * 2 ^ 59
def prefixEnd_2077157 : Nat := 4983230072969 + 3 ^ 40 * 2077157 * 2
def baseEnd_2077157 : Nat := 17556871372036787611273

theorem tailTrace_2077157 : CollatzResearch.WordTrace tailWord_2077157 prefixEnd_2077157 17556871372036787611273 := by
  unfold tailWord_2077157
  simp only [CollatzResearch.WordTrace]
  refine ⟨75760139735822414017605725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50506759823881609345070483 75760139735822414017605725)
  ·
    refine ⟨28410052400933405256602147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75760139735822414017605725 28410052400933405256602147)
    ·
      refine ⟨42615078601400107884903221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28410052400933405256602147 42615078601400107884903221)
      ·
        refine ⟨3995163618881260114209677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42615078601400107884903221 3995163618881260114209677)
        ·
          refine ⟨1498186357080472542828629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3995163618881260114209677 1498186357080472542828629)
          ·
            refine ⟨17556871372036787611273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1498186357080472542828629 17556871372036787611273)
            ·
              rfl

theorem cell21_2077157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 8].length) (baseStart_2077157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077157 prefixEnd_2077157 := by exact prefixLift 2077157
  have htrace : WordTrace (prefixWord ++ tailWord_2077157) baseStart_2077157 baseEnd_2077157 := by
    simpa [prefixWord, tailWord_2077157, baseEnd_2077157] using wordTrace_append hprefix tailTrace_2077157
  have hstable : (prefixWord ++ tailWord_2077157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077157).length < 2 ^ (prefixWord ++ tailWord_2077157).sum := by decide
  have hdescent : baseEnd_2077157 < baseStart_2077157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077188 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2077188 : Nat := 118140960795 + 2077188 * 2 ^ 59
def prefixEnd_2077188 : Nat := 4983230072969 + 3 ^ 40 * 2077188 * 2
def baseEnd_2077188 : Nat := 474042601667344100487641

theorem tailTrace_2077188 : CollatzResearch.WordTrace tailWord_2077188 prefixEnd_2077188 474042601667344100487641 := by
  unfold tailWord_2077188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37880635199355053155992109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50507513599140070874656145 37880635199355053155992109)
  ·
    refine ⟨14205238199758144933497041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37880635199355053155992109 14205238199758144933497041)
    ·
      refine ⟨10653928649818608700122781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14205238199758144933497041 10653928649818608700122781)
      ·
        refine ⟨3995223243681978262546043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10653928649818608700122781 3995223243681978262546043)
        ·
          refine ⟨5992834865522967393819065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995223243681978262546043 5992834865522967393819065)
          ·
            refine ⟨4494626149142225545364299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5992834865522967393819065 4494626149142225545364299)
            ·
              refine ⟨6741939223713338318046449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494626149142225545364299 6741939223713338318046449)
              ·
                refine ⟨5056454417785003738534837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741939223713338318046449 5056454417785003738534837)
                ·
                  refine ⟨474042601667344100487641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056454417785003738534837 474042601667344100487641)
                  ·
                    rfl

theorem cell21_2077188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2077188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077188 prefixEnd_2077188 := by exact prefixLift 2077188
  have htrace : WordTrace (prefixWord ++ tailWord_2077188) baseStart_2077188 baseEnd_2077188 := by
    simpa [prefixWord, tailWord_2077188, baseEnd_2077188] using wordTrace_append hprefix tailTrace_2077188
  have hstable : (prefixWord ++ tailWord_2077188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077188).length < 2 ^ (prefixWord ++ tailWord_2077188).sum := by decide
  have hdescent : baseEnd_2077188 < baseStart_2077188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077219 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_2077219 : Nat := 118140960795 + 2077219 * 2 ^ 59
def prefixEnd_2077219 : Nat := 4983230072969 + 3 ^ 40 * 2077219 * 2
def baseEnd_2077219 : Nat := 474049676289694935470911

theorem tailTrace_2077219 : CollatzResearch.WordTrace tailWord_2077219 prefixEnd_2077219 474049676289694935470911 := by
  unfold tailWord_2077219
  simp only [CollatzResearch.WordTrace]
  refine ⟨75762401061597798606362711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50508267374398532404241807 75762401061597798606362711)
  ·
    refine ⟨113643601592396697909544067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75762401061597798606362711 113643601592396697909544067)
    ·
      refine ⟨170465402388595046864316101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113643601592396697909544067 170465402388595046864316101)
      ·
        refine ⟨31962262947861571287059269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170465402388595046864316101 31962262947861571287059269)
        ·
          refine ⟨5992924302724044616323613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31962262947861571287059269 5992924302724044616323613)
          ·
            refine ⟨2247346613521516731121355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5992924302724044616323613 2247346613521516731121355)
            ·
              refine ⟨3371019920282275096682033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247346613521516731121355 3371019920282275096682033)
              ·
                refine ⟨2528264940211706322511525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371019920282275096682033 2528264940211706322511525)
                ·
                  refine ⟨474049676289694935470911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528264940211706322511525 474049676289694935470911)
                  ·
                    rfl

theorem cell21_2077219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_2077219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077219 prefixEnd_2077219 := by exact prefixLift 2077219
  have htrace : WordTrace (prefixWord ++ tailWord_2077219) baseStart_2077219 baseEnd_2077219 := by
    simpa [prefixWord, tailWord_2077219, baseEnd_2077219] using wordTrace_append hprefix tailTrace_2077219
  have hstable : (prefixWord ++ tailWord_2077219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077219).length < 2 ^ (prefixWord ++ tailWord_2077219).sum := by decide
  have hdescent : baseEnd_2077219 < baseStart_2077219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077281 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 3]
def baseStart_2077281 : Nat := 118140960795 + 2077281 * 2 ^ 59
def prefixEnd_2077281 : Nat := 4983230072969 + 3 ^ 40 * 2077281 * 2
def baseEnd_2077281 : Nat := 474063825534396605437451

theorem tailTrace_2077281 : CollatzResearch.WordTrace tailWord_2077281 prefixEnd_2077281 474063825534396605437451 := by
  unfold tailWord_2077281
  simp only [CollatzResearch.WordTrace]
  refine ⟨75764662387373183195119697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50509774924915455463413131 75764662387373183195119697)
  ·
    refine ⟨56823496790529887396339773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75764662387373183195119697 56823496790529887396339773)
    ·
      refine ⟨21308811296448707773627415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56823496790529887396339773 21308811296448707773627415)
      ·
        refine ⟨31963216944673061660441123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308811296448707773627415 31963216944673061660441123)
        ·
          refine ⟨47944825417009592490661685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31963216944673061660441123 47944825417009592490661685)
          ·
            refine ⟨4494827382844649295999533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47944825417009592490661685 4494827382844649295999533)
            ·
              refine ⟨1685560268566743485999825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4494827382844649295999533 1685560268566743485999825)
              ·
                refine ⟨1264170201425057614499869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685560268566743485999825 1264170201425057614499869)
                ·
                  refine ⟨474063825534396605437451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264170201425057614499869 474063825534396605437451)
                  ·
                    rfl

theorem cell21_2077281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_2077281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077281 prefixEnd_2077281 := by exact prefixLift 2077281
  have htrace : WordTrace (prefixWord ++ tailWord_2077281) baseStart_2077281 baseEnd_2077281 := by
    simpa [prefixWord, tailWord_2077281, baseEnd_2077281] using wordTrace_append hprefix tailTrace_2077281
  have hstable : (prefixWord ++ tailWord_2077281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077281).length < 2 ^ (prefixWord ++ tailWord_2077281).sum := by decide
  have hdescent : baseEnd_2077281 < baseStart_2077281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077399 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_2077399 : Nat := 118140960795 + 2077399 * 2 ^ 59
def prefixEnd_2077399 : Nat := 4983230072969 + 3 ^ 40 * 2077399 * 2
def baseEnd_2077399 : Nat := 474090754742054622470543

theorem tailTrace_2077399 : CollatzResearch.WordTrace tailWord_2077399 prefixEnd_2077399 474090754742054622470543 := by
  unfold tailWord_2077399
  simp only [CollatzResearch.WordTrace]
  refine ⟨75768966200945689347915251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50512644133963792898610167 75768966200945689347915251)
  ·
    refine ⟨113653449301418534021872877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75768966200945689347915251 113653449301418534021872877)
    ·
      refine ⟨42620043488031950258202329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113653449301418534021872877 42620043488031950258202329)
      ·
        refine ⟨31965032616023962693651747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42620043488031950258202329 31965032616023962693651747)
        ·
          refine ⟨47947548924035944040477621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31965032616023962693651747 47947548924035944040477621)
          ·
            refine ⟨4495082711628369753794777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47947548924035944040477621 4495082711628369753794777)
            ·
              refine ⟨3371312033721277315346083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495082711628369753794777 3371312033721277315346083)
              ·
                refine ⟨5056968050581915973019125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371312033721277315346083 5056968050581915973019125)
                ·
                  refine ⟨474090754742054622470543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056968050581915973019125 474090754742054622470543)
                  ·
                    rfl

theorem cell21_2077399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_2077399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077399 prefixEnd_2077399 := by exact prefixLift 2077399
  have htrace : WordTrace (prefixWord ++ tailWord_2077399) baseStart_2077399 baseEnd_2077399 := by
    simpa [prefixWord, tailWord_2077399, baseEnd_2077399] using wordTrace_append hprefix tailTrace_2077399
  have hstable : (prefixWord ++ tailWord_2077399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077399).length < 2 ^ (prefixWord ++ tailWord_2077399).sum := by decide
  have hdescent : baseEnd_2077399 < baseStart_2077399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077503 : List Nat := [1, 1, 2, 2, 5, 10]
def baseStart_2077503 : Nat := 118140960795 + 2077503 * 2 ^ 59
def prefixEnd_2077503 : Nat := 4983230072969 + 3 ^ 40 * 2077503 * 2
def baseEnd_2077503 : Nat := 17559795887369390842111

theorem tailTrace_2077503 : CollatzResearch.WordTrace tailWord_2077503 prefixEnd_2077503 17559795887369390842111 := by
  unfold tailWord_2077503
  simp only [CollatzResearch.WordTrace]
  refine ⟨75772759392568915109701163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50515172928379276739800775 75772759392568915109701163)
  ·
    refine ⟨113659139088853372664551745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75772759392568915109701163 113659139088853372664551745)
    ·
      refine ⟨85244354316640029498413809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113659139088853372664551745 85244354316640029498413809)
      ·
        refine ⟨63933265737480022123810357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85244354316640029498413809 63933265737480022123810357)
        ·
          refine ⟨5993743662888752074107221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63933265737480022123810357 5993743662888752074107221)
          ·
            refine ⟨17559795887369390842111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5993743662888752074107221 17559795887369390842111)
            ·
              rfl

theorem cell21_2077503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 10].length) (baseStart_2077503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077503 prefixEnd_2077503 := by exact prefixLift 2077503
  have htrace : WordTrace (prefixWord ++ tailWord_2077503) baseStart_2077503 baseEnd_2077503 := by
    simpa [prefixWord, tailWord_2077503, baseEnd_2077503] using wordTrace_append hprefix tailTrace_2077503
  have hstable : (prefixWord ++ tailWord_2077503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077503).length < 2 ^ (prefixWord ++ tailWord_2077503).sum := by decide
  have hdescent : baseEnd_2077503 < baseStart_2077503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077678 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2077678 : Nat := 118140960795 + 2077678 * 2 ^ 59
def prefixEnd_2077678 : Nat := 4983230072969 + 3 ^ 40 * 2077678 * 2
def baseEnd_2077678 : Nat := 474154426343212137319973

theorem tailTrace_2077678 : CollatzResearch.WordTrace tailWord_2077678 prefixEnd_2077678 474154426343212137319973 := by
  unfold tailWord_2077678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472392770866864999665211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50519428111289946664881125 9472392770866864999665211)
  ·
    refine ⟨14208589156300297499497817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9472392770866864999665211 14208589156300297499497817)
    ·
      refine ⟨10656441867225223124623363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14208589156300297499497817 10656441867225223124623363)
      ·
        refine ⟨15984662800837834686935045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656441867225223124623363 15984662800837834686935045)
        ·
          refine ⟨2997124275157094003800321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15984662800837834686935045 2997124275157094003800321)
          ·
            refine ⟨2247843206367820502850241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997124275157094003800321 2247843206367820502850241)
            ·
              refine ⟨1685882404775865377137681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247843206367820502850241 1685882404775865377137681)
              ·
                refine ⟨1264411803581899032853261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685882404775865377137681 1264411803581899032853261)
                ·
                  refine ⟨474154426343212137319973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264411803581899032853261 474154426343212137319973)
                  ·
                    rfl

theorem cell21_2077678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2077678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077678 prefixEnd_2077678 := by exact prefixLift 2077678
  have htrace : WordTrace (prefixWord ++ tailWord_2077678) baseStart_2077678 baseEnd_2077678 := by
    simpa [prefixWord, tailWord_2077678, baseEnd_2077678] using wordTrace_append hprefix tailTrace_2077678
  have hstable : (prefixWord ++ tailWord_2077678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077678).length < 2 ^ (prefixWord ++ tailWord_2077678).sum := by decide
  have hdescent : baseEnd_2077678 < baseStart_2077678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077720 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_2077720 : Nat := 118140960795 + 2077720 * 2 ^ 59
def prefixEnd_2077720 : Nat := 4983230072969 + 3 ^ 40 * 2077720 * 2
def baseEnd_2077720 : Nat := 474164011315429397619887

theorem tailTrace_2077720 : CollatzResearch.WordTrace tailWord_2077720 prefixEnd_2077720 474164011315429397619887 := by
  unfold tailWord_2077720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890337016391380585175307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50520449355188507446900409 37890337016391380585175307)
  ·
    refine ⟨56835505524587070877762961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37890337016391380585175307 56835505524587070877762961)
    ·
      refine ⟨42626629143440303158322221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56835505524587070877762961 42626629143440303158322221)
      ·
        refine ⟨15984985928790113684370833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42626629143440303158322221 15984985928790113684370833)
        ·
          refine ⟨11988739446592585263278125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15984985928790113684370833 11988739446592585263278125)
          ·
            refine ⟨4495777292472219473729297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11988739446592585263278125 4495777292472219473729297)
            ·
              refine ⟨3371832969354164605296973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495777292472219473729297 3371832969354164605296973)
              ·
                refine ⟨1264437363507811726986365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3371832969354164605296973 1264437363507811726986365)
                ·
                  refine ⟨474164011315429397619887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264437363507811726986365 474164011315429397619887)
                  ·
                    rfl

theorem cell21_2077720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_2077720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077720 prefixEnd_2077720 := by exact prefixLift 2077720
  have htrace : WordTrace (prefixWord ++ tailWord_2077720) baseStart_2077720 baseEnd_2077720 := by
    simpa [prefixWord, tailWord_2077720, baseEnd_2077720] using wordTrace_append hprefix tailTrace_2077720
  have hstable : (prefixWord ++ tailWord_2077720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077720).length < 2 ^ (prefixWord ++ tailWord_2077720).sum := by decide
  have hdescent : baseEnd_2077720 < baseStart_2077720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077731 : List Nat := [1, 1, 1, 4, 3, 3, 8]
def baseStart_2077731 : Nat := 118140960795 + 2077731 * 2 ^ 59
def prefixEnd_2077731 : Nat := 4983230072969 + 3 ^ 40 * 2077731 * 2
def baseEnd_2077731 : Nat := 52685169073921758104059

theorem tailTrace_2077731 : CollatzResearch.WordTrace tailWord_2077731 prefixEnd_2077731 52685169073921758104059 := by
  unfold tailWord_2077731
  simp only [CollatzResearch.WordTrace]
  refine ⟨75781075235742910049001047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50520716823828606699334031 75781075235742910049001047)
  ·
    refine ⟨113671612853614365073501571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75781075235742910049001047 113671612853614365073501571)
    ·
      refine ⟨170507419280421547610252357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113671612853614365073501571 170507419280421547610252357)
      ·
        refine ⟨31970141115079040176922317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170507419280421547610252357 31970141115079040176922317)
        ·
          refine ⟨11988802918154640066345869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31970141115079040176922317 11988802918154640066345869)
          ·
            refine ⟨4495801094307990024879701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11988802918154640066345869 4495801094307990024879701)
            ·
              refine ⟨52685169073921758104059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4495801094307990024879701 52685169073921758104059)
              ·
                rfl

theorem cell21_2077731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_2077731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077731 prefixEnd_2077731 := by exact prefixLift 2077731
  have htrace : WordTrace (prefixWord ++ tailWord_2077731) baseStart_2077731 baseEnd_2077731 := by
    simpa [prefixWord, tailWord_2077731, baseEnd_2077731] using wordTrace_append hprefix tailTrace_2077731
  have hstable : (prefixWord ++ tailWord_2077731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077731).length < 2 ^ (prefixWord ++ tailWord_2077731).sum := by decide
  have hdescent : baseEnd_2077731 < baseStart_2077731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077782 : List Nat := [5, 2, 2, 1, 2, 2, 7]
def baseStart_2077782 : Nat := 118140960795 + 2077782 * 2 ^ 59
def prefixEnd_2077782 : Nat := 4983230072969 + 3 ^ 40 * 2077782 * 2
def baseEnd_2077782 : Nat := 52686462284459007509603

theorem tailTrace_2077782 : CollatzResearch.WordTrace tailWord_2077782 prefixEnd_2077782 52686462284459007509603 := by
  unfold tailWord_2077782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736433459909884109944225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50521956905705430506071733 4736433459909884109944225)
  ·
    refine ⟨3552325094932413082458169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4736433459909884109944225 3552325094932413082458169)
    ·
      refine ⟨2664243821199309811843627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552325094932413082458169 2664243821199309811843627)
      ·
        refine ⟨3996365731798964717765441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664243821199309811843627 3996365731798964717765441)
        ·
          refine ⟨2997274298849223538324081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3996365731798964717765441 2997274298849223538324081)
          ·
            refine ⟨2247955724136917653743061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997274298849223538324081 2247955724136917653743061)
            ·
              refine ⟨52686462284459007509603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2247955724136917653743061 52686462284459007509603)
              ·
                rfl

theorem cell21_2077782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 7].length) (baseStart_2077782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077782 prefixEnd_2077782 := by exact prefixLift 2077782
  have htrace : WordTrace (prefixWord ++ tailWord_2077782) baseStart_2077782 baseEnd_2077782 := by
    simpa [prefixWord, tailWord_2077782, baseEnd_2077782] using wordTrace_append hprefix tailTrace_2077782
  have hstable : (prefixWord ++ tailWord_2077782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077782).length < 2 ^ (prefixWord ++ tailWord_2077782).sum := by decide
  have hdescent : baseEnd_2077782 < baseStart_2077782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077807 : List Nat := [1, 1, 2, 1, 3, 3, 4, 6]
def baseStart_2077807 : Nat := 118140960795 + 2077807 * 2 ^ 59
def prefixEnd_2077807 : Nat := 4983230072969 + 3 ^ 40 * 2077807 * 2
def baseEnd_2077807 : Nat := 158061288633578859889903

theorem tailTrace_2077807 : CollatzResearch.WordTrace tailWord_2077807 prefixEnd_2077807 158061288633578859889903 := by
  unfold tailWord_2077807
  simp only [CollatzResearch.WordTrace]
  refine ⟨75783847183467575028767675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50522564788978383352511783 75783847183467575028767675)
  ·
    refine ⟨113675770775201362543151513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75783847183467575028767675 113675770775201362543151513)
    ·
      refine ⟨85256828081401021907363635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113675770775201362543151513 85256828081401021907363635)
      ·
        refine ⟨127885242122101532861045453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85256828081401021907363635 127885242122101532861045453)
        ·
          refine ⟨47956965795788074822892045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127885242122101532861045453 47956965795788074822892045)
          ·
            refine ⟨17983862173420528058584517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47956965795788074822892045 17983862173420528058584517)
            ·
              refine ⟨3371974157516349010984597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17983862173420528058584517 3371974157516349010984597)
              ·
                refine ⟨158061288633578859889903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3371974157516349010984597 158061288633578859889903)
                ·
                  rfl

theorem cell21_2077807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_2077807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077807 prefixEnd_2077807 := by exact prefixLift 2077807
  have htrace : WordTrace (prefixWord ++ tailWord_2077807) baseStart_2077807 baseEnd_2077807 := by
    simpa [prefixWord, tailWord_2077807, baseEnd_2077807] using wordTrace_append hprefix tailTrace_2077807
  have hstable : (prefixWord ++ tailWord_2077807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077807).length < 2 ^ (prefixWord ++ tailWord_2077807).sum := by decide
  have hdescent : baseEnd_2077807 < baseStart_2077807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077858 : List Nat := [3, 3, 1, 3, 3, 1, 1, 6]
def baseStart_2077858 : Nat := 118140960795 + 2077858 * 2 ^ 59
def prefixEnd_2077858 : Nat := 4983230072969 + 3 ^ 40 * 2077858 * 2
def baseEnd_2077858 : Nat := 158065168265190608106535

theorem tailTrace_2077858 : CollatzResearch.WordTrace tailWord_2077858 prefixEnd_2077858 158065168265190608106535 := by
  unfold tailWord_2077858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946426826570702684718557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50523804870855207159249485 18946426826570702684718557)
  ·
    refine ⟨7104910059964013506769459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18946426826570702684718557 7104910059964013506769459)
    ·
      refine ⟨10657365089946020260154189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104910059964013506769459 10657365089946020260154189)
      ·
        refine ⟨3996511908729757597557821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10657365089946020260154189 3996511908729757597557821)
        ·
          refine ⟨1498691965773659099084183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3996511908729757597557821 1498691965773659099084183)
          ·
            refine ⟨2248037948660488648626275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498691965773659099084183 2248037948660488648626275)
            ·
              refine ⟨3372056922990732972939413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248037948660488648626275 3372056922990732972939413)
              ·
                refine ⟨158065168265190608106535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3372056922990732972939413 158065168265190608106535)
                ·
                  rfl

theorem cell21_2077858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_2077858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077858 prefixEnd_2077858 := by exact prefixLift 2077858
  have htrace : WordTrace (prefixWord ++ tailWord_2077858) baseStart_2077858 baseEnd_2077858 := by
    simpa [prefixWord, tailWord_2077858, baseEnd_2077858] using wordTrace_append hprefix tailTrace_2077858
  have hstable : (prefixWord ++ tailWord_2077858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077858).length < 2 ^ (prefixWord ++ tailWord_2077858).sum := by decide
  have hdescent : baseEnd_2077858 < baseStart_2077858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077889 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 3]
def baseStart_2077889 : Nat := 118140960795 + 2077889 * 2 ^ 59
def prefixEnd_2077889 : Nat := 4983230072969 + 3 ^ 40 * 2077889 * 2
def baseEnd_2077889 : Nat := 474202579417922659302875

theorem tailTrace_2077889 : CollatzResearch.WordTrace tailWord_2077889 prefixEnd_2077889 474202579417922659302875 := by
  unfold tailWord_2077889
  simp only [CollatzResearch.WordTrace]
  refine ⟨75786837969170503033252721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50524558646113668688835147 75786837969170503033252721)
  ·
    refine ⟨56840128476877877274939541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75786837969170503033252721 56840128476877877274939541)
    ·
      refine ⟨2664381022353650497262791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56840128476877877274939541 2664381022353650497262791)
      ·
        refine ⟨3996571533530475745894187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664381022353650497262791 3996571533530475745894187)
        ·
          refine ⟨5994857300295713618841281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996571533530475745894187 5994857300295713618841281)
          ·
            refine ⟨4496142975221785214130961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994857300295713618841281 4496142975221785214130961)
            ·
              refine ⟨3372107231416338910598221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496142975221785214130961 3372107231416338910598221)
              ·
                refine ⟨1264540211781127091474333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3372107231416338910598221 1264540211781127091474333)
                ·
                  refine ⟨474202579417922659302875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264540211781127091474333 474202579417922659302875)
                  ·
                    rfl

theorem cell21_2077889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_2077889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077889 prefixEnd_2077889 := by exact prefixLift 2077889
  have htrace : WordTrace (prefixWord ++ tailWord_2077889) baseStart_2077889 baseEnd_2077889 := by
    simpa [prefixWord, tailWord_2077889, baseEnd_2077889] using wordTrace_append hprefix tailTrace_2077889
  have hstable : (prefixWord ++ tailWord_2077889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077889).length < 2 ^ (prefixWord ++ tailWord_2077889).sum := by decide
  have hdescent : baseEnd_2077889 < baseStart_2077889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077940 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2077940 : Nat := 118140960795 + 2077940 * 2 ^ 59
def prefixEnd_2077940 : Nat := 4983230072969 + 3 ^ 40 * 2077940 * 2
def baseEnd_2077940 : Nat := 474214218312757903952771

theorem tailTrace_2077940 : CollatzResearch.WordTrace tailWord_2077940 prefixEnd_2077940 474214218312757903952771 := by
  unfold tailWord_2077940
  simp only [CollatzResearch.WordTrace]
  refine ⟨37894349045992869371679637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50525798727990492495572849 37894349045992869371679637)
  ·
    refine ⟨1776297611530915751797483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37894349045992869371679637 1776297611530915751797483)
    ·
      refine ⟨2664446417296373627696225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776297611530915751797483 2664446417296373627696225)
      ·
        refine ⟨1998334812972280220772169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2664446417296373627696225 1998334812972280220772169)
        ·
          refine ⟨1498751109729210165579127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998334812972280220772169 1498751109729210165579127)
          ·
            refine ⟨2248126664593815248368691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498751109729210165579127 2248126664593815248368691)
            ·
              refine ⟨3372189996890722872553037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248126664593815248368691 3372189996890722872553037)
              ·
                refine ⟨1264571248834021077207389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3372189996890722872553037 1264571248834021077207389)
                ·
                  refine ⟨474214218312757903952771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264571248834021077207389 474214218312757903952771)
                  ·
                    rfl

theorem cell21_2077940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2077940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2077940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2077940 prefixEnd_2077940 := by exact prefixLift 2077940
  have htrace : WordTrace (prefixWord ++ tailWord_2077940) baseStart_2077940 baseEnd_2077940 := by
    simpa [prefixWord, tailWord_2077940, baseEnd_2077940] using wordTrace_append hprefix tailTrace_2077940
  have hstable : (prefixWord ++ tailWord_2077940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077940).length < 2 ^ (prefixWord ++ tailWord_2077940).sum := by decide
  have hdescent : baseEnd_2077940 < baseStart_2077940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078018 : List Nat := [3, 18]
def baseStart_2078018 : Nat := 118140960795 + 2078018 * 2 ^ 59
def prefixEnd_2078018 : Nat := 4983230072969 + 3 ^ 40 * 2078018 * 2
def baseEnd_2078018 : Nat := 216841343838796114153

theorem tailTrace_2078018 : CollatzResearch.WordTrace tailWord_2078018 prefixEnd_2078018 216841343838796114153 := by
  unfold tailWord_2078018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947885746425789516174677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50527695323802105376465805 18947885746425789516174677)
  ·
    refine ⟨216841343838796114153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 18 18947885746425789516174677 216841343838796114153)
    ·
      rfl

theorem cell21_2078018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 18].length) (baseStart_2078018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078018 prefixEnd_2078018 := by exact prefixLift 2078018
  have htrace : WordTrace (prefixWord ++ tailWord_2078018) baseStart_2078018 baseEnd_2078018 := by
    simpa [prefixWord, tailWord_2078018, baseEnd_2078018] using wordTrace_append hprefix tailTrace_2078018
  have hstable : (prefixWord ++ tailWord_2078018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078018).length < 2 ^ (prefixWord ++ tailWord_2078018).sum := by decide
  have hdescent : baseEnd_2078018 < baseStart_2078018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078052 : List Nat := [2, 3, 1, 1, 3, 3, 3, 5]
def baseStart_2078052 : Nat := 118140960795 + 2078052 * 2 ^ 59
def prefixEnd_2078052 : Nat := 4983230072969 + 3 ^ 40 * 2078052 * 2
def baseEnd_2078052 : Nat := 158079926079556866028625

theorem tailTrace_2078052 : CollatzResearch.WordTrace tailWord_2078052 prefixEnd_2078052 158079926079556866028625 := by
  unfold tailWord_2078052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896391533789990935718205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50528522045053321247624273 37896391533789990935718205)
  ·
    refine ⟨14211146825171246600894327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37896391533789990935718205 14211146825171246600894327)
    ·
      refine ⟨21316720237756869901341491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211146825171246600894327 21316720237756869901341491)
      ·
        refine ⟨31975080356635304852012237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21316720237756869901341491 31975080356635304852012237)
        ·
          refine ⟨11990655133738239319504589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31975080356635304852012237 11990655133738239319504589)
          ·
            refine ⟨4496495675151839744814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11990655133738239319504589 4496495675151839744814221)
            ·
              refine ⟨1686185878181939904305333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4496495675151839744814221 1686185878181939904305333)
              ·
                refine ⟨158079926079556866028625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686185878181939904305333 158079926079556866028625)
                ·
                  rfl

theorem cell21_2078052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_2078052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078052 prefixEnd_2078052 := by exact prefixLift 2078052
  have htrace : WordTrace (prefixWord ++ tailWord_2078052) baseStart_2078052 baseEnd_2078052 := by
    simpa [prefixWord, tailWord_2078052, baseEnd_2078052] using wordTrace_append hprefix tailTrace_2078052
  have hstable : (prefixWord ++ tailWord_2078052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078052).length < 2 ^ (prefixWord ++ tailWord_2078052).sum := by decide
  have hdescent : baseEnd_2078052 < baseStart_2078052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078083 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 3]
def baseStart_2078083 : Nat := 118140960795 + 2078083 * 2 ^ 59
def prefixEnd_2078083 : Nat := 4983230072969 + 3 ^ 40 * 2078083 * 2
def baseEnd_2078083 : Nat := 474246852861021433069145

theorem tailTrace_2078083 : CollatzResearch.WordTrace tailWord_2078083 prefixEnd_2078083 474246852861021433069145 := by
  unfold tailWord_2078083
  simp only [CollatzResearch.WordTrace]
  refine ⟨75793913730467674165814903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50529275820311782777209935 75793913730467674165814903)
  ·
    refine ⟨113690870595701511248722355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75793913730467674165814903 113690870595701511248722355)
    ·
      refine ⟨170536305893552266873083533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113690870595701511248722355 170536305893552266873083533)
      ·
        refine ⟨63951114710082100077406325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170536305893552266873083533 63951114710082100077406325)
        ·
          refine ⟨5995417004070196882256843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63951114710082100077406325 5995417004070196882256843)
          ·
            refine ⟨8993125506105295323385265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995417004070196882256843 8993125506105295323385265)
            ·
              refine ⟨6744844129578971492538949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993125506105295323385265 6744844129578971492538949)
              ·
                refine ⟨1264658274296057154851053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6744844129578971492538949 1264658274296057154851053)
                ·
                  refine ⟨474246852861021433069145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264658274296057154851053 474246852861021433069145)
                  ·
                    rfl

theorem cell21_2078083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].length) (baseStart_2078083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078083 prefixEnd_2078083 := by exact prefixLift 2078083
  have htrace : WordTrace (prefixWord ++ tailWord_2078083) baseStart_2078083 baseEnd_2078083 := by
    simpa [prefixWord, tailWord_2078083, baseEnd_2078083] using wordTrace_append hprefix tailTrace_2078083
  have hstable : (prefixWord ++ tailWord_2078083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078083).length < 2 ^ (prefixWord ++ tailWord_2078083).sum := by decide
  have hdescent : baseEnd_2078083 < baseStart_2078083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078111 : List Nat := [1, 1, 2, 5, 1, 3, 1, 7]
def baseStart_2078111 : Nat := 118140960795 + 2078111 * 2 ^ 59
def prefixEnd_2078111 : Nat := 4983230072969 + 3 ^ 40 * 2078111 * 2
def baseEnd_2078111 : Nat := 158084414280833202200807

theorem tailTrace_2078111 : CollatzResearch.WordTrace tailWord_2078111 prefixEnd_2078111 158084414280833202200807 := by
  unfold tailWord_2078111
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794934974366234947834187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50529956649577489965222791 75794934974366234947834187)
  ·
    refine ⟨113692402461549352421751281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75794934974366234947834187 113692402461549352421751281)
    ·
      refine ⟨85269301846162014316313461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113692402461549352421751281 85269301846162014316313461)
      ·
        refine ⟨7993997048077688842154387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85269301846162014316313461 7993997048077688842154387)
        ·
          refine ⟨11990995572116533263231581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993997048077688842154387 11990995572116533263231581)
          ·
            refine ⟨4496623339543699973711843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11990995572116533263231581 4496623339543699973711843)
            ·
              refine ⟨6744935009315549960567765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496623339543699973711843 6744935009315549960567765)
              ·
                refine ⟨158084414280833202200807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6744935009315549960567765 158084414280833202200807)
                ·
                  rfl

theorem cell21_2078111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_2078111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078111 prefixEnd_2078111 := by exact prefixLift 2078111
  have htrace : WordTrace (prefixWord ++ tailWord_2078111) baseStart_2078111 baseEnd_2078111 := by
    simpa [prefixWord, tailWord_2078111, baseEnd_2078111] using wordTrace_append hprefix tailTrace_2078111
  have hstable : (prefixWord ++ tailWord_2078111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078111).length < 2 ^ (prefixWord ++ tailWord_2078111).sum := by decide
  have hdescent : baseEnd_2078111 < baseStart_2078111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078201 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_2078201 : Nat := 118140960795 + 2078201 * 2 ^ 59
def prefixEnd_2078201 : Nat := 4983230072969 + 3 ^ 40 * 2078201 * 2
def baseEnd_2078201 : Nat := 474273782068679450102237

theorem tailTrace_2078201 : CollatzResearch.WordTrace tailWord_2078201 prefixEnd_2078201 474273782068679450102237 := by
  unfold tailWord_2078201
  simp only [CollatzResearch.WordTrace]
  refine ⟨75798217544040180318610457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50532145029360120212406971 75798217544040180318610457)
  ·
    refine ⟨56848663158030135238957843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75798217544040180318610457 56848663158030135238957843)
    ·
      refine ⟨85272994737045202858436765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56848663158030135238957843 85272994737045202858436765)
      ·
        refine ⟨31977373026391951071913787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85272994737045202858436765 31977373026391951071913787)
        ·
          refine ⟨47966059539587926607870681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31977373026391951071913787 47966059539587926607870681)
          ·
            refine ⟨35974544654690944955903011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47966059539587926607870681 35974544654690944955903011)
            ·
              refine ⟨53961816982036417433854517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35974544654690944955903011 53961816982036417433854517)
              ·
                refine ⟨5058920342065914134423861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53961816982036417433854517 5058920342065914134423861)
                ·
                  refine ⟨474273782068679450102237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058920342065914134423861 474273782068679450102237)
                  ·
                    rfl

theorem cell21_2078201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_2078201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078201 prefixEnd_2078201 := by exact prefixLift 2078201
  have htrace : WordTrace (prefixWord ++ tailWord_2078201) baseStart_2078201 baseEnd_2078201 := by
    simpa [prefixWord, tailWord_2078201, baseEnd_2078201] using wordTrace_append hprefix tailTrace_2078201
  have hstable : (prefixWord ++ tailWord_2078201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078201).length < 2 ^ (prefixWord ++ tailWord_2078201).sum := by decide
  have hdescent : baseEnd_2078201 < baseStart_2078201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078218 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_2078218 : Nat := 118140960795 + 2078218 * 2 ^ 59
def prefixEnd_2078218 : Nat := 4983230072969 + 3 ^ 40 * 2078218 * 2
def baseEnd_2078218 : Nat := 474277661700291198318869

theorem tailTrace_2078218 : CollatzResearch.WordTrace tailWord_2078218 prefixEnd_2078218 474277661700291198318869 := by
  unfold tailWord_2078218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949709396244648055494827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50532558389985728147986205 18949709396244648055494827)
  ·
    refine ⟨28424564094366972083242241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949709396244648055494827 28424564094366972083242241)
    ·
      refine ⟨21318423070775229062431681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28424564094366972083242241 21318423070775229062431681)
      ·
        refine ⟨15988817303081421796823761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21318423070775229062431681 15988817303081421796823761)
        ·
          refine ⟨11991612977311066347617821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15988817303081421796823761 11991612977311066347617821)
          ·
            refine ⟨4496854866491649880356683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11991612977311066347617821 4496854866491649880356683)
            ·
              refine ⟨6745282299737474820535025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496854866491649880356683 6745282299737474820535025)
              ·
                refine ⟨5058961724803106115401269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745282299737474820535025 5058961724803106115401269)
                ·
                  refine ⟨474277661700291198318869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058961724803106115401269 474277661700291198318869)
                  ·
                    rfl

theorem cell21_2078218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_2078218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078218 prefixEnd_2078218 := by exact prefixLift 2078218
  have htrace : WordTrace (prefixWord ++ tailWord_2078218) baseStart_2078218 baseEnd_2078218 := by
    simpa [prefixWord, tailWord_2078218, baseEnd_2078218] using wordTrace_append hprefix tailTrace_2078218
  have hstable : (prefixWord ++ tailWord_2078218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078218).length < 2 ^ (prefixWord ++ tailWord_2078218).sum := by decide
  have hdescent : baseEnd_2078218 < baseStart_2078218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078238 : List Nat := [4, 3, 3, 1, 1, 1, 8]
def baseStart_2078238 : Nat := 118140960795 + 2078238 * 2 ^ 59
def prefixEnd_2078238 : Nat := 4983230072969 + 3 ^ 40 * 2078238 * 2
def baseEnd_2078238 : Nat := 52698025108086178665055

theorem tailTrace_2078238 : CollatzResearch.WordTrace tailWord_2078238 prefixEnd_2078238 52698025108086178665055 := by
  unfold tailWord_2078238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474945880613266954713421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50533044696604090425138245 9474945880613266954713421)
  ·
    refine ⟨3553104705229975108017533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9474945880613266954713421 3553104705229975108017533)
    ·
      refine ⟨1332414264461240665506575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3553104705229975108017533 1332414264461240665506575)
      ·
        refine ⟨1998621396691860998259863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332414264461240665506575 1998621396691860998259863)
        ·
          refine ⟨2997932095037791497389795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998621396691860998259863 2997932095037791497389795)
          ·
            refine ⟨4496898142556687246084693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997932095037791497389795 4496898142556687246084693)
            ·
              refine ⟨52698025108086178665055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4496898142556687246084693 52698025108086178665055)
              ·
                rfl

theorem cell21_2078238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 8].length) (baseStart_2078238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078238 prefixEnd_2078238 := by exact prefixLift 2078238
  have htrace : WordTrace (prefixWord ++ tailWord_2078238) baseStart_2078238 baseEnd_2078238 := by
    simpa [prefixWord, tailWord_2078238, baseEnd_2078238] using wordTrace_append hprefix tailTrace_2078238
  have hstable : (prefixWord ++ tailWord_2078238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078238).length < 2 ^ (prefixWord ++ tailWord_2078238).sum := by decide
  have hdescent : baseEnd_2078238 < baseStart_2078238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078277 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2078277 : Nat := 118140960795 + 2078277 * 2 ^ 59
def prefixEnd_2078277 : Nat := 4983230072969 + 3 ^ 40 * 2078277 * 2
def baseEnd_2078277 : Nat := 474291126304120206835415

theorem tailTrace_2078277 : CollatzResearch.WordTrace tailWord_2078277 prefixEnd_2078277 474291126304120206835415 := by
  unfold tailWord_2078277
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800989491764845298377085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50533992994509896865584723 75800989491764845298377085)
  ·
    refine ⟨28425371059411816986891407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75800989491764845298377085 28425371059411816986891407)
    ·
      refine ⟨42638056589117725480337111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28425371059411816986891407 42638056589117725480337111)
      ·
        refine ⟨63957084883676588220505667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42638056589117725480337111 63957084883676588220505667)
        ·
          refine ⟨95935627325514882330758501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63957084883676588220505667 95935627325514882330758501)
          ·
            refine ⟨17987930123534040437017219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95935627325514882330758501 17987930123534040437017219)
            ·
              refine ⟨26981895185301060655525829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987930123534040437017219 26981895185301060655525829)
              ·
                refine ⟨5059105347243948872911093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26981895185301060655525829 5059105347243948872911093)
                ·
                  refine ⟨474291126304120206835415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5059105347243948872911093 474291126304120206835415)
                  ·
                    rfl

theorem cell21_2078277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2078277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078277 prefixEnd_2078277 := by exact prefixLift 2078277
  have htrace : WordTrace (prefixWord ++ tailWord_2078277) baseStart_2078277 baseEnd_2078277 := by
    simpa [prefixWord, tailWord_2078277, baseEnd_2078277] using wordTrace_append hprefix tailTrace_2078277
  have hstable : (prefixWord ++ tailWord_2078277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078277).length < 2 ^ (prefixWord ++ tailWord_2078277).sum := by decide
  have hdescent : baseEnd_2078277 < baseStart_2078277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078308 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2078308 : Nat := 118140960795 + 2078308 * 2 ^ 59
def prefixEnd_2078308 : Nat := 4983230072969 + 3 ^ 40 * 2078308 * 2
def baseEnd_2078308 : Nat := 474298200926471041818685

theorem tailTrace_2078308 : CollatzResearch.WordTrace tailWord_2078308 prefixEnd_2078308 474298200926471041818685 := by
  unfold tailWord_2078308
  simp only [CollatzResearch.WordTrace]
  refine ⟨37901060077326268796377789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50534746769768358395170385 37901060077326268796377789)
  ·
    refine ⟨14212897528997350798641671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37901060077326268796377789 14212897528997350798641671)
    ·
      refine ⟨21319346293496026197962507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14212897528997350798641671 21319346293496026197962507)
      ·
        refine ⟨31979019440244039296943761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21319346293496026197962507 31979019440244039296943761)
        ·
          refine ⟨23984264580183029472707821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31979019440244039296943761 23984264580183029472707821)
          ·
            refine ⟨8994099217568636052265433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23984264580183029472707821 8994099217568636052265433)
            ·
              refine ⟨6745574413176477039199075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994099217568636052265433 6745574413176477039199075)
              ·
                refine ⟨10118361619764715558798613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745574413176477039199075 10118361619764715558798613)
                ·
                  refine ⟨474298200926471041818685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10118361619764715558798613 474298200926471041818685)
                  ·
                    rfl

theorem cell21_2078308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2078308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078308 prefixEnd_2078308 := by exact prefixLift 2078308
  have htrace : WordTrace (prefixWord ++ tailWord_2078308) baseStart_2078308 baseEnd_2078308 := by
    simpa [prefixWord, tailWord_2078308, baseEnd_2078308] using wordTrace_append hprefix tailTrace_2078308
  have hstable : (prefixWord ++ tailWord_2078308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078308).length < 2 ^ (prefixWord ++ tailWord_2078308).sum := by decide
  have hdescent : baseEnd_2078308 < baseStart_2078308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078356 : List Nat := [2, 4, 2, 2, 3, 8]
def baseStart_2078356 : Nat := 118140960795 + 2078356 * 2 ^ 59
def prefixEnd_2078356 : Nat := 4983230072969 + 3 ^ 40 * 2078356 * 2
def baseEnd_2078356 : Nat := 17567005747423467593281

theorem tailTrace_2078356 : CollatzResearch.WordTrace tailWord_2078356 prefixEnd_2078356 17567005747423467593281 := by
  unfold tailWord_2078356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37901935429239320895251461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50535913905652427860335281 37901935429239320895251461)
  ·
    refine ⟨7106612892982372667859649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37901935429239320895251461 7106612892982372667859649)
    ·
      refine ⟨5329959669736779500894737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106612892982372667859649 5329959669736779500894737)
      ·
        refine ⟨3997469752302584625671053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329959669736779500894737 3997469752302584625671053)
        ·
          refine ⟨1499051157113469234626645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3997469752302584625671053 1499051157113469234626645)
          ·
            refine ⟨17567005747423467593281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1499051157113469234626645 17567005747423467593281)
            ·
              rfl

theorem cell21_2078356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 8].length) (baseStart_2078356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078356 prefixEnd_2078356 := by exact prefixLift 2078356
  have htrace : WordTrace (prefixWord ++ tailWord_2078356) baseStart_2078356 baseEnd_2078356 := by
    simpa [prefixWord, tailWord_2078356, baseEnd_2078356] using wordTrace_append hprefix tailTrace_2078356
  have hstable : (prefixWord ++ tailWord_2078356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078356).length < 2 ^ (prefixWord ++ tailWord_2078356).sum := by decide
  have hdescent : baseEnd_2078356 < baseStart_2078356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078384 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_2078384 : Nat := 118140960795 + 2078384 * 2 ^ 59
def prefixEnd_2078384 : Nat := 4983230072969 + 3 ^ 40 * 2078384 * 2
def baseEnd_2078384 : Nat := 474315545161911798551863

theorem tailTrace_2078384 : CollatzResearch.WordTrace tailWord_2078384 prefixEnd_2078384 474315545161911798551863 := by
  unfold tailWord_2078384
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902446051188601286261103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50536594734918135048348137 37902446051188601286261103)
  ·
    refine ⟨56853669076782901929391655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37902446051188601286261103 56853669076782901929391655)
    ·
      refine ⟨85280503615174352894087483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56853669076782901929391655 85280503615174352894087483)
      ·
        refine ⟨127920755422761529341131225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85280503615174352894087483 127920755422761529341131225)
        ·
          refine ⟨95940566567071147005848419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127920755422761529341131225 95940566567071147005848419)
          ·
            refine ⟨143910849850606720508772629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95940566567071147005848419 143910849850606720508772629)
            ·
              refine ⟨6745821086747190023848717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143910849850606720508772629 6745821086747190023848717)
              ·
                refine ⟨2529682907530196258943269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6745821086747190023848717 2529682907530196258943269)
                ·
                  refine ⟨474315545161911798551863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529682907530196258943269 474315545161911798551863)
                  ·
                    rfl

theorem cell21_2078384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_2078384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078384 prefixEnd_2078384 := by exact prefixLift 2078384
  have htrace : WordTrace (prefixWord ++ tailWord_2078384) baseStart_2078384 baseEnd_2078384 := by
    simpa [prefixWord, tailWord_2078384, baseEnd_2078384] using wordTrace_append hprefix tailTrace_2078384
  have hstable : (prefixWord ++ tailWord_2078384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078384).length < 2 ^ (prefixWord ++ tailWord_2078384).sum := by decide
  have hdescent : baseEnd_2078384 < baseStart_2078384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078418 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2078418 : Nat := 118140960795 + 2078418 * 2 ^ 59
def prefixEnd_2078418 : Nat := 4983230072969 + 3 ^ 40 * 2078418 * 2
def baseEnd_2078418 : Nat := 474323304425135294985127

theorem tailTrace_2078418 : CollatzResearch.WordTrace tailWord_2078418 prefixEnd_2078418 474323304425135294985127 := by
  unfold tailWord_2078418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951533046063506594814977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50537421456169350919506605 18951533046063506594814977)
  ·
    refine ⟨14213649784547629946111233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18951533046063506594814977 14213649784547629946111233)
    ·
      refine ⟨10660237338410722459583425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14213649784547629946111233 10660237338410722459583425)
      ·
        refine ⟨7995178003808041844687569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10660237338410722459583425 7995178003808041844687569)
        ·
          refine ⟨5996383502856031383515677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995178003808041844687569 5996383502856031383515677)
          ·
            refine ⟨2248643813571011768818379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5996383502856031383515677 2248643813571011768818379)
            ·
              refine ⟨3372965720356517653227569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248643813571011768818379 3372965720356517653227569)
              ·
                refine ⟨2529724290267388239920677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372965720356517653227569 2529724290267388239920677)
                ·
                  refine ⟨474323304425135294985127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529724290267388239920677 474323304425135294985127)
                  ·
                    rfl

theorem cell21_2078418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2078418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078418 prefixEnd_2078418 := by exact prefixLift 2078418
  have htrace : WordTrace (prefixWord ++ tailWord_2078418) baseStart_2078418 baseEnd_2078418 := by
    simpa [prefixWord, tailWord_2078418, baseEnd_2078418] using wordTrace_append hprefix tailTrace_2078418
  have hstable : (prefixWord ++ tailWord_2078418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078418).length < 2 ^ (prefixWord ++ tailWord_2078418).sum := by decide
  have hdescent : baseEnd_2078418 < baseStart_2078418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078474 : List Nat := [3, 1, 2, 2, 1, 3, 9]
def baseStart_2078474 : Nat := 118140960795 + 2078474 * 2 ^ 59
def prefixEnd_2078474 : Nat := 4983230072969 + 3 ^ 40 * 2078474 * 2
def baseEnd_2078474 : Nat := 52704009376454626894631

theorem tailTrace_2078474 : CollatzResearch.WordTrace tailWord_2078474 prefixEnd_2078474 52704009376454626894631 := by
  unfold tailWord_2078474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18952043668012786985824619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50538783114700765295532317 18952043668012786985824619)
  ·
    refine ⟨28428065502019180478736929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18952043668012786985824619 28428065502019180478736929)
    ·
      refine ⟨21321049126514385359052697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28428065502019180478736929 21321049126514385359052697)
      ·
        refine ⟨15990786844885789019289523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21321049126514385359052697 15990786844885789019289523)
        ·
          refine ⟨23986180267328683528934285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990786844885789019289523 23986180267328683528934285)
          ·
            refine ⟨8994817600248256323350357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23986180267328683528934285 8994817600248256323350357)
            ·
              refine ⟨52704009376454626894631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8994817600248256323350357 52704009376454626894631)
              ·
                rfl

theorem cell21_2078474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 9].length) (baseStart_2078474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078474 prefixEnd_2078474 := by exact prefixLift 2078474
  have htrace : WordTrace (prefixWord ++ tailWord_2078474) baseStart_2078474 baseEnd_2078474 := by
    simpa [prefixWord, tailWord_2078474, baseEnd_2078474] using wordTrace_append hprefix tailTrace_2078474
  have hstable : (prefixWord ++ tailWord_2078474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078474).length < 2 ^ (prefixWord ++ tailWord_2078474).sum := by decide
  have hdescent : baseEnd_2078474 < baseStart_2078474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078519 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_2078519 : Nat := 118140960795 + 2078519 * 2 ^ 59
def prefixEnd_2078519 : Nat := 4983230072969 + 3 ^ 40 * 2078519 * 2
def baseEnd_2078519 : Nat := 474346354001181563801587

theorem tailTrace_2078519 : CollatzResearch.WordTrace tailWord_2078519 prefixEnd_2078519 474346354001181563801587 := by
  unfold tailWord_2078519
  simp only [CollatzResearch.WordTrace]
  refine ⟨75809815956888120628686611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50539877304592080419124407 75809815956888120628686611)
  ·
    refine ⟨113714723935332180943029917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75809815956888120628686611 113714723935332180943029917)
    ·
      refine ⟨42643021475749567853636219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113714723935332180943029917 42643021475749567853636219)
      ·
        refine ⟨63964532213624351780454329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42643021475749567853636219 63964532213624351780454329)
        ·
          refine ⟨47973399160218263835340747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63964532213624351780454329 47973399160218263835340747)
          ·
            refine ⟨71960098740327395753011121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47973399160218263835340747 71960098740327395753011121)
            ·
              refine ⟨53970074055245546814758341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71960098740327395753011121 53970074055245546814758341)
              ·
                refine ⟨10119388885358540027767189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53970074055245546814758341 10119388885358540027767189)
                ·
                  refine ⟨474346354001181563801587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10119388885358540027767189 474346354001181563801587)
                  ·
                    rfl

theorem cell21_2078519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_2078519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078519 prefixEnd_2078519 := by exact prefixLift 2078519
  have htrace : WordTrace (prefixWord ++ tailWord_2078519) baseStart_2078519 baseEnd_2078519 := by
    simpa [prefixWord, tailWord_2078519, baseEnd_2078519] using wordTrace_append hprefix tailTrace_2078519
  have hstable : (prefixWord ++ tailWord_2078519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078519).length < 2 ^ (prefixWord ++ tailWord_2078519).sum := by decide
  have hdescent : baseEnd_2078519 < baseStart_2078519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078536 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_2078536 : Nat := 118140960795 + 2078536 * 2 ^ 59
def prefixEnd_2078536 : Nat := 4983230072969 + 3 ^ 40 * 2078536 * 2
def baseEnd_2078536 : Nat := 474350233632793312018219

theorem tailTrace_2078536 : CollatzResearch.WordTrace tailWord_2078536 prefixEnd_2078536 474350233632793312018219 := by
  unfold tailWord_2078536
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905217998913266266027731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50540290665217688354703641 37905217998913266266027731)
  ·
    refine ⟨56857826998369899399041597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37905217998913266266027731 56857826998369899399041597)
    ·
      refine ⟨21321685124388712274640599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56857826998369899399041597 21321685124388712274640599)
      ·
        refine ⟨31982527686583068411960899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21321685124388712274640599 31982527686583068411960899)
        ·
          refine ⟨47973791529874602617941349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31982527686583068411960899 47973791529874602617941349)
          ·
            refine ⟨8995085911851487990864003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47973791529874602617941349 8995085911851487990864003)
            ·
              refine ⟨13492628867777231986296005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995085911851487990864003 13492628867777231986296005)
              ·
                refine ⟨2529867912708230997430501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13492628867777231986296005 2529867912708230997430501)
                ·
                  refine ⟨474350233632793312018219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529867912708230997430501 474350233632793312018219)
                  ·
                    rfl

theorem cell21_2078536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_2078536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078536 prefixEnd_2078536 := by exact prefixLift 2078536
  have htrace : WordTrace (prefixWord ++ tailWord_2078536) baseStart_2078536 baseEnd_2078536 := by
    simpa [prefixWord, tailWord_2078536, baseEnd_2078536] using wordTrace_append hprefix tailTrace_2078536
  have hstable : (prefixWord ++ tailWord_2078536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078536).length < 2 ^ (prefixWord ++ tailWord_2078536).sum := by decide
  have hdescent : baseEnd_2078536 < baseStart_2078536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078567 : List Nat := [1, 1, 5, 1, 2, 1, 5, 5]
def baseStart_2078567 : Nat := 118140960795 + 2078567 * 2 ^ 59
def prefixEnd_2078567 : Nat := 4983230072969 + 3 ^ 40 * 2078567 * 2
def baseEnd_2078567 : Nat := 158119102751714715667163

theorem tailTrace_2078567 : CollatzResearch.WordTrace tailWord_2078567 prefixEnd_2078567 158119102751714715667163 := by
  unfold tailWord_2078567
  simp only [CollatzResearch.WordTrace]
  refine ⟨75811566660714224826433955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50541044440476149884289303 75811566660714224826433955)
  ·
    refine ⟨113717349991071337239650933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75811566660714224826433955 113717349991071337239650933)
    ·
      refine ⟨10661001561662937866217275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113717349991071337239650933 10661001561662937866217275)
      ·
        refine ⟨15991502342494406799325913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661001561662937866217275 15991502342494406799325913)
        ·
          refine ⟨11993626756870805099494435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15991502342494406799325913 11993626756870805099494435)
          ·
            refine ⟨17990440135306207649241653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993626756870805099494435 17990440135306207649241653)
            ·
              refine ⟨1686603762684956967116405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17990440135306207649241653 1686603762684956967116405)
              ·
                refine ⟨158119102751714715667163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686603762684956967116405 158119102751714715667163)
                ·
                  rfl

theorem cell21_2078567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].length) (baseStart_2078567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078567 prefixEnd_2078567 := by exact prefixLift 2078567
  have htrace : WordTrace (prefixWord ++ tailWord_2078567) baseStart_2078567 baseEnd_2078567 := by
    simpa [prefixWord, tailWord_2078567, baseEnd_2078567] using wordTrace_append hprefix tailTrace_2078567
  have hstable : (prefixWord ++ tailWord_2078567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078567).length < 2 ^ (prefixWord ++ tailWord_2078567).sum := by decide
  have hdescent : baseEnd_2078567 < baseStart_2078567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078581 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2078581 : Nat := 118140960795 + 2078581 * 2 ^ 59
def prefixEnd_2078581 : Nat := 4983230072969 + 3 ^ 40 * 2078581 * 2
def baseEnd_2078581 : Nat := 474360503245883233768127

theorem tailTrace_2078581 : CollatzResearch.WordTrace tailWord_2078581 prefixEnd_2078581 474360503245883233768127 := by
  unfold tailWord_2078581
  simp only [CollatzResearch.WordTrace]
  refine ⟨75812077282663505217443597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50541384855109003478295731 75812077282663505217443597)
  ·
    refine ⟨28429528980998814456541349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75812077282663505217443597 28429528980998814456541349)
    ·
      refine ⟨5330536683937277710601503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28429528980998814456541349 5330536683937277710601503)
      ·
        refine ⟨7995805025905916565902255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330536683937277710601503 7995805025905916565902255)
        ·
          refine ⟨11993707538858874848853383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995805025905916565902255 11993707538858874848853383)
          ·
            refine ⟨17990561308288312273280075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993707538858874848853383 17990561308288312273280075)
            ·
              refine ⟨26985841962432468409920113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17990561308288312273280075 26985841962432468409920113)
              ·
                refine ⟨20239381471824351307440085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26985841962432468409920113 20239381471824351307440085)
                ·
                  refine ⟨474360503245883233768127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20239381471824351307440085 474360503245883233768127)
                  ·
                    rfl

theorem cell21_2078581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2078581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078581 prefixEnd_2078581 := by exact prefixLift 2078581
  have htrace : WordTrace (prefixWord ++ tailWord_2078581) baseStart_2078581 baseEnd_2078581 := by
    simpa [prefixWord, tailWord_2078581, baseEnd_2078581] using wordTrace_append hprefix tailTrace_2078581
  have hstable : (prefixWord ++ tailWord_2078581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078581).length < 2 ^ (prefixWord ++ tailWord_2078581).sum := by decide
  have hdescent : baseEnd_2078581 < baseStart_2078581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078702 : List Nat := [4, 1, 2, 1, 3, 10]
def baseStart_2078702 : Nat := 118140960795 + 2078702 * 2 ^ 59
def prefixEnd_2078702 : Nat := 4983230072969 + 3 ^ 40 * 2078702 * 2
def baseEnd_2078702 : Nat := 17569930262756070824119

theorem tailTrace_2078702 : CollatzResearch.WordTrace tailWord_2078702 prefixEnd_2078702 17569930262756070824119 := by
  unfold tailWord_2078702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477061314403142860324795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50544327010150095255065573 9477061314403142860324795)
  ·
    refine ⟨14215591971604714290487193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9477061314403142860324795 14215591971604714290487193)
    ·
      refine ⟨10661693978703535717865395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14215591971604714290487193 10661693978703535717865395)
      ·
        refine ⟨15992540968055303576798093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661693978703535717865395 15992540968055303576798093)
        ·
          refine ⟨5997202863020738841299285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15992540968055303576798093 5997202863020738841299285)
          ·
            refine ⟨17569930262756070824119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5997202863020738841299285 17569930262756070824119)
            ·
              rfl

theorem cell21_2078702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 10].length) (baseStart_2078702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078702 prefixEnd_2078702 := by exact prefixLift 2078702
  have htrace : WordTrace (prefixWord ++ tailWord_2078702) baseStart_2078702 baseEnd_2078702 := by
    simpa [prefixWord, tailWord_2078702, baseEnd_2078702] using wordTrace_append hprefix tailTrace_2078702
  have hstable : (prefixWord ++ tailWord_2078702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078702).length < 2 ^ (prefixWord ++ tailWord_2078702).sum := by decide
  have hdescent : baseEnd_2078702 < baseStart_2078702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078705 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_2078705 : Nat := 118140960795 + 2078705 * 2 ^ 59
def prefixEnd_2078705 : Nat := 4983230072969 + 3 ^ 40 * 2078705 * 2
def baseEnd_2078705 : Nat := 474388801735286573701207

theorem tailTrace_2078705 : CollatzResearch.WordTrace tailWord_2078705 prefixEnd_2078705 474388801735286573701207 := by
  unfold tailWord_2078705
  simp only [CollatzResearch.WordTrace]
  refine ⟨75816599934214274394957569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50544399956142849596638379 75816599934214274394957569)
  ·
    refine ⟨56862449950660705796218177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75816599934214274394957569 56862449950660705796218177)
    ·
      refine ⟨42646837462995529347163633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56862449950660705796218177 42646837462995529347163633)
      ·
        refine ⟨31985128097246647010372725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42646837462995529347163633 31985128097246647010372725)
        ·
          refine ⟨2998605759116873157222443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31985128097246647010372725 2998605759116873157222443)
          ·
            refine ⟨4497908638675309735833665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998605759116873157222443 4497908638675309735833665)
            ·
              refine ⟨3373431479006482301875249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497908638675309735833665 3373431479006482301875249)
              ·
                refine ⟨2530073609254861726406437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373431479006482301875249 2530073609254861726406437)
                ·
                  refine ⟨474388801735286573701207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530073609254861726406437 474388801735286573701207)
                  ·
                    rfl

theorem cell21_2078705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_2078705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078705 prefixEnd_2078705 := by exact prefixLift 2078705
  have htrace : WordTrace (prefixWord ++ tailWord_2078705) baseStart_2078705 baseEnd_2078705 := by
    simpa [prefixWord, tailWord_2078705, baseEnd_2078705] using wordTrace_append hprefix tailTrace_2078705
  have hstable : (prefixWord ++ tailWord_2078705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078705).length < 2 ^ (prefixWord ++ tailWord_2078705).sum := by decide
  have hdescent : baseEnd_2078705 < baseStart_2078705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078781 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2078781 : Nat := 118140960795 + 2078781 * 2 ^ 59
def prefixEnd_2078781 : Nat := 4983230072969 + 3 ^ 40 * 2078781 * 2
def baseEnd_2078781 : Nat := 474406145970727330434385

theorem tailTrace_2078781 : CollatzResearch.WordTrace tailWord_2078781 prefixEnd_2078781 474406145970727330434385 := by
  unfold tailWord_2078781
  simp only [CollatzResearch.WordTrace]
  refine ⟨75819371881938939374724197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50546247921292626249816131 75819371881938939374724197)
  ·
    refine ⟨14216132227863551132760787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75819371881938939374724197 14216132227863551132760787)
    ·
      refine ⟨21324198341795326699141181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14216132227863551132760787 21324198341795326699141181)
      ·
        refine ⟨7996574378173247512177943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21324198341795326699141181 7996574378173247512177943)
        ·
          refine ⟨11994861567259871268266915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996574378173247512177943 11994861567259871268266915)
          ·
            refine ⟨17992292350889806902400373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994861567259871268266915 17992292350889806902400373)
            ·
              refine ⟨1686777407895919397100035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17992292350889806902400373 1686777407895919397100035)
              ·
                refine ⟨2530166111843879095650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686777407895919397100035 2530166111843879095650053)
                ·
                  refine ⟨474406145970727330434385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530166111843879095650053 474406145970727330434385)
                  ·
                    rfl

theorem cell21_2078781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2078781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078781 prefixEnd_2078781 := by exact prefixLift 2078781
  have htrace : WordTrace (prefixWord ++ tailWord_2078781) baseStart_2078781 baseEnd_2078781 := by
    simpa [prefixWord, tailWord_2078781, baseEnd_2078781] using wordTrace_append hprefix tailTrace_2078781
  have hstable : (prefixWord ++ tailWord_2078781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078781).length < 2 ^ (prefixWord ++ tailWord_2078781).sum := by decide
  have hdescent : baseEnd_2078781 < baseStart_2078781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078792 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_2078792 : Nat := 118140960795 + 2078792 * 2 ^ 59
def prefixEnd_2078792 : Nat := 4983230072969 + 3 ^ 40 * 2078792 * 2
def baseEnd_2078792 : Nat := 474408656320593755751029

theorem tailTrace_2078792 : CollatzResearch.WordTrace tailWord_2078792 prefixEnd_2078792 474408656320593755751029 := by
  unfold tailWord_2078792
  simp only [CollatzResearch.WordTrace]
  refine ⟨37909886542449544126687315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50546515389932725502249753 37909886542449544126687315)
  ·
    refine ⟨56864829813674316190030973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37909886542449544126687315 56864829813674316190030973)
    ·
      refine ⟨21324311180127868571261615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56864829813674316190030973 21324311180127868571261615)
      ·
        refine ⟨31986466770191802856892423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324311180127868571261615 31986466770191802856892423)
        ·
          refine ⟨47979700155287704285338635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31986466770191802856892423 47979700155287704285338635)
          ·
            refine ⟨71969550232931556428007953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47979700155287704285338635 71969550232931556428007953)
            ·
              refine ⟨53977162674698667321005965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71969550232931556428007953 53977162674698667321005965)
              ·
                refine ⟨20241436003012000245377237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53977162674698667321005965 20241436003012000245377237)
                ·
                  refine ⟨474408656320593755751029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20241436003012000245377237 474408656320593755751029)
                  ·
                    rfl

theorem cell21_2078792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_2078792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078792 prefixEnd_2078792 := by exact prefixLift 2078792
  have htrace : WordTrace (prefixWord ++ tailWord_2078792) baseStart_2078792 baseEnd_2078792 := by
    simpa [prefixWord, tailWord_2078792, baseEnd_2078792] using wordTrace_append hprefix tailTrace_2078792
  have hstable : (prefixWord ++ tailWord_2078792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078792).length < 2 ^ (prefixWord ++ tailWord_2078792).sum := by decide
  have hdescent : baseEnd_2078792 < baseStart_2078792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078823 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_2078823 : Nat := 118140960795 + 2078823 * 2 ^ 59
def prefixEnd_2078823 : Nat := 4983230072969 + 3 ^ 40 * 2078823 * 2
def baseEnd_2078823 : Nat := 474415730942944590734299

theorem tailTrace_2078823 : CollatzResearch.WordTrace tailWord_2078823 prefixEnd_2078823 474415730942944590734299 := by
  unfold tailWord_2078823
  simp only [CollatzResearch.WordTrace]
  refine ⟨75820903747786780547753123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50547269165191187031835415 75820903747786780547753123)
  ·
    refine ⟨113731355621680170821629685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75820903747786780547753123 113731355621680170821629685)
    ·
      refine ⟨10662314589532516014527783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113731355621680170821629685 10662314589532516014527783)
      ·
        refine ⟨15993471884298774021791675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662314589532516014527783 15993471884298774021791675)
        ·
          refine ⟨23990207826448161032687513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15993471884298774021791675 23990207826448161032687513)
          ·
            refine ⟨17992655869836120774515635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23990207826448161032687513 17992655869836120774515635)
            ·
              refine ⟨26988983804754181161773453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17992655869836120774515635 26988983804754181161773453)
              ·
                refine ⟨10120868926782817935665045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26988983804754181161773453 10120868926782817935665045)
                ·
                  refine ⟨474415730942944590734299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10120868926782817935665045 474415730942944590734299)
                  ·
                    rfl

theorem cell21_2078823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_2078823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078823 prefixEnd_2078823 := by exact prefixLift 2078823
  have htrace : WordTrace (prefixWord ++ tailWord_2078823) baseStart_2078823 baseEnd_2078823 := by
    simpa [prefixWord, tailWord_2078823, baseEnd_2078823] using wordTrace_append hprefix tailTrace_2078823
  have hstable : (prefixWord ++ tailWord_2078823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078823).length < 2 ^ (prefixWord ++ tailWord_2078823).sum := by decide
  have hdescent : baseEnd_2078823 < baseStart_2078823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078930 : List Nat := [3, 2, 2, 2, 1, 3, 8]
def baseStart_2078930 : Nat := 118140960795 + 2078930 * 2 ^ 59
def prefixEnd_2078930 : Nat := 4983230072969 + 3 ^ 40 * 2078930 * 2
def baseEnd_2078930 : Nat := 52715572200081798050083

theorem tailTrace_2078930 : CollatzResearch.WordTrace tailWord_2078930 prefixEnd_2078930 52715572200081798050083 := by
  unfold tailWord_2078930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956201589599784455474561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50549870905599425214598829 18956201589599784455474561)
  ·
    refine ⟨14217151192199838341605921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18956201589599784455474561 14217151192199838341605921)
    ·
      refine ⟨10662863394149878756204441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14217151192199838341605921 10662863394149878756204441)
      ·
        refine ⟨7997147545612409067153331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10662863394149878756204441 7997147545612409067153331)
        ·
          refine ⟨11995721318418613600729997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997147545612409067153331 11995721318418613600729997)
          ·
            refine ⟨4498395494406980100273749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11995721318418613600729997 4498395494406980100273749)
            ·
              refine ⟨52715572200081798050083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4498395494406980100273749 52715572200081798050083)
              ·
                rfl

theorem cell21_2078930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 8].length) (baseStart_2078930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2078930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2078930 prefixEnd_2078930 := by exact prefixLift 2078930
  have htrace : WordTrace (prefixWord ++ tailWord_2078930) baseStart_2078930 baseEnd_2078930 := by
    simpa [prefixWord, tailWord_2078930, baseEnd_2078930] using wordTrace_append hprefix tailTrace_2078930
  have hstable : (prefixWord ++ tailWord_2078930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078930).length < 2 ^ (prefixWord ++ tailWord_2078930).sum := by decide
  have hdescent : baseEnd_2078930 < baseStart_2078930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079020 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_2079020 : Nat := 118140960795 + 2079020 * 2 ^ 59
def prefixEnd_2079020 : Nat := 4983230072969 + 3 ^ 40 * 2079020 * 2
def baseEnd_2079020 : Nat := 474460689026916025950563

theorem tailTrace_2079020 : CollatzResearch.WordTrace tailWord_2079020 prefixEnd_2079020 474460689026916025950563 := by
  unfold tailWord_2079020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914044464036541596337257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50552059285382055461783009 37914044464036541596337257)
  ·
    refine ⟨28435533348027406197252943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37914044464036541596337257 28435533348027406197252943)
    ·
      refine ⟨42653300022041109295879415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28435533348027406197252943 42653300022041109295879415)
      ·
        refine ⟨63979950033061663943819123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42653300022041109295879415 63979950033061663943819123)
        ·
          refine ⟨95969925049592495915728685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63979950033061663943819123 95969925049592495915728685)
          ·
            refine ⟨35988721893597185968398257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95969925049592495915728685 35988721893597185968398257)
            ·
              refine ⟨26991541420197889476298693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35988721893597185968398257 26991541420197889476298693)
              ·
                refine ⟨5060914016287104276806005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26991541420197889476298693 5060914016287104276806005)
                ·
                  refine ⟨474460689026916025950563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5060914016287104276806005 474460689026916025950563)
                  ·
                    rfl

theorem cell21_2079020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_2079020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079020 prefixEnd_2079020 := by exact prefixLift 2079020
  have htrace : WordTrace (prefixWord ++ tailWord_2079020) baseStart_2079020 baseEnd_2079020 := by
    simpa [prefixWord, tailWord_2079020, baseEnd_2079020] using wordTrace_append hprefix tailTrace_2079020
  have hstable : (prefixWord ++ tailWord_2079020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079020).length < 2 ^ (prefixWord ++ tailWord_2079020).sum := by decide
  have hdescent : baseEnd_2079020 < baseStart_2079020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079113 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_2079113 : Nat := 118140960795 + 2079113 * 2 ^ 59
def prefixEnd_2079113 : Nat := 4983230072969 + 3 ^ 40 * 2079113 * 2
def baseEnd_2079113 : Nat := 474481912893968530900373

theorem tailTrace_2079113 : CollatzResearch.WordTrace tailWord_2079113 prefixEnd_2079113 474481912893968530900373 := by
  unfold tailWord_2079113
  simp only [CollatzResearch.WordTrace]
  refine ⟨75831480916736160075809993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50554320611157440050539995 75831480916736160075809993)
  ·
    refine ⟨56873610687552120056857495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75831480916736160075809993 56873610687552120056857495)
    ·
      refine ⟨85310416031328180085286243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56873610687552120056857495 85310416031328180085286243)
      ·
        refine ⟨127965624046992270127929365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85310416031328180085286243 127965624046992270127929365)
        ·
          refine ⟨5998388627202762662246689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127965624046992270127929365 5998388627202762662246689)
          ·
            refine ⟨4498791470402071996685017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5998388627202762662246689 4498791470402071996685017)
            ·
              refine ⟨3374093602801553997513763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4498791470402071996685017 3374093602801553997513763)
              ·
                refine ⟨5061140404202330996270645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374093602801553997513763 5061140404202330996270645)
                ·
                  refine ⟨474481912893968530900373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061140404202330996270645 474481912893968530900373)
                  ·
                    rfl

theorem cell21_2079113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_2079113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079113 prefixEnd_2079113 := by exact prefixLift 2079113
  have htrace : WordTrace (prefixWord ++ tailWord_2079113) baseStart_2079113 baseEnd_2079113 := by
    simpa [prefixWord, tailWord_2079113, baseEnd_2079113] using wordTrace_append hprefix tailTrace_2079113
  have hstable : (prefixWord ++ tailWord_2079113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079113).length < 2 ^ (prefixWord ++ tailWord_2079113).sum := by decide
  have hdescent : baseEnd_2079113 < baseStart_2079113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079127 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_2079127 : Nat := 118140960795 + 2079127 * 2 ^ 59
def prefixEnd_2079127 : Nat := 4983230072969 + 3 ^ 40 * 2079127 * 2
def baseEnd_2079127 : Nat := 474485107884707617667011

theorem tailTrace_2079127 : CollatzResearch.WordTrace tailWord_2079127 prefixEnd_2079127 474485107884707617667011 := by
  unfold tailWord_2079127
  simp only [CollatzResearch.WordTrace]
  refine ⟨75831991538685440466819635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50554661025790293644546423 75831991538685440466819635)
  ·
    refine ⟨113747987308028160700229453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75831991538685440466819635 113747987308028160700229453)
    ·
      refine ⟨42655495240510560262586045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113747987308028160700229453 42655495240510560262586045)
      ·
        refine ⟨15995810715191460098469767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42655495240510560262586045 15995810715191460098469767)
        ·
          refine ⟨23993716072787190147704651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995810715191460098469767 23993716072787190147704651)
          ·
            refine ⟨35990574109180785221556977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993716072787190147704651 35990574109180785221556977)
            ·
              refine ⟨26992930581885588916167733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35990574109180785221556977 26992930581885588916167733)
              ·
                refine ⟨2530587242051773960890725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26992930581885588916167733 2530587242051773960890725)
                ·
                  refine ⟨474485107884707617667011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530587242051773960890725 474485107884707617667011)
                  ·
                    rfl

theorem cell21_2079127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_2079127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079127 prefixEnd_2079127 := by exact prefixLift 2079127
  have htrace : WordTrace (prefixWord ++ tailWord_2079127) baseStart_2079127 baseEnd_2079127 := by
    simpa [prefixWord, tailWord_2079127, baseEnd_2079127] using wordTrace_append hprefix tailTrace_2079127
  have hstable : (prefixWord ++ tailWord_2079127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079127).length < 2 ^ (prefixWord ++ tailWord_2079127).sum := by decide
  have hdescent : baseEnd_2079127 < baseStart_2079127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079141 : List Nat := [1, 3, 1, 2, 1, 1, 5, 7]
def baseStart_2079141 : Nat := 118140960795 + 2079141 * 2 ^ 59
def prefixEnd_2079141 : Nat := 4983230072969 + 3 ^ 40 * 2079141 * 2
def baseEnd_2079141 : Nat := 158162767625148901477883

theorem tailTrace_2079141 : CollatzResearch.WordTrace tailWord_2079141 prefixEnd_2079141 158162767625148901477883 := by
  unfold tailWord_2079141
  simp only [CollatzResearch.WordTrace]
  refine ⟨75832502160634720857829277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50555001440423147238552851 75832502160634720857829277)
  ·
    refine ⟨28437188310238020321685979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75832502160634720857829277 28437188310238020321685979)
    ·
      refine ⟨42655782465357030482528969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28437188310238020321685979 42655782465357030482528969)
      ·
        refine ⟨31991836849017772861896727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42655782465357030482528969 31991836849017772861896727)
        ·
          refine ⟨47987755273526659292845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31991836849017772861896727 47987755273526659292845091)
          ·
            refine ⟨71981632910289988939267637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47987755273526659292845091 71981632910289988939267637)
            ·
              refine ⟨6748278085339686463056341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71981632910289988939267637 6748278085339686463056341)
              ·
                refine ⟨158162767625148901477883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6748278085339686463056341 158162767625148901477883)
                ·
                  rfl

theorem cell21_2079141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_2079141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079141 prefixEnd_2079141 := by exact prefixLift 2079141
  have htrace : WordTrace (prefixWord ++ tailWord_2079141) baseStart_2079141 baseEnd_2079141 := by
    simpa [prefixWord, tailWord_2079141, baseEnd_2079141] using wordTrace_append hprefix tailTrace_2079141
  have hstable : (prefixWord ++ tailWord_2079141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079141).length < 2 ^ (prefixWord ++ tailWord_2079141).sum := by decide
  have hdescent : baseEnd_2079141 < baseStart_2079141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079144 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_2079144 : Nat := 118140960795 + 2079144 * 2 ^ 59
def prefixEnd_2079144 : Nat := 4983230072969 + 3 ^ 40 * 2079144 * 2
def baseEnd_2079144 : Nat := 474488987516319365883643

theorem tailTrace_2079144 : CollatzResearch.WordTrace tailWord_2079144 prefixEnd_2079144 474488987516319365883643 := by
  unfold tailWord_2079144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916305789811926185094243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50555074386415901580125657 37916305789811926185094243)
  ·
    refine ⟨56874458684717889277641365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37916305789811926185094243 56874458684717889277641365)
    ·
      refine ⟨2665990250846151059889439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56874458684717889277641365 2665990250846151059889439)
      ·
        refine ⟨3998985376269226589834159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665990250846151059889439 3998985376269226589834159)
        ·
          refine ⟨5998478064403839884751239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998985376269226589834159 5998478064403839884751239)
          ·
            refine ⟨8997717096605759827126859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998478064403839884751239 8997717096605759827126859)
            ·
              refine ⟨13496575644908639740690289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997717096605759827126859 13496575644908639740690289)
              ·
                refine ⟨10122431733681479805517717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13496575644908639740690289 10122431733681479805517717)
                ·
                  refine ⟨474488987516319365883643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10122431733681479805517717 474488987516319365883643)
                  ·
                    rfl

theorem cell21_2079144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_2079144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079144 prefixEnd_2079144 := by exact prefixLift 2079144
  have htrace : WordTrace (prefixWord ++ tailWord_2079144) baseStart_2079144 baseEnd_2079144 := by
    simpa [prefixWord, tailWord_2079144, baseEnd_2079144] using wordTrace_append hprefix tailTrace_2079144
  have hstable : (prefixWord ++ tailWord_2079144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079144).length < 2 ^ (prefixWord ++ tailWord_2079144).sum := by decide
  have hdescent : baseEnd_2079144 < baseStart_2079144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079271 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 4]
def baseStart_2079271 : Nat := 118140960795 + 2079271 * 2 ^ 59
def prefixEnd_2079271 : Nat := 4983230072969 + 3 ^ 40 * 2079271 * 2
def baseEnd_2079271 : Nat := 474517970646595367266717

theorem tailTrace_2079271 : CollatzResearch.WordTrace tailWord_2079271 prefixEnd_2079271 474517970646595367266717 := by
  unfold tailWord_2079271
  simp only [CollatzResearch.WordTrace]
  refine ⟨75837243650163753060061667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50558162433442502040041111 75837243650163753060061667)
  ·
    refine ⟨113755865475245629590092501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75837243650163753060061667 113755865475245629590092501)
    ·
      refine ⟨2666153097076069443517793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113755865475245629590092501 2666153097076069443517793)
      ·
        refine ⟨1999614822807052082638345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666153097076069443517793 1999614822807052082638345)
        ·
          refine ⟨1499711117105289061978759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999614822807052082638345 1499711117105289061978759)
          ·
            refine ⟨2249566675657933592968139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499711117105289061978759 2249566675657933592968139)
            ·
              refine ⟨3374350013486900389452209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249566675657933592968139 3374350013486900389452209)
              ·
                refine ⟨2530762510115175292089157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374350013486900389452209 2530762510115175292089157)
                ·
                  refine ⟨474517970646595367266717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530762510115175292089157 474517970646595367266717)
                  ·
                    rfl

theorem cell21_2079271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].length) (baseStart_2079271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079271 prefixEnd_2079271 := by exact prefixLift 2079271
  have htrace : WordTrace (prefixWord ++ tailWord_2079271) baseStart_2079271 baseEnd_2079271 := by
    simpa [prefixWord, tailWord_2079271, baseEnd_2079271] using wordTrace_append hprefix tailTrace_2079271
  have hstable : (prefixWord ++ tailWord_2079271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079271).length < 2 ^ (prefixWord ++ tailWord_2079271).sum := by decide
  have hdescent : baseEnd_2079271 < baseStart_2079271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079310 : List Nat := [4, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2079310 : Nat := 118140960795 + 2079310 * 2 ^ 59
def prefixEnd_2079310 : Nat := 4983230072969 + 3 ^ 40 * 2079310 * 2
def baseEnd_2079310 : Nat := 158175623659313322038879

theorem tailTrace_2079310 : CollatzResearch.WordTrace tailWord_2079310 prefixEnd_2079310 158175623659313322038879 := by
  unfold tailWord_2079310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479833262127807840091423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50559110731348308480487589 9479833262127807840091423)
  ·
    refine ⟨14219749893191711760137135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9479833262127807840091423 14219749893191711760137135)
    ·
      refine ⟨21329624839787567640205703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14219749893191711760137135 21329624839787567640205703)
      ·
        refine ⟨31994437259681351460308555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21329624839787567640205703 31994437259681351460308555)
        ·
          refine ⟨47991655889522027190462833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31994437259681351460308555 47991655889522027190462833)
          ·
            refine ⟨35993741917141520392847125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47991655889522027190462833 35993741917141520392847125)
            ·
              refine ⟨1687206652366008768414709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35993741917141520392847125 1687206652366008768414709)
              ·
                refine ⟨158175623659313322038879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1687206652366008768414709 158175623659313322038879)
                ·
                  rfl

theorem cell21_2079310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2079310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079310 prefixEnd_2079310 := by exact prefixLift 2079310
  have htrace : WordTrace (prefixWord ++ tailWord_2079310) baseStart_2079310 baseEnd_2079310 := by
    simpa [prefixWord, tailWord_2079310, baseEnd_2079310] using wordTrace_append hprefix tailTrace_2079310
  have hstable : (prefixWord ++ tailWord_2079310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079310).length < 2 ^ (prefixWord ++ tailWord_2079310).sum := by decide
  have hdescent : baseEnd_2079310 < baseStart_2079310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079341 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2079341 : Nat := 118140960795 + 2079341 * 2 ^ 59
def prefixEnd_2079341 : Nat := 4983230072969 + 3 ^ 40 * 2079341 * 2
def baseEnd_2079341 : Nat := 474533945600290801099907

theorem tailTrace_2079341 : CollatzResearch.WordTrace tailWord_2079341 prefixEnd_2079341 474533945600290801099907 := by
  unfold tailWord_2079341
  simp only [CollatzResearch.WordTrace]
  refine ⟨75839796759910155015109877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50559864506606770010073251 75839796759910155015109877)
  ·
    refine ⟨7109980946241577032666551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75839796759910155015109877 7109980946241577032666551)
    ·
      refine ⟨10664971419362365548999827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109980946241577032666551 10664971419362365548999827)
      ·
        refine ⟨15997457129043548323499741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664971419362365548999827 15997457129043548323499741)
        ·
          refine ⟨5999046423391330621312403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15997457129043548323499741 5999046423391330621312403)
          ·
            refine ⟨8998569635086995931968605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999046423391330621312403 8998569635086995931968605)
            ·
              refine ⟨3374463613157623474488227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998569635086995931968605 3374463613157623474488227)
              ·
                refine ⟨5061695419736435211732341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374463613157623474488227 5061695419736435211732341)
                ·
                  refine ⟨474533945600290801099907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061695419736435211732341 474533945600290801099907)
                  ·
                    rfl

theorem cell21_2079341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2079341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079341 prefixEnd_2079341 := by exact prefixLift 2079341
  have htrace : WordTrace (prefixWord ++ tailWord_2079341) baseStart_2079341 baseEnd_2079341 := by
    simpa [prefixWord, tailWord_2079341, baseEnd_2079341] using wordTrace_append hprefix tailTrace_2079341
  have hstable : (prefixWord ++ tailWord_2079341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079341).length < 2 ^ (prefixWord ++ tailWord_2079341).sum := by decide
  have hdescent : baseEnd_2079341 < baseStart_2079341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079386 : List Nat := [3, 1, 1, 6, 1, 9]
def baseStart_2079386 : Nat := 118140960795 + 2079386 * 2 ^ 59
def prefixEnd_2079386 : Nat := 4983230072969 + 3 ^ 40 * 2079386 * 2
def baseEnd_2079386 : Nat := 17575711674569656401845

theorem tailTrace_2079386 : CollatzResearch.WordTrace tailWord_2079386 prefixEnd_2079386 17575711674569656401845 := by
  unfold tailWord_2079386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960359511186781925124503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50560958696498085133665341 18960359511186781925124503)
  ·
    refine ⟨28440539266780172887686755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18960359511186781925124503 28440539266780172887686755)
    ·
      refine ⟨42660808900170259331530133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28440539266780172887686755 42660808900170259331530133)
      ·
        refine ⟨1999725417195480906165475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42660808900170259331530133 1999725417195480906165475)
        ·
          refine ⟨2999588125793221359248213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999725417195480906165475 2999588125793221359248213)
          ·
            refine ⟨17575711674569656401845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2999588125793221359248213 17575711674569656401845)
            ·
              rfl

theorem cell21_2079386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 9].length) (baseStart_2079386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079386 prefixEnd_2079386 := by exact prefixLift 2079386
  have htrace : WordTrace (prefixWord ++ tailWord_2079386) baseStart_2079386 baseEnd_2079386 := by
    simpa [prefixWord, tailWord_2079386, baseEnd_2079386] using wordTrace_append hprefix tailTrace_2079386
  have hstable : (prefixWord ++ tailWord_2079386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079386).length < 2 ^ (prefixWord ++ tailWord_2079386).sum := by decide
  have hdescent : baseEnd_2079386 < baseStart_2079386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079392 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_2079392 : Nat := 118140960795 + 2079392 * 2 ^ 59
def prefixEnd_2079392 : Nat := 4983230072969 + 3 ^ 40 * 2079392 * 2
def baseEnd_2079392 : Nat := 474545584495126045749803

theorem tailTrace_2079392 : CollatzResearch.WordTrace tailWord_2079392 prefixEnd_2079392 474545584495126045749803 := by
  unfold tailWord_2079392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920828441362695362608215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50561104588483593816810953 37920828441362695362608215)
  ·
    refine ⟨56881242662044043043912323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37920828441362695362608215 56881242662044043043912323)
    ·
      refine ⟨85321863993066064565868485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56881242662044043043912323 85321863993066064565868485)
      ·
        refine ⟨15997849498699887106100341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85321863993066064565868485 15997849498699887106100341)
        ·
          refine ⟨1499798390503114416196907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15997849498699887106100341 1499798390503114416196907)
          ·
            refine ⟨2249697585754671624295361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499798390503114416196907 2249697585754671624295361)
            ·
              refine ⟨1687273189316003718221521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249697585754671624295361 1687273189316003718221521)
              ·
                refine ⟨1265454891987002788666141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687273189316003718221521 1265454891987002788666141)
                ·
                  refine ⟨474545584495126045749803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265454891987002788666141 474545584495126045749803)
                  ·
                    rfl

theorem cell21_2079392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_2079392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079392 prefixEnd_2079392 := by exact prefixLift 2079392
  have htrace : WordTrace (prefixWord ++ tailWord_2079392) baseStart_2079392 baseEnd_2079392 := by
    simpa [prefixWord, tailWord_2079392, baseEnd_2079392] using wordTrace_append hprefix tailTrace_2079392
  have hstable : (prefixWord ++ tailWord_2079392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079392).length < 2 ^ (prefixWord ++ tailWord_2079392).sum := by decide
  have hdescent : baseEnd_2079392 < baseStart_2079392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079434 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_2079434 : Nat := 118140960795 + 2079434 * 2 ^ 59
def prefixEnd_2079434 : Nat := 4983230072969 + 3 ^ 40 * 2079434 * 2
def baseEnd_2079434 : Nat := 474555169467343306049717

theorem tailTrace_2079434 : CollatzResearch.WordTrace tailWord_2079434 prefixEnd_2079434 474555169467343306049717 := by
  unfold tailWord_2079434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960797187143307974561339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50562125832382154598830237 18960797187143307974561339)
  ·
    refine ⟨28441195780714961961842009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18960797187143307974561339 28441195780714961961842009)
    ·
      refine ⟨21330896835536221471381507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28441195780714961961842009 21330896835536221471381507)
      ·
        refine ⟨31996345253304332207072261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21330896835536221471381507 31996345253304332207072261)
        ·
          refine ⟨5999314734994562288826049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31996345253304332207072261 5999314734994562288826049)
          ·
            refine ⟨4499486051245921716619537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5999314734994562288826049 4499486051245921716619537)
            ·
              refine ⟨3374614538434441287464653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499486051245921716619537 3374614538434441287464653)
              ·
                refine ⟨1265480451912915482799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3374614538434441287464653 1265480451912915482799245)
                ·
                  refine ⟨474555169467343306049717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265480451912915482799245 474555169467343306049717)
                  ·
                    rfl

theorem cell21_2079434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_2079434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079434 prefixEnd_2079434 := by exact prefixLift 2079434
  have htrace : WordTrace (prefixWord ++ tailWord_2079434) baseStart_2079434 baseEnd_2079434 := by
    simpa [prefixWord, tailWord_2079434, baseEnd_2079434] using wordTrace_append hprefix tailTrace_2079434
  have hstable : (prefixWord ++ tailWord_2079434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079434).length < 2 ^ (prefixWord ++ tailWord_2079434).sum := by decide
  have hdescent : baseEnd_2079434 < baseStart_2079434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079448 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_2079448 : Nat := 118140960795 + 2079448 * 2 ^ 59
def prefixEnd_2079448 : Nat := 4983230072969 + 3 ^ 40 * 2079448 * 2
def baseEnd_2079448 : Nat := 474558364458082392816355

theorem tailTrace_2079448 : CollatzResearch.WordTrace tailWord_2079448 prefixEnd_2079448 474558364458082392816355 := by
  unfold tailWord_2079448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921849685261256144627499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50562466247015008192836665 37921849685261256144627499)
  ·
    refine ⟨56882774527891884216941249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37921849685261256144627499 56882774527891884216941249)
    ·
      refine ⟨42662080895918913162705937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56882774527891884216941249 42662080895918913162705937)
      ·
        refine ⟨31996560671939184872029453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42662080895918913162705937 31996560671939184872029453)
        ·
          refine ⟨11998710251977194327011045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31996560671939184872029453 11998710251977194327011045)
          ·
            refine ⟨2249758172245723936314571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11998710251977194327011045 2249758172245723936314571)
            ·
              refine ⟨3374637258368585904471857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249758172245723936314571 3374637258368585904471857)
              ·
                refine ⟨2530977943776439428353893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374637258368585904471857 2530977943776439428353893)
                ·
                  refine ⟨474558364458082392816355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530977943776439428353893 474558364458082392816355)
                  ·
                    rfl

theorem cell21_2079448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_2079448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079448 prefixEnd_2079448 := by exact prefixLift 2079448
  have htrace : WordTrace (prefixWord ++ tailWord_2079448) baseStart_2079448 baseEnd_2079448 := by
    simpa [prefixWord, tailWord_2079448, baseEnd_2079448] using wordTrace_append hprefix tailTrace_2079448
  have hstable : (prefixWord ++ tailWord_2079448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079448).length < 2 ^ (prefixWord ++ tailWord_2079448).sum := by decide
  have hdescent : baseEnd_2079448 < baseStart_2079448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079521 : List Nat := [1, 2, 3, 2, 1, 2, 4, 6]
def baseStart_2079521 : Nat := 118140960795 + 2079521 * 2 ^ 59
def prefixEnd_2079521 : Nat := 4983230072969 + 3 ^ 40 * 2079521 * 2
def baseEnd_2079521 : Nat := 158191674684216829366513

theorem tailTrace_2079521 : CollatzResearch.WordTrace tailWord_2079521 prefixEnd_2079521 158191674684216829366513 := by
  unfold tailWord_2079521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75846361899258045756662417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50564241266172030504441611 75846361899258045756662417)
  ·
    refine ⟨56884771424443534317496813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75846361899258045756662417 56884771424443534317496813)
    ·
      refine ⟨21331789284166325369061305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56884771424443534317496813 21331789284166325369061305)
      ·
        refine ⟨15998841963124744026795979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21331789284166325369061305 15998841963124744026795979)
        ·
          refine ⟨23998262944687116040193969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998841963124744026795979 23998262944687116040193969)
          ·
            refine ⟨17998697208515337030145477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23998262944687116040193969 17998697208515337030145477)
            ·
              refine ⟨3374755726596625693152277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17998697208515337030145477 3374755726596625693152277)
              ·
                refine ⟨158191674684216829366513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3374755726596625693152277 158191674684216829366513)
                ·
                  rfl

theorem cell21_2079521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_2079521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079521 prefixEnd_2079521 := by exact prefixLift 2079521
  have htrace : WordTrace (prefixWord ++ tailWord_2079521) baseStart_2079521 baseEnd_2079521 := by
    simpa [prefixWord, tailWord_2079521, baseEnd_2079521] using wordTrace_append hprefix tailTrace_2079521
  have hstable : (prefixWord ++ tailWord_2079521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079521).length < 2 ^ (prefixWord ++ tailWord_2079521).sum := by decide
  have hdescent : baseEnd_2079521 < baseStart_2079521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079524 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_2079524 : Nat := 118140960795 + 2079524 * 2 ^ 59
def prefixEnd_2079524 : Nat := 4983230072969 + 3 ^ 40 * 2079524 * 2
def baseEnd_2079524 : Nat := 474575708693523149549533

theorem tailTrace_2079524 : CollatzResearch.WordTrace tailWord_2079524 prefixEnd_2079524 474575708693523149549533 := by
  unfold tailWord_2079524
  simp only [CollatzResearch.WordTrace]
  refine ⟨37923235659123588634510813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50564314212164784846014417 37923235659123588634510813)
  ·
    refine ⟨14221213372171345737941555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37923235659123588634510813 14221213372171345737941555)
    ·
      refine ⟨21331820058257018606912333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221213372171345737941555 21331820058257018606912333)
      ·
        refine ⟨7999432521846381977592125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21331820058257018606912333 7999432521846381977592125)
        ·
          refine ⟨2999787195692393241597047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7999432521846381977592125 2999787195692393241597047)
          ·
            refine ⟨4499680793538589862395571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999787195692393241597047 4499680793538589862395571)
            ·
              refine ⟨6749521190307884793593357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499680793538589862395571 6749521190307884793593357)
              ·
                refine ⟨2531070446365456797597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6749521190307884793593357 2531070446365456797597509)
                ·
                  refine ⟨474575708693523149549533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531070446365456797597509 474575708693523149549533)
                  ·
                    rfl

theorem cell21_2079524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_2079524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079524 prefixEnd_2079524 := by exact prefixLift 2079524
  have htrace : WordTrace (prefixWord ++ tailWord_2079524) baseStart_2079524 baseEnd_2079524 := by
    simpa [prefixWord, tailWord_2079524, baseEnd_2079524] using wordTrace_append hprefix tailTrace_2079524
  have hstable : (prefixWord ++ tailWord_2079524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079524).length < 2 ^ (prefixWord ++ tailWord_2079524).sum := by decide
  have hdescent : baseEnd_2079524 < baseStart_2079524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079558 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2079558 : Nat := 118140960795 + 2079558 * 2 ^ 59
def prefixEnd_2079558 : Nat := 4983230072969 + 3 ^ 40 * 2079558 * 2
def baseEnd_2079558 : Nat := 474583467956746645982797

theorem tailTrace_2079558 : CollatzResearch.WordTrace tailWord_2079558 prefixEnd_2079558 474583467956746645982797 := by
  unfold tailWord_2079558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370240981253875033617479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50565140933416000717172885 2370240981253875033617479)
  ·
    refine ⟨3555361471880812550426219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370240981253875033617479 3555361471880812550426219)
    ·
      refine ⟨5333042207821218825639329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555361471880812550426219 5333042207821218825639329)
      ·
        refine ⟨3999781655865914119229497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5333042207821218825639329 3999781655865914119229497)
        ·
          refine ⟨2999836241899435589422123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999781655865914119229497 2999836241899435589422123)
          ·
            refine ⟨4499754362849153384133185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999836241899435589422123 4499754362849153384133185)
            ·
              refine ⟨3374815772136865038099889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499754362849153384133185 3374815772136865038099889)
              ·
                refine ⟨2531111829102648778574917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374815772136865038099889 2531111829102648778574917)
                ·
                  refine ⟨474583467956746645982797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531111829102648778574917 474583467956746645982797)
                  ·
                    rfl

theorem cell21_2079558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2079558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079558 prefixEnd_2079558 := by exact prefixLift 2079558
  have htrace : WordTrace (prefixWord ++ tailWord_2079558) baseStart_2079558 baseEnd_2079558 := by
    simpa [prefixWord, tailWord_2079558, baseEnd_2079558] using wordTrace_append hprefix tailTrace_2079558
  have hstable : (prefixWord ++ tailWord_2079558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079558).length < 2 ^ (prefixWord ++ tailWord_2079558).sum := by decide
  have hdescent : baseEnd_2079558 < baseStart_2079558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079566 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2079566 : Nat := 118140960795 + 2079566 * 2 ^ 59
def prefixEnd_2079566 : Nat := 4983230072969 + 3 ^ 40 * 2079566 * 2
def baseEnd_2079566 : Nat := 474585293665740409849447

theorem tailTrace_2079566 : CollatzResearch.WordTrace tailWord_2079566 prefixEnd_2079566 474585293665740409849447 := by
  unfold tailWord_2079566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481000398011877305256319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50565335456063345628033701 9481000398011877305256319)
  ·
    refine ⟨14221500597017815957884479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481000398011877305256319 14221500597017815957884479)
    ·
      refine ⟨21332250895526723936826719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221500597017815957884479 21332250895526723936826719)
      ·
        refine ⟨31998376343290085905240079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21332250895526723936826719 31998376343290085905240079)
        ·
          refine ⟨47997564514935128857860119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31998376343290085905240079 47997564514935128857860119)
          ·
            refine ⟨71996346772402693286790179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47997564514935128857860119 71996346772402693286790179)
            ·
              refine ⟨107994520158604039930185269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71996346772402693286790179 107994520158604039930185269)
              ·
                refine ⟨10124486264869128743454869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107994520158604039930185269 10124486264869128743454869)
                ·
                  refine ⟨474585293665740409849447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10124486264869128743454869 474585293665740409849447)
                  ·
                    rfl

theorem cell21_2079566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2079566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079566 prefixEnd_2079566 := by exact prefixLift 2079566
  have htrace : WordTrace (prefixWord ++ tailWord_2079566) baseStart_2079566 baseEnd_2079566 := by
    simpa [prefixWord, tailWord_2079566, baseEnd_2079566] using wordTrace_append hprefix tailTrace_2079566
  have hstable : (prefixWord ++ tailWord_2079566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079566).length < 2 ^ (prefixWord ++ tailWord_2079566).sum := by decide
  have hdescent : baseEnd_2079566 < baseStart_2079566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079673 : List Nat := [1, 2, 1, 4, 2, 4, 7]
def baseStart_2079673 : Nat := 118140960795 + 2079673 * 2 ^ 59
def prefixEnd_2079673 : Nat := 4983230072969 + 3 ^ 40 * 2079673 * 2
def baseEnd_2079673 : Nat := 52734412502614666840655

theorem tailTrace_2079673 : CollatzResearch.WordTrace tailWord_2079673 prefixEnd_2079673 52734412502614666840655 := by
  unfold tailWord_2079673
  simp only [CollatzResearch.WordTrace]
  refine ⟨75851905794707375716195673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50567937196471583810797115 75851905794707375716195673)
  ·
    refine ⟨56888929346030531787146755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75851905794707375716195673 56888929346030531787146755)
    ·
      refine ⟨85333394019045797680720133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56888929346030531787146755 85333394019045797680720133)
      ·
        refine ⟨16000011378571087065135025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85333394019045797680720133 16000011378571087065135025)
        ·
          refine ⟨12000008533928315298851269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16000011378571087065135025 12000008533928315298851269)
          ·
            refine ⟨2250001600111559118534613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12000008533928315298851269 2250001600111559118534613)
            ·
              refine ⟨52734412502614666840655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2250001600111559118534613 52734412502614666840655)
              ·
                rfl

theorem cell21_2079673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 7].length) (baseStart_2079673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079673 prefixEnd_2079673 := by exact prefixLift 2079673
  have htrace : WordTrace (prefixWord ++ tailWord_2079673) baseStart_2079673 baseEnd_2079673 := by
    simpa [prefixWord, tailWord_2079673, baseEnd_2079673] using wordTrace_append hprefix tailTrace_2079673
  have hstable : (prefixWord ++ tailWord_2079673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079673).length < 2 ^ (prefixWord ++ tailWord_2079673).sum := by decide
  have hdescent : baseEnd_2079673 < baseStart_2079673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079794 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2079794 : Nat := 118140960795 + 2079794 * 2 ^ 59
def prefixEnd_2079794 : Nat := 4983230072969 + 3 ^ 40 * 2079794 * 2
def baseEnd_2079794 : Nat := 474637326372062680048981

theorem tailTrace_2079794 : CollatzResearch.WordTrace tailWord_2079794 prefixEnd_2079794 474637326372062680048981 := by
  unfold tailWord_2079794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964079756817253345337609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50570879351512675587566957 18964079756817253345337609)
  ·
    refine ⟨14223059817612940009003207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18964079756817253345337609 14223059817612940009003207)
    ·
      refine ⟨21334589726419410013504811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14223059817612940009003207 21334589726419410013504811)
      ·
        refine ⟨32001884589629115020257217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334589726419410013504811 32001884589629115020257217)
        ·
          refine ⟨24001413442221836265192913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32001884589629115020257217 24001413442221836265192913)
          ·
            refine ⟨18001060081666377198894685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24001413442221836265192913 18001060081666377198894685)
            ·
              refine ⟨6750397530624891449585507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18001060081666377198894685 6750397530624891449585507)
              ·
                refine ⟨10125596295937337174378261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750397530624891449585507 10125596295937337174378261)
                ·
                  refine ⟨474637326372062680048981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10125596295937337174378261 474637326372062680048981)
                  ·
                    rfl

theorem cell21_2079794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2079794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079794 prefixEnd_2079794 := by exact prefixLift 2079794
  have htrace : WordTrace (prefixWord ++ tailWord_2079794) baseStart_2079794 baseEnd_2079794 := by
    simpa [prefixWord, tailWord_2079794, baseEnd_2079794] using wordTrace_append hprefix tailTrace_2079794
  have hstable : (prefixWord ++ tailWord_2079794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079794).length < 2 ^ (prefixWord ++ tailWord_2079794).sum := by decide
  have hdescent : baseEnd_2079794 < baseStart_2079794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079808 : List Nat := [2, 1, 1, 2, 2, 3, 2, 8]
def baseStart_2079808 : Nat := 118140960795 + 2079808 * 2 ^ 59
def prefixEnd_2079808 : Nat := 4983230072969 + 3 ^ 40 * 2079808 * 2
def baseEnd_2079808 : Nat := 158213507120933922271873

theorem tailTrace_2079808 : CollatzResearch.WordTrace tailWord_2079808 prefixEnd_2079808 158213507120933922271873 := by
  unfold tailWord_2079808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37928414824609146886180039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50571219766145529181573385 37928414824609146886180039)
  ·
    refine ⟨56892622236913720329270059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37928414824609146886180039 56892622236913720329270059)
    ·
      refine ⟨85338933355370580493905089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56892622236913720329270059 85338933355370580493905089)
      ·
        refine ⟨64004200016527935370428817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85338933355370580493905089 64004200016527935370428817)
        ·
          refine ⟨48003150012395951527821613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64004200016527935370428817 48003150012395951527821613)
          ·
            refine ⟨18001181254648481822933105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48003150012395951527821613 18001181254648481822933105)
            ·
              refine ⟨13500885940986361367199829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18001181254648481822933105 13500885940986361367199829)
              ·
                refine ⟨158213507120933922271873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13500885940986361367199829 158213507120933922271873)
                ·
                  rfl

theorem cell21_2079808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_2079808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079808 prefixEnd_2079808 := by exact prefixLift 2079808
  have htrace : WordTrace (prefixWord ++ tailWord_2079808) baseStart_2079808 baseEnd_2079808 := by
    simpa [prefixWord, tailWord_2079808, baseEnd_2079808] using wordTrace_append hprefix tailTrace_2079808
  have hstable : (prefixWord ++ tailWord_2079808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079808).length < 2 ^ (prefixWord ++ tailWord_2079808).sum := by decide
  have hdescent : baseEnd_2079808 < baseStart_2079808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079811 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 4]
def baseStart_2079811 : Nat := 118140960795 + 2079811 * 2 ^ 59
def prefixEnd_2079811 : Nat := 4983230072969 + 3 ^ 40 * 2079811 * 2
def baseEnd_2079811 : Nat := 474641206003674428265613

theorem tailTrace_2079811 : CollatzResearch.WordTrace tailWord_2079811 prefixEnd_2079811 474641206003674428265613 := by
  unfold tailWord_2079811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75856939068207425284719287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50571292712138283523146191 75856939068207425284719287)
  ·
    refine ⟨113785408602311137927078931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75856939068207425284719287 113785408602311137927078931)
    ·
      refine ⟨170678112903466706890618397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113785408602311137927078931 170678112903466706890618397)
      ·
        refine ⟨64004292338800015083981899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170678112903466706890618397 64004292338800015083981899)
        ·
          refine ⟨96006438508200022625972849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64004292338800015083981899 96006438508200022625972849)
          ·
            refine ⟨72004828881150016969479637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96006438508200022625972849 72004828881150016969479637)
            ·
              refine ⟨1687613176901953522722179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72004828881150016969479637 1687613176901953522722179)
              ·
                refine ⟨2531419765352930284083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687613176901953522722179 2531419765352930284083269)
                ·
                  refine ⟨474641206003674428265613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531419765352930284083269 474641206003674428265613)
                  ·
                    rfl

theorem cell21_2079811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_2079811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079811 prefixEnd_2079811 := by exact prefixLift 2079811
  have htrace : WordTrace (prefixWord ++ tailWord_2079811) baseStart_2079811 baseEnd_2079811 := by
    simpa [prefixWord, tailWord_2079811, baseEnd_2079811] using wordTrace_append hprefix tailTrace_2079811
  have hstable : (prefixWord ++ tailWord_2079811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079811).length < 2 ^ (prefixWord ++ tailWord_2079811).sum := by decide
  have hdescent : baseEnd_2079811 < baseStart_2079811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079825 : List Nat := [1, 2, 2, 1, 3, 1, 6, 5]
def baseStart_2079825 : Nat := 118140960795 + 2079825 * 2 ^ 59
def prefixEnd_2079825 : Nat := 4983230072969 + 3 ^ 40 * 2079825 * 2
def baseEnd_2079825 : Nat := 158214800331471171677417

theorem tailTrace_2079825 : CollatzResearch.WordTrace tailWord_2079825 prefixEnd_2079825 158214800331471171677417 := by
  unfold tailWord_2079825
  simp only [CollatzResearch.WordTrace]
  refine ⟨75857449690156705675728929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50571633126771137117152619 75857449690156705675728929)
  ·
    refine ⟨56893087267617529256796697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75857449690156705675728929 56893087267617529256796697)
    ·
      refine ⟨42669815450713146942597523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56893087267617529256796697 42669815450713146942597523)
      ·
        refine ⟨64004723176069720413896285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42669815450713146942597523 64004723176069720413896285)
        ·
          refine ⟨24001771191026145155211107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64004723176069720413896285 24001771191026145155211107)
          ·
            refine ⟨36002656786539217732816661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24001771191026145155211107 36002656786539217732816661)
            ·
              refine ⟨1687624536869025831225781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36002656786539217732816661 1687624536869025831225781)
              ·
                refine ⟨158214800331471171677417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1687624536869025831225781 158214800331471171677417)
                ·
                  rfl

theorem cell21_2079825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].length) (baseStart_2079825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079825 prefixEnd_2079825 := by exact prefixLift 2079825
  have htrace : WordTrace (prefixWord ++ tailWord_2079825) baseStart_2079825 baseEnd_2079825 := by
    simpa [prefixWord, tailWord_2079825, baseEnd_2079825] using wordTrace_append hprefix tailTrace_2079825
  have hstable : (prefixWord ++ tailWord_2079825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079825).length < 2 ^ (prefixWord ++ tailWord_2079825).sum := by decide
  have hdescent : baseEnd_2079825 < baseStart_2079825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079842 : List Nat := [3, 3, 2, 2, 1, 3, 7]
def baseStart_2079842 : Nat := 118140960795 + 2079842 * 2 ^ 59
def prefixEnd_2079842 : Nat := 4983230072969 + 3 ^ 40 * 2079842 * 2
def baseEnd_2079842 : Nat := 52738697847336140360987

theorem tailTrace_2079842 : CollatzResearch.WordTrace tailWord_2079842 prefixEnd_2079842 52738697847336140360987 := by
  unfold tailWord_2079842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964517432773779394774445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50572046487396745052731853 18964517432773779394774445)
  ·
    refine ⟨7111694037290167273040417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18964517432773779394774445 7111694037290167273040417)
    ·
      refine ⟨5333770527967625454780313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7111694037290167273040417 5333770527967625454780313)
      ·
        refine ⟨4000327895975719091085235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5333770527967625454780313 4000327895975719091085235)
        ·
          refine ⟨6000491843963578636627853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000327895975719091085235 6000491843963578636627853)
          ·
            refine ⟨2250184441486341988735445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6000491843963578636627853 2250184441486341988735445)
            ·
              refine ⟨52738697847336140360987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2250184441486341988735445 52738697847336140360987)
              ·
                rfl

theorem cell21_2079842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 7].length) (baseStart_2079842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079842 prefixEnd_2079842 := by exact prefixLift 2079842
  have htrace : WordTrace (prefixWord ++ tailWord_2079842) baseStart_2079842 baseEnd_2079842 := by
    simpa [prefixWord, tailWord_2079842, baseEnd_2079842] using wordTrace_append hprefix tailTrace_2079842
  have hstable : (prefixWord ++ tailWord_2079842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079842).length < 2 ^ (prefixWord ++ tailWord_2079842).sum := by decide
  have hdescent : baseEnd_2079842 < baseStart_2079842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079932 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_2079932 : Nat := 118140960795 + 2079932 * 2 ^ 59
def prefixEnd_2079932 : Nat := 4983230072969 + 3 ^ 40 * 2079932 * 2
def baseEnd_2079932 : Nat := 474668819852205106748699

theorem tailTrace_2079932 : CollatzResearch.WordTrace tailWord_2079932 prefixEnd_2079932 474668819852205106748699 := by
  unfold tailWord_2079932
  simp only [CollatzResearch.WordTrace]
  refine ⟨37930676150384531474937025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50574234867179375299916033 37930676150384531474937025)
  ·
    refine ⟨28448007112788398606202769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37930676150384531474937025 28448007112788398606202769)
    ·
      refine ⟨21336005334591298954652077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28448007112788398606202769 21336005334591298954652077)
      ·
        refine ⟨8001002000471737107994529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21336005334591298954652077 8001002000471737107994529)
        ·
          refine ⟨6000751500353802830995897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8001002000471737107994529 6000751500353802830995897)
          ·
            refine ⟨4500563625265352123246923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000751500353802830995897 4500563625265352123246923)
            ·
              refine ⟨6750845437898028184870385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500563625265352123246923 6750845437898028184870385)
              ·
                refine ⟨5063134078423521138652789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750845437898028184870385 5063134078423521138652789)
                ·
                  refine ⟨474668819852205106748699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063134078423521138652789 474668819852205106748699)
                  ·
                    rfl

theorem cell21_2079932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_2079932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2079932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2079932 prefixEnd_2079932 := by exact prefixLift 2079932
  have htrace : WordTrace (prefixWord ++ tailWord_2079932) baseStart_2079932 baseEnd_2079932 := by
    simpa [prefixWord, tailWord_2079932, baseEnd_2079932] using wordTrace_append hprefix tailTrace_2079932
  have hstable : (prefixWord ++ tailWord_2079932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079932).length < 2 ^ (prefixWord ++ tailWord_2079932).sum := by decide
  have hdescent : baseEnd_2079932 < baseStart_2079932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080005 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2080005 : Nat := 118140960795 + 2080005 * 2 ^ 59
def prefixEnd_2080005 : Nat := 4983230072969 + 3 ^ 40 * 2080005 * 2
def baseEnd_2080005 : Nat := 474685479446773202031883

theorem tailTrace_2080005 : CollatzResearch.WordTrace tailWord_2080005 prefixEnd_2080005 474685479446773202031883 := by
  unfold tailWord_2080005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75864014829504596417281469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50576009886336397611520979 75864014829504596417281469)
  ·
    refine ⟨28449005561064223656480551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75864014829504596417281469 28449005561064223656480551)
    ·
      refine ⟨42673508341596335484720827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449005561064223656480551 42673508341596335484720827)
      ·
        refine ⟨64010262512394503227081241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42673508341596335484720827 64010262512394503227081241)
        ·
          refine ⟨48007696884295877420310931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64010262512394503227081241 48007696884295877420310931)
          ·
            refine ⟨72011545326443816130466397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48007696884295877420310931 72011545326443816130466397)
            ·
              refine ⟨27004329497416431048924899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72011545326443816130466397 27004329497416431048924899)
              ·
                refine ⟨40506494246124646573387349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27004329497416431048924899 40506494246124646573387349)
                ·
                  refine ⟨474685479446773202031883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40506494246124646573387349 474685479446773202031883)
                  ·
                    rfl

theorem cell21_2080005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2080005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080005 prefixEnd_2080005 := by exact prefixLift 2080005
  have htrace : WordTrace (prefixWord ++ tailWord_2080005) baseStart_2080005 baseEnd_2080005 := by
    simpa [prefixWord, tailWord_2080005, baseEnd_2080005] using wordTrace_append hprefix tailTrace_2080005
  have hstable : (prefixWord ++ tailWord_2080005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080005).length < 2 ^ (prefixWord ++ tailWord_2080005).sum := by decide
  have hdescent : baseEnd_2080005 < baseStart_2080005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080070 : List Nat := [6, 1, 1, 3, 10]
def baseStart_2080070 : Nat := 118140960795 + 2080070 * 2 ^ 59
def prefixEnd_2080070 : Nat := 4983230072969 + 3 ^ 40 * 2080070 * 2
def baseEnd_2080070 : Nat := 5860497695461080659857

theorem tailTrace_2080070 : CollatzResearch.WordTrace tailWord_2080070 prefixEnd_2080070 5860497695461080659857 := by
  unfold tailWord_2080070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370824549195909766199927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50577590382846075012265109 2370824549195909766199927)
  ·
    refine ⟨3556236823793864649299891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370824549195909766199927 3556236823793864649299891)
    ·
      refine ⟨5334355235690796973949837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556236823793864649299891 5334355235690796973949837)
      ·
        refine ⟨2000383213384048865231189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5334355235690796973949837 2000383213384048865231189)
        ·
          refine ⟨5860497695461080659857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 2000383213384048865231189 5860497695461080659857)
          ·
            rfl

theorem cell21_2080070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 10].length) (baseStart_2080070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080070 prefixEnd_2080070 := by exact prefixLift 2080070
  have htrace : WordTrace (prefixWord ++ tailWord_2080070) baseStart_2080070 baseEnd_2080070 := by
    simpa [prefixWord, tailWord_2080070, baseEnd_2080070] using wordTrace_append hprefix tailTrace_2080070
  have hstable : (prefixWord ++ tailWord_2080070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080070).length < 2 ^ (prefixWord ++ tailWord_2080070).sum := by decide
  have hdescent : baseEnd_2080070 < baseStart_2080070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080129 : List Nat := [1, 2, 4, 3, 2, 1, 8]
def baseStart_2080129 : Nat := 118140960795 + 2080129 * 2 ^ 59
def prefixEnd_2080129 : Nat := 4983230072969 + 3 ^ 40 * 2080129 * 2
def baseEnd_2080129 : Nat := 52745975326241837996107

theorem tailTrace_2080129 : CollatzResearch.WordTrace tailWord_2080129 prefixEnd_2080129 52745975326241837996107 := by
  unfold tailWord_2080129
  simp only [CollatzResearch.WordTrace]
  refine ⟨75868537481055365594795441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50579024987370243729863627 75868537481055365594795441)
  ·
    refine ⟨56901403110791524196096581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75868537481055365594795441 56901403110791524196096581)
    ·
      refine ⟨10669013083273410786768109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56901403110791524196096581 10669013083273410786768109)
      ·
        refine ⟨4000879906227529045038041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10669013083273410786768109 4000879906227529045038041)
        ·
          refine ⟨3000659929670646783778531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000879906227529045038041 3000659929670646783778531)
          ·
            refine ⟨4500989894505970175667797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000659929670646783778531 4500989894505970175667797)
            ·
              refine ⟨52745975326241837996107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4500989894505970175667797 52745975326241837996107)
              ·
                rfl

theorem cell21_2080129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 8].length) (baseStart_2080129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080129 prefixEnd_2080129 := by exact prefixLift 2080129
  have htrace : WordTrace (prefixWord ++ tailWord_2080129) baseStart_2080129 baseEnd_2080129 := by
    simpa [prefixWord, tailWord_2080129, baseEnd_2080129] using wordTrace_append hprefix tailTrace_2080129
  have hstable : (prefixWord ++ tailWord_2080129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080129).length < 2 ^ (prefixWord ++ tailWord_2080129).sum := by decide
  have hdescent : baseEnd_2080129 < baseStart_2080129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080250 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_2080250 : Nat := 118140960795 + 2080250 * 2 ^ 59
def prefixEnd_2080250 : Nat := 4983230072969 + 3 ^ 40 * 2080250 * 2
def baseEnd_2080250 : Nat := 474741391784707220448049

theorem tailTrace_2080250 : CollatzResearch.WordTrace tailWord_2080250 prefixEnd_2080250 474741391784707220448049 := by
  unfold tailWord_2080250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18968237678404250814987551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50581967142411335506633469 18968237678404250814987551)
  ·
    refine ⟨28452356517606376222481327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18968237678404250814987551 28452356517606376222481327)
    ·
      refine ⟨42678534776409564333721991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28452356517606376222481327 42678534776409564333721991)
      ·
        refine ⟨64017802164614346500582987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42678534776409564333721991 64017802164614346500582987)
        ·
          refine ⟨96026703246921519750874481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64017802164614346500582987 96026703246921519750874481)
          ·
            refine ⟨72020027435191139813155861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96026703246921519750874481 72020027435191139813155861)
            ·
              refine ⟨3375938786024584678741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72020027435191139813155861 3375938786024584678741681)
              ·
                refine ⟨2531954089518438509056261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375938786024584678741681 2531954089518438509056261)
                ·
                  refine ⟨474741391784707220448049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531954089518438509056261 474741391784707220448049)
                  ·
                    rfl

theorem cell21_2080250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_2080250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080250 prefixEnd_2080250 := by exact prefixLift 2080250
  have htrace : WordTrace (prefixWord ++ tailWord_2080250) baseStart_2080250 baseEnd_2080250 := by
    simpa [prefixWord, tailWord_2080250, baseEnd_2080250] using wordTrace_append hprefix tailTrace_2080250
  have hstable : (prefixWord ++ tailWord_2080250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080250).length < 2 ^ (prefixWord ++ tailWord_2080250).sum := by decide
  have hdescent : baseEnd_2080250 < baseStart_2080250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080253 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 3]
def baseStart_2080253 : Nat := 118140960795 + 2080253 * 2 ^ 59
def prefixEnd_2080253 : Nat := 4983230072969 + 3 ^ 40 * 2080253 * 2
def baseEnd_2080253 : Nat := 474742076425579881898043

theorem tailTrace_2080253 : CollatzResearch.WordTrace tailWord_2080253 prefixEnd_2080253 474742076425579881898043 := by
  unfold tailWord_2080253
  simp only [CollatzResearch.WordTrace]
  refine ⟨75873060132606134772309413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50582040088404089848206275 75873060132606134772309413)
  ·
    refine ⟨14226198774863650269808015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75873060132606134772309413 14226198774863650269808015)
    ·
      refine ⟨21339298162295475404712023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14226198774863650269808015 21339298162295475404712023)
      ·
        refine ⟨32008947243443213107068035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21339298162295475404712023 32008947243443213107068035)
        ·
          refine ⟨48013420865164819660602053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32008947243443213107068035 48013420865164819660602053)
          ·
            refine ⟨9002516412218403686362885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48013420865164819660602053 9002516412218403686362885)
            ·
              refine ⟨1687971827290950691193041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9002516412218403686362885 1687971827290950691193041)
              ·
                refine ⟨1265978870468213018394781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687971827290950691193041 1265978870468213018394781)
                ·
                  refine ⟨474742076425579881898043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265978870468213018394781 474742076425579881898043)
                  ·
                    rfl

theorem cell21_2080253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_2080253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080253 prefixEnd_2080253 := by exact prefixLift 2080253
  have htrace : WordTrace (prefixWord ++ tailWord_2080253) baseStart_2080253 baseEnd_2080253 := by
    simpa [prefixWord, tailWord_2080253, baseEnd_2080253] using wordTrace_append hprefix tailTrace_2080253
  have hstable : (prefixWord ++ tailWord_2080253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080253).length < 2 ^ (prefixWord ++ tailWord_2080253).sum := by decide
  have hdescent : baseEnd_2080253 < baseStart_2080253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080264 : List Nat := [2, 1, 3, 2, 1, 1, 5, 6]
def baseStart_2080264 : Nat := 118140960795 + 2080264 * 2 ^ 59
def prefixEnd_2080264 : Nat := 4983230072969 + 3 ^ 40 * 2080264 * 2
def baseEnd_2080264 : Nat := 158248195591815435738229

theorem tailTrace_2080264 : CollatzResearch.WordTrace tailWord_2080264 prefixEnd_2080264 158248195591815435738229 := by
  unfold tailWord_2080264
  simp only [CollatzResearch.WordTrace]
  refine ⟨37936730667783141825479923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50582307557044189100639897 37936730667783141825479923)
  ·
    refine ⟨56905096001674712738219885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37936730667783141825479923 56905096001674712738219885)
    ·
      refine ⟨21339411000628017276832457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56905096001674712738219885 21339411000628017276832457)
      ·
        refine ⟨16004558250471012957624343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21339411000628017276832457 16004558250471012957624343)
        ·
          refine ⟨24006837375706519436436515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16004558250471012957624343 24006837375706519436436515)
          ·
            refine ⟨36010256063559779154654773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24006837375706519436436515 36010256063559779154654773)
            ·
              refine ⟨3375961505958729295748885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36010256063559779154654773 3375961505958729295748885)
              ·
                refine ⟨158248195591815435738229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3375961505958729295748885 158248195591815435738229)
                ·
                  rfl

theorem cell21_2080264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_2080264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080264 prefixEnd_2080264 := by exact prefixLift 2080264
  have htrace : WordTrace (prefixWord ++ tailWord_2080264) baseStart_2080264 baseEnd_2080264 := by
    simpa [prefixWord, tailWord_2080264, baseEnd_2080264] using wordTrace_append hprefix tailTrace_2080264
  have hstable : (prefixWord ++ tailWord_2080264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080264).length < 2 ^ (prefixWord ++ tailWord_2080264).sum := by decide
  have hdescent : baseEnd_2080264 < baseStart_2080264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080312 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_2080312 : Nat := 118140960795 + 2080312 * 2 ^ 59
def prefixEnd_2080312 : Nat := 4983230072969 + 3 ^ 40 * 2080312 * 2
def baseEnd_2080312 : Nat := 474755541029408890414589

theorem tailTrace_2080312 : CollatzResearch.WordTrace tailWord_2080312 prefixEnd_2080312 474755541029408890414589 := by
  unfold tailWord_2080312
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937606019696193924353595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50583474692928258565804793 37937606019696193924353595)
  ·
    refine ⟨56906409029544290886530393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37937606019696193924353595 56906409029544290886530393)
    ·
      refine ⟨42679806772158218164897795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56906409029544290886530393 42679806772158218164897795)
      ·
        refine ⟨64019710158237327247346693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42679806772158218164897795 64019710158237327247346693)
        ·
          refine ⟨12003695654669498858877505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64019710158237327247346693 12003695654669498858877505)
          ·
            refine ⟨9002771741002124144158129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12003695654669498858877505 9002771741002124144158129)
            ·
              refine ⟨6752078805751593108118597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9002771741002124144158129 6752078805751593108118597)
              ·
                refine ⟨1266014776078423707772237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6752078805751593108118597 1266014776078423707772237)
                ·
                  refine ⟨474755541029408890414589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266014776078423707772237 474755541029408890414589)
                  ·
                    rfl

theorem cell21_2080312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_2080312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080312 prefixEnd_2080312 := by exact prefixLift 2080312
  have htrace : WordTrace (prefixWord ++ tailWord_2080312) baseStart_2080312 baseEnd_2080312 := by
    simpa [prefixWord, tailWord_2080312, baseEnd_2080312] using wordTrace_append hprefix tailTrace_2080312
  have hstable : (prefixWord ++ tailWord_2080312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080312).length < 2 ^ (prefixWord ++ tailWord_2080312).sum := by decide
  have hdescent : baseEnd_2080312 < baseStart_2080312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080340 : List Nat := [2, 4, 1, 1, 1, 2, 3, 7]
def baseStart_2080340 : Nat := 118140960795 + 2080340 * 2 ^ 59
def prefixEnd_2080340 : Nat := 4983230072969 + 3 ^ 40 * 2080340 * 2
def baseEnd_2080340 : Nat := 158253977003629021315955

theorem tailTrace_2080340 : CollatzResearch.WordTrace tailWord_2080340 prefixEnd_2080340 158253977003629021315955 := by
  unfold tailWord_2080340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37938116641645474315363237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50584155522193965753817649 37938116641645474315363237)
  ·
    refine ⟨7113396870308526434130607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37938116641645474315363237 7113396870308526434130607)
    ·
      refine ⟨10670095305462789651195911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113396870308526434130607 10670095305462789651195911)
      ·
        refine ⟨16005142958194184476793867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670095305462789651195911 16005142958194184476793867)
        ·
          refine ⟨24007714437291276715190801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16005142958194184476793867 24007714437291276715190801)
          ·
            refine ⟨18005785827968457536393101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24007714437291276715190801 18005785827968457536393101)
            ·
              refine ⟨6752169685488171576147413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18005785827968457536393101 6752169685488171576147413)
              ·
                refine ⟨158253977003629021315955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6752169685488171576147413 158253977003629021315955)
                ·
                  rfl

theorem cell21_2080340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_2080340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080340 prefixEnd_2080340 := by exact prefixLift 2080340
  have htrace : WordTrace (prefixWord ++ tailWord_2080340) baseStart_2080340 baseEnd_2080340 := by
    simpa [prefixWord, tailWord_2080340, baseEnd_2080340] using wordTrace_append hprefix tailTrace_2080340
  have hstable : (prefixWord ++ tailWord_2080340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080340).length < 2 ^ (prefixWord ++ tailWord_2080340).sum := by decide
  have hdescent : baseEnd_2080340 < baseStart_2080340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080470 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2080470 : Nat := 118140960795 + 2080470 * 2 ^ 59
def prefixEnd_2080470 : Nat := 4983230072969 + 3 ^ 40 * 2080470 * 2
def baseEnd_2080470 : Nat := 474791598782035726780933

theorem tailTrace_2080470 : CollatzResearch.WordTrace tailWord_2080470 prefixEnd_2080470 474791598782035726780933 := by
  unfold tailWord_2080470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742560923301248802059929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50587316515213320555305909 4742560923301248802059929)
  ·
    refine ⟨3556920692475936601544947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4742560923301248802059929 3556920692475936601544947)
    ·
      refine ⟨5335381038713904902317421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556920692475936601544947 5335381038713904902317421)
      ·
        refine ⟨2000767889517714338369033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5335381038713904902317421 2000767889517714338369033)
        ·
          refine ⟨1500575917138285753776775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000767889517714338369033 1500575917138285753776775)
          ·
            refine ⟨2250863875707428630665163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500575917138285753776775 2250863875707428630665163)
            ·
              refine ⟨3376295813561142945997745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250863875707428630665163 3376295813561142945997745)
              ·
                refine ⟨2532221860170857209498309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376295813561142945997745 2532221860170857209498309)
                ·
                  refine ⟨474791598782035726780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532221860170857209498309 474791598782035726780933)
                  ·
                    rfl

theorem cell21_2080470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2080470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080470 prefixEnd_2080470 := by exact prefixLift 2080470
  have htrace : WordTrace (prefixWord ++ tailWord_2080470) baseStart_2080470 baseEnd_2080470 := by
    simpa [prefixWord, tailWord_2080470, baseEnd_2080470] using wordTrace_append hprefix tailTrace_2080470
  have hstable : (prefixWord ++ tailWord_2080470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080470).length < 2 ^ (prefixWord ++ tailWord_2080470).sum := by decide
  have hdescent : baseEnd_2080470 < baseStart_2080470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080532 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2080532 : Nat := 118140960795 + 2080532 * 2 ^ 59
def prefixEnd_2080532 : Nat := 4983230072969 + 3 ^ 40 * 2080532 * 2
def baseEnd_2080532 : Nat := 474805748026737396747473

theorem tailTrace_2080532 : CollatzResearch.WordTrace tailWord_2080532 prefixEnd_2080532 474805748026737396747473 := by
  unfold tailWord_2080532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37941618049297682710857925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50588824065730243614477233 37941618049297682710857925)
  ·
    refine ⟨7114053384243315508285861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37941618049297682710857925 7114053384243315508285861)
    ·
      refine ⟨1333885009545621657803599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7114053384243315508285861 1333885009545621657803599)
      ·
        refine ⟨2000827514318432486705399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333885009545621657803599 2000827514318432486705399)
        ·
          refine ⟨3001241271477648730058099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000827514318432486705399 3001241271477648730058099)
          ·
            refine ⟨4501861907216473095087149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001241271477648730058099 4501861907216473095087149)
            ·
              refine ⟨1688198215206177410657681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4501861907216473095087149 1688198215206177410657681)
              ·
                refine ⟨1266148661404633057993261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688198215206177410657681 1266148661404633057993261)
                ·
                  refine ⟨474805748026737396747473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266148661404633057993261 474805748026737396747473)
                  ·
                    rfl

theorem cell21_2080532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2080532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080532 prefixEnd_2080532 := by exact prefixLift 2080532
  have htrace : WordTrace (prefixWord ++ tailWord_2080532) baseStart_2080532 baseEnd_2080532 := by
    simpa [prefixWord, tailWord_2080532, baseEnd_2080532] using wordTrace_append hprefix tailTrace_2080532
  have hstable : (prefixWord ++ tailWord_2080532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080532).length < 2 ^ (prefixWord ++ tailWord_2080532).sum := by decide
  have hdescent : baseEnd_2080532 < baseStart_2080532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080647 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_2080647 : Nat := 118140960795 + 2080647 * 2 ^ 59
def prefixEnd_2080647 : Nat := 4983230072969 + 3 ^ 40 * 2080647 * 2
def baseEnd_2080647 : Nat := 474831992593522752330571

theorem tailTrace_2080647 : CollatzResearch.WordTrace tailWord_2080647 prefixEnd_2080647 474831992593522752330571 := by
  unfold tailWord_2080647
  simp only [CollatzResearch.WordTrace]
  refine ⟨75887430493178740062152195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50591620328785826708101463 75887430493178740062152195)
  ·
    refine ⟨113831145739768110093228293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75887430493178740062152195 113831145739768110093228293)
    ·
      refine ⟨21343339826206520642480305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113831145739768110093228293 21343339826206520642480305)
      ·
        refine ⟨16007504869654890481860229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21343339826206520642480305 16007504869654890481860229)
        ·
          refine ⟨3001407163060291965348793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16007504869654890481860229 3001407163060291965348793)
          ·
            refine ⟨2251055372295218974011595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3001407163060291965348793 2251055372295218974011595)
            ·
              refine ⟨3376583058442828461017393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251055372295218974011595 3376583058442828461017393)
              ·
                refine ⟨2532437293832121345763045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376583058442828461017393 2532437293832121345763045)
                ·
                  refine ⟨474831992593522752330571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532437293832121345763045 474831992593522752330571)
                  ·
                    rfl

theorem cell21_2080647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_2080647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080647 prefixEnd_2080647 := by exact prefixLift 2080647
  have htrace : WordTrace (prefixWord ++ tailWord_2080647) baseStart_2080647 baseEnd_2080647 := by
    simpa [prefixWord, tailWord_2080647, baseEnd_2080647] using wordTrace_append hprefix tailTrace_2080647
  have hstable : (prefixWord ++ tailWord_2080647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080647).length < 2 ^ (prefixWord ++ tailWord_2080647).sum := by decide
  have hdescent : baseEnd_2080647 < baseStart_2080647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080664 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_2080664 : Nat := 118140960795 + 2080664 * 2 ^ 59
def prefixEnd_2080664 : Nat := 4983230072969 + 3 ^ 40 * 2080664 * 2
def baseEnd_2080664 : Nat := 474835872225134500547203

theorem tailTrace_2080664 : CollatzResearch.WordTrace tailWord_2080664 prefixEnd_2080664 474835872225134500547203 := by
  unfold tailWord_2080664
  simp only [CollatzResearch.WordTrace]
  refine ⟨37944025267058575982760523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50592033689411434643680697 37944025267058575982760523)
  ·
    refine ⟨56916037900587863974140785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37944025267058575982760523 56916037900587863974140785)
    ·
      refine ⟨42687028425440897980605589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56916037900587863974140785 42687028425440897980605589)
      ·
        refine ⟨2000954457442542092840887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42687028425440897980605589 2000954457442542092840887)
        ·
          refine ⟨3001431686163813139261331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000954457442542092840887 3001431686163813139261331)
          ·
            refine ⟨4502147529245719708891997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001431686163813139261331 4502147529245719708891997)
            ·
              refine ⟨1688305323467144890834499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4502147529245719708891997 1688305323467144890834499)
              ·
                refine ⟨2532457985200717336251749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688305323467144890834499 2532457985200717336251749)
                ·
                  refine ⟨474835872225134500547203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532457985200717336251749 474835872225134500547203)
                  ·
                    rfl

theorem cell21_2080664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_2080664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080664 prefixEnd_2080664 := by exact prefixLift 2080664
  have htrace : WordTrace (prefixWord ++ tailWord_2080664) baseStart_2080664 baseEnd_2080664 := by
    simpa [prefixWord, tailWord_2080664, baseEnd_2080664] using wordTrace_append hprefix tailTrace_2080664
  have hstable : (prefixWord ++ tailWord_2080664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080664).length < 2 ^ (prefixWord ++ tailWord_2080664).sum := by decide
  have hdescent : baseEnd_2080664 < baseStart_2080664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080689 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2080689 : Nat := 118140960795 + 2080689 * 2 ^ 59
def prefixEnd_2080689 : Nat := 4983230072969 + 3 ^ 40 * 2080689 * 2
def baseEnd_2080689 : Nat := 474841577565740012630485

theorem tailTrace_2080689 : CollatzResearch.WordTrace tailWord_2080689 prefixEnd_2080689 474841577565740012630485 := by
  unfold tailWord_2080689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75888962359026581235181121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50592641572684387490120747 75888962359026581235181121)
  ·
    refine ⟨56916721769269935926385841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75888962359026581235181121 56916721769269935926385841)
    ·
      refine ⟨42687541326952451944789381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56916721769269935926385841 42687541326952451944789381)
      ·
        refine ⟨8003913998803584739648009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42687541326952451944789381 8003913998803584739648009)
        ·
          refine ⟨6002935499102688554736007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8003913998803584739648009 6002935499102688554736007)
          ·
            refine ⟨9004403248654032832104011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002935499102688554736007 9004403248654032832104011)
            ·
              refine ⟨13506604872981049248156017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004403248654032832104011 13506604872981049248156017)
              ·
                refine ⟨10129953654735786936117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13506604872981049248156017 10129953654735786936117013)
                ·
                  refine ⟨474841577565740012630485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10129953654735786936117013 474841577565740012630485)
                  ·
                    rfl

theorem cell21_2080689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2080689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080689 prefixEnd_2080689 := by exact prefixLift 2080689
  have htrace : WordTrace (prefixWord ++ tailWord_2080689) baseStart_2080689 baseEnd_2080689 := by
    simpa [prefixWord, tailWord_2080689, baseEnd_2080689] using wordTrace_append hprefix tailTrace_2080689
  have hstable : (prefixWord ++ tailWord_2080689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080689).length < 2 ^ (prefixWord ++ tailWord_2080689).sum := by decide
  have hdescent : baseEnd_2080689 < baseStart_2080689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080748 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_2080748 : Nat := 118140960795 + 2080748 * 2 ^ 59
def prefixEnd_2080748 : Nat := 4983230072969 + 3 ^ 40 * 2080748 * 2
def baseEnd_2080748 : Nat := 474855042169569021147031

theorem tailTrace_2080748 : CollatzResearch.WordTrace tailWord_2080748 prefixEnd_2080748 474855042169569021147031 := by
  unfold tailWord_2080748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37945557132906417155789449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50594076177208556207719265 37945557132906417155789449)
  ·
    refine ⟨28459167849679812866842087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37945557132906417155789449 28459167849679812866842087)
    ·
      refine ⟨42688751774519719300263131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28459167849679812866842087 42688751774519719300263131)
      ·
        refine ⟨64033127661779578950394697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42688751774519719300263131 64033127661779578950394697)
        ·
          refine ⟨48024845746334684212796023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64033127661779578950394697 48024845746334684212796023)
          ·
            refine ⟨72037268619502026319194035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48024845746334684212796023 72037268619502026319194035)
            ·
              refine ⟨108055902929253039478791053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72037268619502026319194035 108055902929253039478791053)
              ·
                refine ⟨40520963598469889804546645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108055902929253039478791053 40520963598469889804546645)
                ·
                  refine ⟨474855042169569021147031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40520963598469889804546645 474855042169569021147031)
                  ·
                    rfl

theorem cell21_2080748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_2080748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080748 prefixEnd_2080748 := by exact prefixLift 2080748
  have htrace : WordTrace (prefixWord ++ tailWord_2080748) baseStart_2080748 baseEnd_2080748 := by
    simpa [prefixWord, tailWord_2080748, baseEnd_2080748] using wordTrace_append hprefix tailTrace_2080748
  have hstable : (prefixWord ++ tailWord_2080748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080748).length < 2 ^ (prefixWord ++ tailWord_2080748).sum := by decide
  have hdescent : baseEnd_2080748 < baseStart_2080748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080751 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 3]
def baseStart_2080751 : Nat := 118140960795 + 2080751 * 2 ^ 59
def prefixEnd_2080751 : Nat := 4983230072969 + 3 ^ 40 * 2080751 * 2
def baseEnd_2080751 : Nat := 474855726810441682597025

theorem tailTrace_2080751 : CollatzResearch.WordTrace tailWord_2080751 prefixEnd_2080751 474855726810441682597025 := by
  unfold tailWord_2080751
  simp only [CollatzResearch.WordTrace]
  refine ⟨75891223684801965823938107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50594149123201310549292071 75891223684801965823938107)
  ·
    refine ⟨113836835527202948735907161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75891223684801965823938107 113836835527202948735907161)
    ·
      refine ⟨85377626645402211551930371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113836835527202948735907161 85377626645402211551930371)
      ·
        refine ⟨128066439968103317327895557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85377626645402211551930371 128066439968103317327895557)
        ·
          refine ⟨24012457494019371998980417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128066439968103317327895557 24012457494019371998980417)
          ·
            refine ⟨18009343120514528999235313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24012457494019371998980417 18009343120514528999235313)
            ·
              refine ⟨13507007340385896749426485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18009343120514528999235313 13507007340385896749426485)
              ·
                refine ⟨1266281938161177820258733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13507007340385896749426485 1266281938161177820258733)
                ·
                  refine ⟨474855726810441682597025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266281938161177820258733 474855726810441682597025)
                  ·
                    rfl

theorem cell21_2080751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].length) (baseStart_2080751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080751 prefixEnd_2080751 := by exact prefixLift 2080751
  have htrace : WordTrace (prefixWord ++ tailWord_2080751) baseStart_2080751 baseEnd_2080751 := by
    simpa [prefixWord, tailWord_2080751, baseEnd_2080751] using wordTrace_append hprefix tailTrace_2080751
  have hstable : (prefixWord ++ tailWord_2080751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080751).length < 2 ^ (prefixWord ++ tailWord_2080751).sum := by decide
  have hdescent : baseEnd_2080751 < baseStart_2080751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080765 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2080765 : Nat := 118140960795 + 2080765 * 2 ^ 59
def prefixEnd_2080765 : Nat := 4983230072969 + 3 ^ 40 * 2080765 * 2
def baseEnd_2080765 : Nat := 474858921801180769363663

theorem tailTrace_2080765 : CollatzResearch.WordTrace tailWord_2080765 prefixEnd_2080765 474858921801180769363663 := by
  unfold tailWord_2080765
  simp only [CollatzResearch.WordTrace]
  refine ⟨75891734306751246214947749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50594489537834164143298499 75891734306751246214947749)
  ·
    refine ⟨14229700182515858665302703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75891734306751246214947749 14229700182515858665302703)
    ·
      refine ⟨21344550273773787997954055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14229700182515858665302703 21344550273773787997954055)
      ·
        refine ⟨32016825410660681996931083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344550273773787997954055 32016825410660681996931083)
        ·
          refine ⟨48025238115991022995396625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32016825410660681996931083 48025238115991022995396625)
          ·
            refine ⟨36018928586993267246547469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48025238115991022995396625 36018928586993267246547469)
            ·
              refine ⟨13507098220122475217455301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36018928586993267246547469 13507098220122475217455301)
              ·
                refine ⟨2532580916272964103272869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13507098220122475217455301 2532580916272964103272869)
                ·
                  refine ⟨474858921801180769363663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532580916272964103272869 474858921801180769363663)
                  ·
                    rfl

theorem cell21_2080765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2080765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080765 prefixEnd_2080765 := by exact prefixLift 2080765
  have htrace : WordTrace (prefixWord ++ tailWord_2080765) baseStart_2080765 baseEnd_2080765 := by
    simpa [prefixWord, tailWord_2080765, baseEnd_2080765] using wordTrace_append hprefix tailTrace_2080765
  have hstable : (prefixWord ++ tailWord_2080765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080765).length < 2 ^ (prefixWord ++ tailWord_2080765).sum := by decide
  have hdescent : baseEnd_2080765 < baseStart_2080765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080861 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2080861 : Nat := 118140960795 + 2080861 * 2 ^ 59
def prefixEnd_2080861 : Nat := 4983230072969 + 3 ^ 40 * 2080861 * 2
def baseEnd_2080861 : Nat := 474880830309105935763467

theorem tailTrace_2080861 : CollatzResearch.WordTrace tailWord_2080861 prefixEnd_2080861 474880830309105935763467 := by
  unfold tailWord_2080861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75895235714403454610442437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50596823809602303073628291 75895235714403454610442437)
  ·
    refine ⟨14230356696450647739457957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75895235714403454610442437 14230356696450647739457957)
    ·
      refine ⟨2668191880584496451148367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14230356696450647739457957 2668191880584496451148367)
      ·
        refine ⟨4002287820876744676722551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668191880584496451148367 4002287820876744676722551)
        ·
          refine ⟨6003431731315117015083827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002287820876744676722551 6003431731315117015083827)
          ·
            refine ⟨9005147596972675522625741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003431731315117015083827 9005147596972675522625741)
            ·
              refine ⟨3376930348864753320984653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9005147596972675522625741 3376930348864753320984653)
              ·
                refine ⟨1266348880824282495369245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3376930348864753320984653 1266348880824282495369245)
                ·
                  refine ⟨474880830309105935763467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266348880824282495369245 474880830309105935763467)
                  ·
                    rfl

theorem cell21_2080861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2080861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2080861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2080861 prefixEnd_2080861 := by exact prefixLift 2080861
  have htrace : WordTrace (prefixWord ++ tailWord_2080861) baseStart_2080861 baseEnd_2080861 := by
    simpa [prefixWord, tailWord_2080861, baseEnd_2080861] using wordTrace_append hprefix tailTrace_2080861
  have hstable : (prefixWord ++ tailWord_2080861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080861).length < 2 ^ (prefixWord ++ tailWord_2080861).sum := by decide
  have hdescent : baseEnd_2080861 < baseStart_2080861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081055 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_2081055 : Nat := 118140960795 + 2081055 * 2 ^ 59
def prefixEnd_2081055 : Nat := 4983230072969 + 3 ^ 40 * 2081055 * 2
def baseEnd_2081055 : Nat := 474925103752204709529737

theorem tailTrace_2081055 : CollatzResearch.WordTrace tailWord_2081055 prefixEnd_2081055 474925103752204709529737 := by
  unfold tailWord_2081055
  simp only [CollatzResearch.WordTrace]
  refine ⟨75902311475700625743004619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50601540983800417162003079 75902311475700625743004619)
  ·
    refine ⟨113853467213550938614506929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75902311475700625743004619 113853467213550938614506929)
    ·
      refine ⟨85390100410163203960880197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113853467213550938614506929 85390100410163203960880197)
      ·
        refine ⟨16010643826905600742665037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85390100410163203960880197 16010643826905600742665037)
        ·
          refine ⟨6003991435089600278499389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16010643826905600742665037 6003991435089600278499389)
          ·
            refine ⟨2251496788158600104437271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6003991435089600278499389 2251496788158600104437271)
            ·
              refine ⟨3377245182237900156655907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251496788158600104437271 3377245182237900156655907)
              ·
                refine ⟨5065867773356850234983861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377245182237900156655907 5065867773356850234983861)
                ·
                  refine ⟨474925103752204709529737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065867773356850234983861 474925103752204709529737)
                  ·
                    rfl

theorem cell21_2081055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_2081055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081055 prefixEnd_2081055 := by exact prefixLift 2081055
  have htrace : WordTrace (prefixWord ++ tailWord_2081055) baseStart_2081055 baseEnd_2081055 := by
    simpa [prefixWord, tailWord_2081055, baseEnd_2081055] using wordTrace_append hprefix tailTrace_2081055
  have hstable : (prefixWord ++ tailWord_2081055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081055).length < 2 ^ (prefixWord ++ tailWord_2081055).sum := by decide
  have hdescent : baseEnd_2081055 < baseStart_2081055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081162 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_2081162 : Nat := 118140960795 + 2081162 * 2 ^ 59
def prefixEnd_2081162 : Nat := 4983230072969 + 3 ^ 40 * 2081162 * 2
def baseEnd_2081162 : Nat := 474949522609996301246185

theorem tailTrace_2081162 : CollatzResearch.WordTrace tailWord_2081162 prefixEnd_2081162 474949522609996301246185 := by
  unfold tailWord_2081162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18976553521578245754287435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50604142724208655344766493 18976553521578245754287435)
  ·
    refine ⟨28464830282367368631431153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18976553521578245754287435 28464830282367368631431153)
    ·
      refine ⟨21348622711775526473573365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28464830282367368631431153 21348622711775526473573365)
      ·
        refine ⟨2001433379228955606897503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21348622711775526473573365 2001433379228955606897503)
        ·
          refine ⟨3002150068843433410346255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001433379228955606897503 3002150068843433410346255)
          ·
            refine ⟨4503225103265150115519383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002150068843433410346255 4503225103265150115519383)
            ·
              refine ⟨6754837654897725173279075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503225103265150115519383 6754837654897725173279075)
              ·
                refine ⟨10132256482346587759918613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754837654897725173279075 10132256482346587759918613)
                ·
                  refine ⟨474949522609996301246185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10132256482346587759918613 474949522609996301246185)
                  ·
                    rfl

theorem cell21_2081162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_2081162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081162 prefixEnd_2081162 := by exact prefixLift 2081162
  have htrace : WordTrace (prefixWord ++ tailWord_2081162) baseStart_2081162 baseEnd_2081162 := by
    simpa [prefixWord, tailWord_2081162, baseEnd_2081162] using wordTrace_append hprefix tailTrace_2081162
  have hstable : (prefixWord ++ tailWord_2081162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081162).length < 2 ^ (prefixWord ++ tailWord_2081162).sum := by decide
  have hdescent : baseEnd_2081162 < baseStart_2081162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081207 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 3]
def baseStart_2081207 : Nat := 118140960795 + 2081207 * 2 ^ 59
def prefixEnd_2081207 : Nat := 4983230072969 + 3 ^ 40 * 2081207 * 2
def baseEnd_2081207 : Nat := 474959792223086222996093

theorem tailTrace_2081207 : CollatzResearch.WordTrace tailWord_2081207 prefixEnd_2081207 474959792223086222996093 := by
  unfold tailWord_2081207
  simp only [CollatzResearch.WordTrace]
  refine ⟨75907855371149955702537875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50605236914099970468358583 75907855371149955702537875)
  ·
    refine ⟨113861783056724933553806813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75907855371149955702537875 113861783056724933553806813)
    ·
      refine ⟨42698168646271850082677555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113861783056724933553806813 42698168646271850082677555)
      ·
        refine ⟨64047252969407775124016333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42698168646271850082677555 64047252969407775124016333)
        ·
          refine ⟨24017719863527915671506125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64047252969407775124016333 24017719863527915671506125)
          ·
            refine ⟨9006644948822968376814797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24017719863527915671506125 9006644948822968376814797)
            ·
              refine ⟨3377491855808613141305549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9006644948822968376814797 3377491855808613141305549)
              ·
                refine ⟨1266559445928229927989581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3377491855808613141305549 1266559445928229927989581)
                ·
                  refine ⟨474959792223086222996093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266559445928229927989581 474959792223086222996093)
                  ·
                    rfl

theorem cell21_2081207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].length) (baseStart_2081207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081207 prefixEnd_2081207 := by exact prefixLift 2081207
  have htrace : WordTrace (prefixWord ++ tailWord_2081207) baseStart_2081207 baseEnd_2081207 := by
    simpa [prefixWord, tailWord_2081207, baseEnd_2081207] using wordTrace_append hprefix tailTrace_2081207
  have hstable : (prefixWord ++ tailWord_2081207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081207).length < 2 ^ (prefixWord ++ tailWord_2081207).sum := by decide
  have hdescent : baseEnd_2081207 < baseStart_2081207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081224 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_2081224 : Nat := 118140960795 + 2081224 * 2 ^ 59
def prefixEnd_2081224 : Nat := 4983230072969 + 3 ^ 40 * 2081224 * 2
def baseEnd_2081224 : Nat := 474963671854697971212725

theorem tailTrace_2081224 : CollatzResearch.WordTrace tailWord_2081224 prefixEnd_2081224 474963671854697971212725 := by
  unfold tailWord_2081224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37954237706044183802953363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50605650274725578403937817 37954237706044183802953363)
  ·
    refine ⟨56931356559066275704430045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37954237706044183802953363 56931356559066275704430045)
    ·
      refine ⟨21349258709649853389161267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56931356559066275704430045 21349258709649853389161267)
      ·
        refine ⟨32023888064474780083741901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349258709649853389161267 32023888064474780083741901)
        ·
          refine ⟨12008958024178042531403213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32023888064474780083741901 12008958024178042531403213)
          ·
            refine ⟨4503359259066765949276205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12008958024178042531403213 4503359259066765949276205)
            ·
              refine ⟨1688759722150037230978577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4503359259066765949276205 1688759722150037230978577)
              ·
                refine ⟨1266569791612527923233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688759722150037230978577 1266569791612527923233933)
                ·
                  refine ⟨474963671854697971212725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266569791612527923233933 474963671854697971212725)
                  ·
                    rfl

theorem cell21_2081224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_2081224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081224 prefixEnd_2081224 := by exact prefixLift 2081224
  have htrace : WordTrace (prefixWord ++ tailWord_2081224) baseStart_2081224 baseEnd_2081224 := by
    simpa [prefixWord, tailWord_2081224, baseEnd_2081224] using wordTrace_append hprefix tailTrace_2081224
  have hstable : (prefixWord ++ tailWord_2081224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081224).length < 2 ^ (prefixWord ++ tailWord_2081224).sum := by decide
  have hdescent : baseEnd_2081224 < baseStart_2081224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081238 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2081238 : Nat := 118140960795 + 2081238 * 2 ^ 59
def prefixEnd_2081238 : Nat := 4983230072969 + 3 ^ 40 * 2081238 * 2
def baseEnd_2081238 : Nat := 474966866845437057979363

theorem tailTrace_2081238 : CollatzResearch.WordTrace tailWord_2081238 prefixEnd_2081238 474966866845437057979363 := by
  unfold tailWord_2081238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744311627127352999807273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50605990689358431997944245 4744311627127352999807273)
  ·
    refine ⟨3558233720345514749855455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744311627127352999807273 3558233720345514749855455)
    ·
      refine ⟨5337350580518272124783183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558233720345514749855455 5337350580518272124783183)
      ·
        refine ⟨8006025870777408187174775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337350580518272124783183 8006025870777408187174775)
        ·
          refine ⟨12009038806166112280762163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006025870777408187174775 12009038806166112280762163)
          ·
            refine ⟨18013558209249168421143245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009038806166112280762163 18013558209249168421143245)
            ·
              refine ⟨6755084328468438157928717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013558209249168421143245 6755084328468438157928717)
              ·
                refine ⟨2533156623175664309223269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755084328468438157928717 2533156623175664309223269)
                ·
                  refine ⟨474966866845437057979363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533156623175664309223269 474966866845437057979363)
                  ·
                    rfl

theorem cell21_2081238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2081238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081238 prefixEnd_2081238 := by exact prefixLift 2081238
  have htrace : WordTrace (prefixWord ++ tailWord_2081238) baseStart_2081238 baseEnd_2081238 := by
    simpa [prefixWord, tailWord_2081238, baseEnd_2081238] using wordTrace_append hprefix tailTrace_2081238
  have hstable : (prefixWord ++ tailWord_2081238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081238).length < 2 ^ (prefixWord ++ tailWord_2081238).sum := by decide
  have hdescent : baseEnd_2081238 < baseStart_2081238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081249 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_2081249 : Nat := 118140960795 + 2081249 * 2 ^ 59
def prefixEnd_2081249 : Nat := 4983230072969 + 3 ^ 40 * 2081249 * 2
def baseEnd_2081249 : Nat := 474969377195303483296007

theorem tailTrace_2081249 : CollatzResearch.WordTrace tailWord_2081249 prefixEnd_2081249 474969377195303483296007 := by
  unfold tailWord_2081249
  simp only [CollatzResearch.WordTrace]
  refine ⟨75909387236997796875566801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50606258157998531250377867 75909387236997796875566801)
  ·
    refine ⟨56932040427748347656675101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75909387236997796875566801 56932040427748347656675101)
    ·
      refine ⟨21349515160405630371253163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56932040427748347656675101 21349515160405630371253163)
      ·
        refine ⟨32024272740608445556879745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349515160405630371253163 32024272740608445556879745)
        ·
          refine ⟨24018204555456334167659809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32024272740608445556879745 24018204555456334167659809)
          ·
            refine ⟨18013653416592250625744857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24018204555456334167659809 18013653416592250625744857)
            ·
              refine ⟨13510240062444187969308643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18013653416592250625744857 13510240062444187969308643)
              ·
                refine ⟨20265360093666281953962965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13510240062444187969308643 20265360093666281953962965)
                ·
                  refine ⟨474969377195303483296007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20265360093666281953962965 474969377195303483296007)
                  ·
                    rfl

theorem cell21_2081249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_2081249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081249 prefixEnd_2081249 := by exact prefixLift 2081249
  have htrace : WordTrace (prefixWord ++ tailWord_2081249) baseStart_2081249 baseEnd_2081249 := by
    simpa [prefixWord, tailWord_2081249, baseEnd_2081249] using wordTrace_append hprefix tailTrace_2081249
  have hstable : (prefixWord ++ tailWord_2081249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081249).length < 2 ^ (prefixWord ++ tailWord_2081249).sum := by decide
  have hdescent : baseEnd_2081249 < baseStart_2081249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081286 : List Nat := [6, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2081286 : Nat := 118140960795 + 2081286 * 2 ^ 59
def prefixEnd_2081286 : Nat := 4983230072969 + 3 ^ 40 * 2081286 * 2
def baseEnd_2081286 : Nat := 158325940366466547059755

theorem tailTrace_2081286 : CollatzResearch.WordTrace tailWord_2081286 prefixEnd_2081286 158325940366466547059755 := by
  unfold tailWord_2081286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372210523058242256083241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50607157825242501463109141 2372210523058242256083241)
  ·
    refine ⟨1779157892293681692062431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372210523058242256083241 1779157892293681692062431)
    ·
      refine ⟨2668736838440522538093647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779157892293681692062431 2668736838440522538093647)
      ·
        refine ⟨4003105257660783807140471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668736838440522538093647 4003105257660783807140471)
        ·
          refine ⟨6004657886491175710710707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003105257660783807140471 6004657886491175710710707)
          ·
            refine ⟨9006986829736763566066061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004657886491175710710707 9006986829736763566066061)
            ·
              refine ⟨3377620061151286337274773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9006986829736763566066061 3377620061151286337274773)
              ·
                refine ⟨158325940366466547059755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3377620061151286337274773 158325940366466547059755)
                ·
                  rfl

theorem cell21_2081286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2081286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081286 prefixEnd_2081286 := by exact prefixLift 2081286
  have htrace : WordTrace (prefixWord ++ tailWord_2081286) baseStart_2081286 baseEnd_2081286 := by
    simpa [prefixWord, tailWord_2081286, baseEnd_2081286] using wordTrace_append hprefix tailTrace_2081286
  have hstable : (prefixWord ++ tailWord_2081286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081286).length < 2 ^ (prefixWord ++ tailWord_2081286).sum := by decide
  have hdescent : baseEnd_2081286 < baseStart_2081286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081508 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2081508 : Nat := 118140960795 + 2081508 * 2 ^ 59
def prefixEnd_2081508 : Nat := 4983230072969 + 3 ^ 40 * 2081508 * 2
def baseEnd_2081508 : Nat := 475028484523976588478811

theorem tailTrace_2081508 : CollatzResearch.WordTrace tailWord_2081508 prefixEnd_2081508 475028484523976588478811 := by
  unfold tailWord_2081508
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959416871529742054622589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50612555828706322739496785 37959416871529742054622589)
  ·
    refine ⟨14234781326823653270483471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37959416871529742054622589 14234781326823653270483471)
    ·
      refine ⟨21352171990235479905725207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14234781326823653270483471 21352171990235479905725207)
      ·
        refine ⟨32028257985353219858587811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21352171990235479905725207 32028257985353219858587811)
        ·
          refine ⟨48042386978029829787881717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32028257985353219858587811 48042386978029829787881717)
          ·
            refine ⟨4503973779190296542613911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48042386978029829787881717 4503973779190296542613911)
            ·
              refine ⟨6755960668785444813920867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503973779190296542613911 6755960668785444813920867)
              ·
                refine ⟨10133941003178167220881301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755960668785444813920867 10133941003178167220881301)
                ·
                  refine ⟨475028484523976588478811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10133941003178167220881301 475028484523976588478811)
                  ·
                    rfl

theorem cell21_2081508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2081508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081508 prefixEnd_2081508 := by exact prefixLift 2081508
  have htrace : WordTrace (prefixWord ++ tailWord_2081508) baseStart_2081508 baseEnd_2081508 := by
    simpa [prefixWord, tailWord_2081508, baseEnd_2081508] using wordTrace_append hprefix tailTrace_2081508
  have hstable : (prefixWord ++ tailWord_2081508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081508).length < 2 ^ (prefixWord ++ tailWord_2081508).sum := by decide
  have hdescent : baseEnd_2081508 < baseStart_2081508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081570 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2081570 : Nat := 118140960795 + 2081570 * 2 ^ 59
def prefixEnd_2081570 : Nat := 4983230072969 + 3 ^ 40 * 2081570 * 2
def baseEnd_2081570 : Nat := 475042633768678258445351

theorem tailTrace_2081570 : CollatzResearch.WordTrace tailWord_2081570 prefixEnd_2081570 475042633768678258445351 := by
  unfold tailWord_2081570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980273767208717174500541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50614063379223245798668109 18980273767208717174500541)
  ·
    refine ⟨7117602662703268940437703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18980273767208717174500541 7117602662703268940437703)
    ·
      refine ⟨10676403994054903410656555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117602662703268940437703 10676403994054903410656555)
      ·
        refine ⟨16014605991082355115984833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676403994054903410656555 16014605991082355115984833)
        ·
          refine ⟨12010954493311766336988625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16014605991082355115984833 12010954493311766336988625)
          ·
            refine ⟨9008215869983824752741469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12010954493311766336988625 9008215869983824752741469)
            ·
              refine ⟨3378080951243934282278051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9008215869983824752741469 3378080951243934282278051)
              ·
                refine ⟨5067121426865901423417077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378080951243934282278051 5067121426865901423417077)
                ·
                  refine ⟨475042633768678258445351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067121426865901423417077 475042633768678258445351)
                  ·
                    rfl

theorem cell21_2081570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2081570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081570 prefixEnd_2081570 := by exact prefixLift 2081570
  have htrace : WordTrace (prefixWord ++ tailWord_2081570) baseStart_2081570 baseEnd_2081570 := by
    simpa [prefixWord, tailWord_2081570, baseEnd_2081570] using wordTrace_append hprefix tailTrace_2081570
  have hstable : (prefixWord ++ tailWord_2081570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081570).length < 2 ^ (prefixWord ++ tailWord_2081570).sum := by decide
  have hdescent : baseEnd_2081570 < baseStart_2081570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081719 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_2081719 : Nat := 118140960795 + 2081719 * 2 ^ 59
def prefixEnd_2081719 : Nat := 4983230072969 + 3 ^ 40 * 2081719 * 2
def baseEnd_2081719 : Nat := 475076637598687110461713

theorem tailTrace_2081719 : CollatzResearch.WordTrace tailWord_2081719 prefixEnd_2081719 475076637598687110461713 := by
  unfold tailWord_2081719
  simp only [CollatzResearch.WordTrace]
  refine ⟨75926529545295067145176211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50617686363530044763450807 75926529545295067145176211)
  ·
    refine ⟨113889794317942600717764317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75926529545295067145176211 113889794317942600717764317)
    ·
      refine ⟨42708672869228475269161619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113889794317942600717764317 42708672869228475269161619)
      ·
        refine ⟨64063009303842712903742429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42708672869228475269161619 64063009303842712903742429)
        ·
          refine ⟨24023628488941017338903411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64063009303842712903742429 24023628488941017338903411)
          ·
            refine ⟨36035442733411526008355117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24023628488941017338903411 36035442733411526008355117)
            ·
              refine ⟨13513291025029322253133169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36035442733411526008355117 13513291025029322253133169)
              ·
                refine ⟨10134968268771991689849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513291025029322253133169 10134968268771991689849877)
                ·
                  refine ⟨475076637598687110461713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10134968268771991689849877 475076637598687110461713)
                  ·
                    rfl

theorem cell21_2081719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_2081719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081719 prefixEnd_2081719 := by exact prefixLift 2081719
  have htrace : WordTrace (prefixWord ++ tailWord_2081719) baseStart_2081719 baseEnd_2081719 := by
    simpa [prefixWord, tailWord_2081719, baseEnd_2081719] using wordTrace_append hprefix tailTrace_2081719
  have hstable : (prefixWord ++ tailWord_2081719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081719).length < 2 ^ (prefixWord ++ tailWord_2081719).sum := by decide
  have hdescent : baseEnd_2081719 < baseStart_2081719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081739 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 3]
def baseStart_2081739 : Nat := 118140960795 + 2081739 * 2 ^ 59
def prefixEnd_2081739 : Nat := 4983230072969 + 3 ^ 40 * 2081739 * 2
def baseEnd_2081739 : Nat := 475081201871171520128339

theorem tailTrace_2081739 : CollatzResearch.WordTrace tailWord_2081739 prefixEnd_2081739 475081201871171520128339 := by
  unfold tailWord_2081739
  simp only [CollatzResearch.WordTrace]
  refine ⟨75927259005222610560904271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50618172670148407040602847 75927259005222610560904271)
  ·
    refine ⟨113890888507833915841356407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75927259005222610560904271 113890888507833915841356407)
    ·
      refine ⟨170836332761750873762034611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113890888507833915841356407 170836332761750873762034611)
      ·
        refine ⟨256254499142626310643051917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170836332761750873762034611 256254499142626310643051917)
        ·
          refine ⟨96095437178484866491144469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256254499142626310643051917 96095437178484866491144469)
          ·
            refine ⟨4504473617741478116772397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96095437178484866491144469 4504473617741478116772397)
            ·
              refine ⟨1689177606653054293789649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4504473617741478116772397 1689177606653054293789649)
              ·
                refine ⟨1266883204989790720342237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689177606653054293789649 1266883204989790720342237)
                ·
                  refine ⟨475081201871171520128339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266883204989790720342237 475081201871171520128339)
                  ·
                    rfl

theorem cell21_2081739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].length) (baseStart_2081739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081739 prefixEnd_2081739 := by exact prefixLift 2081739
  have htrace : WordTrace (prefixWord ++ tailWord_2081739) baseStart_2081739 baseEnd_2081739 := by
    simpa [prefixWord, tailWord_2081739, baseEnd_2081739] using wordTrace_append hprefix tailTrace_2081739
  have hstable : (prefixWord ++ tailWord_2081739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081739).length < 2 ^ (prefixWord ++ tailWord_2081739).sum := by decide
  have hdescent : baseEnd_2081739 < baseStart_2081739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081753 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 4]
def baseStart_2081753 : Nat := 118140960795 + 2081753 * 2 ^ 59
def prefixEnd_2081753 : Nat := 4983230072969 + 3 ^ 40 * 2081753 * 2
def baseEnd_2081753 : Nat := 475084396861910606894977

theorem tailTrace_2081753 : CollatzResearch.WordTrace tailWord_2081753 prefixEnd_2081753 475084396861910606894977 := by
  unfold tailWord_2081753
  simp only [CollatzResearch.WordTrace]
  refine ⟨75927769627171890951913913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50618513084781260634609275 75927769627171890951913913)
  ·
    refine ⟨56945827220378918213935435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75927769627171890951913913 56945827220378918213935435)
    ·
      refine ⟨85418740830568377320903153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56945827220378918213935435 85418740830568377320903153)
      ·
        refine ⟨64064055622926282990677365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85418740830568377320903153 64064055622926282990677365)
        ·
          refine ⟨6006005214649339030376003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64064055622926282990677365 6006005214649339030376003)
          ·
            refine ⟨9009007821974008545564005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006005214649339030376003 9009007821974008545564005)
            ·
              refine ⟨1689188966620126602293251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9009007821974008545564005 1689188966620126602293251)
              ·
                refine ⟨2533783449930189903439877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689188966620126602293251 2533783449930189903439877)
                ·
                  refine ⟨475084396861910606894977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533783449930189903439877 475084396861910606894977)
                  ·
                    rfl

theorem cell21_2081753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_2081753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081753 prefixEnd_2081753 := by exact prefixLift 2081753
  have htrace : WordTrace (prefixWord ++ tailWord_2081753) baseStart_2081753 baseEnd_2081753 := by
    simpa [prefixWord, tailWord_2081753, baseEnd_2081753] using wordTrace_append hprefix tailTrace_2081753
  have hstable : (prefixWord ++ tailWord_2081753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081753).length < 2 ^ (prefixWord ++ tailWord_2081753).sum := by decide
  have hdescent : baseEnd_2081753 < baseStart_2081753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081790 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2081790 : Nat := 118140960795 + 2081790 * 2 ^ 59
def prefixEnd_2081790 : Nat := 4983230072969 + 3 ^ 40 * 2081790 * 2
def baseEnd_2081790 : Nat := 475092840766006764778235

theorem tailTrace_2081790 : CollatzResearch.WordTrace tailWord_2081790 prefixEnd_2081790 475092840766006764778235 := by
  unfold tailWord_2081790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491139891004730783876353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50619412752025230847340549 9491139891004730783876353)
  ·
    refine ⟨7118354918253548087907265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9491139891004730783876353 7118354918253548087907265)
    ·
      refine ⟨5338766188690161065930449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7118354918253548087907265 5338766188690161065930449)
      ·
        refine ⟨4004074641517620799447837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5338766188690161065930449 4004074641517620799447837)
        ·
          refine ⟨1501527990569107799792939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004074641517620799447837 1501527990569107799792939)
          ·
            refine ⟨2252291985853661699689409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501527990569107799792939 2252291985853661699689409)
            ·
              refine ⟨1689218989390246274767057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252291985853661699689409 1689218989390246274767057)
              ·
                refine ⟨1266914242042684706075293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689218989390246274767057 1266914242042684706075293)
                ·
                  refine ⟨475092840766006764778235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266914242042684706075293 475092840766006764778235)
                  ·
                    rfl

theorem cell21_2081790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2081790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081790 prefixEnd_2081790 := by exact prefixLift 2081790
  have htrace : WordTrace (prefixWord ++ tailWord_2081790) baseStart_2081790 baseEnd_2081790 := by
    simpa [prefixWord, tailWord_2081790, baseEnd_2081790] using wordTrace_append hprefix tailTrace_2081790
  have hstable : (prefixWord ++ tailWord_2081790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081790).length < 2 ^ (prefixWord ++ tailWord_2081790).sum := by decide
  have hdescent : baseEnd_2081790 < baseStart_2081790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081840 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_2081840 : Nat := 118140960795 + 2081840 * 2 ^ 59
def prefixEnd_2081840 : Nat := 4983230072969 + 3 ^ 40 * 2081840 * 2
def baseEnd_2081840 : Nat := 475104251447217788944799

theorem tailTrace_2081840 : CollatzResearch.WordTrace tailWord_2081840 prefixEnd_2081840 475104251447217788944799 := by
  unfold tailWord_2081840
  simp only [CollatzResearch.WordTrace]
  refine ⟨37965471388928352405165487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50620628518571136540220649 37965471388928352405165487)
  ·
    refine ⟨56948207083392528607748231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37965471388928352405165487 56948207083392528607748231)
    ·
      refine ⟨85422310625088792911622347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56948207083392528607748231 85422310625088792911622347)
      ·
        refine ⟨128133465937633189367433521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85422310625088792911622347 128133465937633189367433521)
        ·
          refine ⟨96100099453224892025575141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128133465937633189367433521 96100099453224892025575141)
          ·
            refine ⟨18018768647479667254795339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96100099453224892025575141 18018768647479667254795339)
            ·
              refine ⟨27028152971219500882193009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018768647479667254795339 27028152971219500882193009)
              ·
                refine ⟨20271114728414625661644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27028152971219500882193009 20271114728414625661644757)
                ·
                  refine ⟨475104251447217788944799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20271114728414625661644757 475104251447217788944799)
                  ·
                    rfl

theorem cell21_2081840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_2081840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081840 prefixEnd_2081840 := by exact prefixLift 2081840
  have htrace : WordTrace (prefixWord ++ tailWord_2081840) baseStart_2081840 baseEnd_2081840 := by
    simpa [prefixWord, tailWord_2081840, baseEnd_2081840] using wordTrace_append hprefix tailTrace_2081840
  have hstable : (prefixWord ++ tailWord_2081840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081840).length < 2 ^ (prefixWord ++ tailWord_2081840).sum := by decide
  have hdescent : baseEnd_2081840 < baseStart_2081840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081846 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2081846 : Nat := 118140960795 + 2081846 * 2 ^ 59
def prefixEnd_2081846 : Nat := 4983230072969 + 3 ^ 40 * 2081846 * 2
def baseEnd_2081846 : Nat := 475105620728963111844787

theorem tailTrace_2081846 : CollatzResearch.WordTrace tailWord_2081846 prefixEnd_2081846 475105620728963111844787 := by
  unfold tailWord_2081846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745697600989685489690587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50620774410556645223366261 4745697600989685489690587)
  ·
    refine ⟨7118546401484528234535881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4745697600989685489690587 7118546401484528234535881)
    ·
      refine ⟨5338909801113396175901911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7118546401484528234535881 5338909801113396175901911)
      ·
        refine ⟨8008364701670094263852867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338909801113396175901911 8008364701670094263852867)
        ·
          refine ⟨12012547052505141395779301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8008364701670094263852867 12012547052505141395779301)
          ·
            refine ⟨2252352572344714011708619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12012547052505141395779301 2252352572344714011708619)
            ·
              refine ⟨3378528858517071017562929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252352572344714011708619 3378528858517071017562929)
              ·
                refine ⟨2533896643887803263172197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378528858517071017562929 2533896643887803263172197)
                ·
                  refine ⟨475105620728963111844787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533896643887803263172197 475105620728963111844787)
                  ·
                    rfl

theorem cell21_2081846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2081846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081846 prefixEnd_2081846 := by exact prefixLift 2081846
  have htrace : WordTrace (prefixWord ++ tailWord_2081846) baseStart_2081846 baseEnd_2081846 := by
    simpa [prefixWord, tailWord_2081846, baseEnd_2081846] using wordTrace_append hprefix tailTrace_2081846
  have hstable : (prefixWord ++ tailWord_2081846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081846).length < 2 ^ (prefixWord ++ tailWord_2081846).sum := by decide
  have hdescent : baseEnd_2081846 < baseStart_2081846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081902 : List Nat := [4, 1, 2, 2, 1, 2, 9]
def baseStart_2081902 : Nat := 118140960795 + 2081902 * 2 ^ 59
def prefixEnd_2081902 : Nat := 4983230072969 + 3 ^ 40 * 2081902 * 2
def baseEnd_2081902 : Nat := 52790933410213273212371

theorem tailTrace_2081902 : CollatzResearch.WordTrace tailWord_2081902 prefixEnd_2081902 52790933410213273212371 := by
  unfold tailWord_2081902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491650512954011174885995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50622136069088059599391973 9491650512954011174885995)
  ·
    refine ⟨14237475769431016762328993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9491650512954011174885995 14237475769431016762328993)
    ·
      refine ⟨10678106827073262571746745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14237475769431016762328993 10678106827073262571746745)
      ·
        refine ⟨8008580120304946928810059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10678106827073262571746745 8008580120304946928810059)
        ·
          refine ⟨12012870180457420393215089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8008580120304946928810059 12012870180457420393215089)
          ·
            refine ⟨9009652635343065294911317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012870180457420393215089 9009652635343065294911317)
            ·
              refine ⟨52790933410213273212371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9009652635343065294911317 52790933410213273212371)
              ·
                rfl

theorem cell21_2081902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 9].length) (baseStart_2081902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081902 prefixEnd_2081902 := by exact prefixLift 2081902
  have htrace : WordTrace (prefixWord ++ tailWord_2081902) baseStart_2081902 baseEnd_2081902 := by
    simpa [prefixWord, tailWord_2081902, baseEnd_2081902] using wordTrace_append hprefix tailTrace_2081902
  have hstable : (prefixWord ++ tailWord_2081902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081902).length < 2 ^ (prefixWord ++ tailWord_2081902).sum := by decide
  have hdescent : baseEnd_2081902 < baseStart_2081902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081992 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_2081992 : Nat := 118140960795 + 2081992 * 2 ^ 59
def prefixEnd_2081992 : Nat := 4983230072969 + 3 ^ 40 * 2081992 * 2
def baseEnd_2081992 : Nat := 475138939918099302411155

theorem tailTrace_2081992 : CollatzResearch.WordTrace tailWord_2081992 prefixEnd_2081992 475138939918099302411155 := by
  unfold tailWord_2081992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37968243336653017384932115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50624324448870689846576153 37968243336653017384932115)
  ·
    refine ⟨56952365004979526077398173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37968243336653017384932115 56952365004979526077398173)
    ·
      refine ⟨21357136876867322279024315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56952365004979526077398173 21357136876867322279024315)
      ·
        refine ⟨32035705315300983418536473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21357136876867322279024315 32035705315300983418536473)
        ·
          refine ⟨24026778986475737563902355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32035705315300983418536473 24026778986475737563902355)
          ·
            refine ⟨36040168479713606345853533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24026778986475737563902355 36040168479713606345853533)
            ·
              refine ⟨13515063179892602379695075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36040168479713606345853533 13515063179892602379695075)
              ·
                refine ⟨20272594769838903569542613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515063179892602379695075 20272594769838903569542613)
                ·
                  refine ⟨475138939918099302411155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20272594769838903569542613 475138939918099302411155)
                  ·
                    rfl

theorem cell21_2081992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_2081992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2081992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2081992 prefixEnd_2081992 := by exact prefixLift 2081992
  have htrace : WordTrace (prefixWord ++ tailWord_2081992) baseStart_2081992 baseEnd_2081992 := by
    simpa [prefixWord, tailWord_2081992, baseEnd_2081992] using wordTrace_append hprefix tailTrace_2081992
  have hstable : (prefixWord ++ tailWord_2081992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081992).length < 2 ^ (prefixWord ++ tailWord_2081992).sum := by decide
  have hdescent : baseEnd_2081992 < baseStart_2081992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082026 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_2082026 : Nat := 118140960795 + 2082026 * 2 ^ 59
def prefixEnd_2082026 : Nat := 4983230072969 + 3 ^ 40 * 2082026 * 2
def baseEnd_2082026 : Nat := 475146699181322798844419

theorem tailTrace_2082026 : CollatzResearch.WordTrace tailWord_2082026 prefixEnd_2082026 475146699181322798844419 := by
  unfold tailWord_2082026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984431688795714644150483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50625151170121905717734621 18984431688795714644150483)
  ·
    refine ⟨28476647533193571966225725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18984431688795714644150483 28476647533193571966225725)
    ·
      refine ⟨10678742824947589487334647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28476647533193571966225725 10678742824947589487334647)
      ·
        refine ⟨16018114237421384231001971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678742824947589487334647 16018114237421384231001971)
        ·
          refine ⟨24027171356132076346502957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018114237421384231001971 24027171356132076346502957)
          ·
            refine ⟨9010189258549528629938609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24027171356132076346502957 9010189258549528629938609)
            ·
              refine ⟨6757641943912146472453957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010189258549528629938609 6757641943912146472453957)
              ·
                refine ⟨1267057864483527463585117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6757641943912146472453957 1267057864483527463585117)
                ·
                  refine ⟨475146699181322798844419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267057864483527463585117 475146699181322798844419)
                  ·
                    rfl

theorem cell21_2082026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_2082026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082026 prefixEnd_2082026 := by exact prefixLift 2082026
  have htrace : WordTrace (prefixWord ++ tailWord_2082026) baseStart_2082026 baseEnd_2082026 := by
    simpa [prefixWord, tailWord_2082026, baseEnd_2082026] using wordTrace_append hprefix tailTrace_2082026
  have hstable : (prefixWord ++ tailWord_2082026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082026).length < 2 ^ (prefixWord ++ tailWord_2082026).sum := by decide
  have hdescent : baseEnd_2082026 < baseStart_2082026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082085 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_2082085 : Nat := 118140960795 + 2082085 * 2 ^ 59
def prefixEnd_2082085 : Nat := 4983230072969 + 3 ^ 40 * 2082085 * 2
def baseEnd_2082085 : Nat := 475160163785151807360965

theorem tailTrace_2082085 : CollatzResearch.WordTrace tailWord_2082085 prefixEnd_2082085 475160163785151807360965 := by
  unfold tailWord_2082085
  simp only [CollatzResearch.WordTrace]
  refine ⟨75939878661969111652999709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50626585774646074435333139 75939878661969111652999709)
  ·
    refine ⟨28477454498238416869874891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75939878661969111652999709 28477454498238416869874891)
    ·
      refine ⟨42716181747357625304812337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28477454498238416869874891 42716181747357625304812337)
      ·
        refine ⟨32037136310518218978609253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42716181747357625304812337 32037136310518218978609253)
        ·
          refine ⟨6006963058222166058489235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32037136310518218978609253 6006963058222166058489235)
          ·
            refine ⟨9010444587333249087733853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006963058222166058489235 9010444587333249087733853)
            ·
              refine ⟨3378916720249968407900195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9010444587333249087733853 3378916720249968407900195)
              ·
                refine ⟨5068375080374952611850293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378916720249968407900195 5068375080374952611850293)
                ·
                  refine ⟨475160163785151807360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068375080374952611850293 475160163785151807360965)
                  ·
                    rfl

theorem cell21_2082085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_2082085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082085 prefixEnd_2082085 := by exact prefixLift 2082085
  have htrace : WordTrace (prefixWord ++ tailWord_2082085) baseStart_2082085 baseEnd_2082085 := by
    simpa [prefixWord, tailWord_2082085, baseEnd_2082085] using wordTrace_append hprefix tailTrace_2082085
  have hstable : (prefixWord ++ tailWord_2082085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082085).length < 2 ^ (prefixWord ++ tailWord_2082085).sum := by decide
  have hdescent : baseEnd_2082085 < baseStart_2082085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082220 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2082220 : Nat := 118140960795 + 2082220 * 2 ^ 59
def prefixEnd_2082220 : Nat := 4983230072969 + 3 ^ 40 * 2082220 * 2
def baseEnd_2082220 : Nat := 475190972624421572610689

theorem tailTrace_2082220 : CollatzResearch.WordTrace tailWord_2082220 prefixEnd_2082220 475190972624421572610689 := by
  unfold tailWord_2082220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972401258240014854582057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50629868344320019806109409 37972401258240014854582057)
  ·
    refine ⟨28479300943680011140936543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37972401258240014854582057 28479300943680011140936543)
    ·
      refine ⟨42718951415520016711404815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28479300943680011140936543 42718951415520016711404815)
      ·
        refine ⟨64078427123280025067107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42718951415520016711404815 64078427123280025067107223)
        ·
          refine ⟨96117640684920037600660835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64078427123280025067107223 96117640684920037600660835)
          ·
            refine ⟨144176461027380056400991253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96117640684920037600660835 144176461027380056400991253)
            ·
              refine ⟨6758271610658440143796465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144176461027380056400991253 6758271610658440143796465)
              ·
                refine ⟨5068703707993830107847349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758271610658440143796465 5068703707993830107847349)
                ·
                  refine ⟨475190972624421572610689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068703707993830107847349 475190972624421572610689)
                  ·
                    rfl

theorem cell21_2082220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2082220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082220 prefixEnd_2082220 := by exact prefixLift 2082220
  have htrace : WordTrace (prefixWord ++ tailWord_2082220) baseStart_2082220 baseEnd_2082220 := by
    simpa [prefixWord, tailWord_2082220, baseEnd_2082220] using wordTrace_append hprefix tailTrace_2082220
  have hstable : (prefixWord ++ tailWord_2082220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082220).length < 2 ^ (prefixWord ++ tailWord_2082220).sum := by decide
  have hdescent : baseEnd_2082220 < baseStart_2082220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082265 : List Nat := [1, 2, 1, 2, 4, 2, 1, 8]
def baseStart_2082265 : Nat := 118140960795 + 2082265 * 2 ^ 59
def prefixEnd_2082265 : Nat := 4983230072969 + 3 ^ 40 * 2082265 * 2
def baseEnd_2082265 : Nat := 158400414079170498120199

theorem tailTrace_2082265 : CollatzResearch.WordTrace tailWord_2082265 prefixEnd_2082265 158400414079170498120199 := by
  unfold tailWord_2082265
  simp only [CollatzResearch.WordTrace]
  refine ⟨75946443801317002394552249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50630962534211334929701499 75946443801317002394552249)
  ·
    refine ⟨56959832850987751795914187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75946443801317002394552249 56959832850987751795914187)
    ·
      refine ⟨85439749276481627693871281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56959832850987751795914187 85439749276481627693871281)
      ·
        refine ⟨64079811957361220770403461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85439749276481627693871281 64079811957361220770403461)
        ·
          refine ⟨12014964742005228894450649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64079811957361220770403461 12014964742005228894450649)
          ·
            refine ⟨9011223556503921670837987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12014964742005228894450649 9011223556503921670837987)
            ·
              refine ⟨13516835334755882506256981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011223556503921670837987 13516835334755882506256981)
              ·
                refine ⟨158400414079170498120199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13516835334755882506256981 158400414079170498120199)
                ·
                  rfl

theorem cell21_2082265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_2082265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082265 prefixEnd_2082265 := by exact prefixLift 2082265
  have htrace : WordTrace (prefixWord ++ tailWord_2082265) baseStart_2082265 baseEnd_2082265 := by
    simpa [prefixWord, tailWord_2082265, baseEnd_2082265] using wordTrace_append hprefix tailTrace_2082265
  have hstable : (prefixWord ++ tailWord_2082265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082265).length < 2 ^ (prefixWord ++ tailWord_2082265).sum := by decide
  have hdescent : baseEnd_2082265 < baseStart_2082265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082302 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2082302 : Nat := 118140960795 + 2082302 * 2 ^ 59
def prefixEnd_2082302 : Nat := 4983230072969 + 3 ^ 40 * 2082302 * 2
def baseEnd_2082302 : Nat := 475209686141607652243855

theorem tailTrace_2082302 : CollatzResearch.WordTrace tailWord_2082302 prefixEnd_2082302 475209686141607652243855 := by
  unfold tailWord_2082302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493474162772869714206145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50631862201455305142432773 9493474162772869714206145)
  ·
    refine ⟨7120105622079652285654609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9493474162772869714206145 7120105622079652285654609)
    ·
      refine ⟨5340079216559739214240957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7120105622079652285654609 5340079216559739214240957)
      ·
        refine ⟨2002529706209902205340359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5340079216559739214240957 2002529706209902205340359)
        ·
          refine ⟨3003794559314853308010539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002529706209902205340359 3003794559314853308010539)
          ·
            refine ⟨4505691838972279962015809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003794559314853308010539 4505691838972279962015809)
            ·
              refine ⟨3379268879229209971511857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505691838972279962015809 3379268879229209971511857)
              ·
                refine ⟨2534451659421907478633893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379268879229209971511857 2534451659421907478633893)
                ·
                  refine ⟨475209686141607652243855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534451659421907478633893 475209686141607652243855)
                  ·
                    rfl

theorem cell21_2082302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2082302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082302 prefixEnd_2082302 := by exact prefixLift 2082302
  have htrace : WordTrace (prefixWord ++ tailWord_2082302) baseStart_2082302 baseEnd_2082302 := by
    simpa [prefixWord, tailWord_2082302, baseEnd_2082302] using wordTrace_append hprefix tailTrace_2082302
  have hstable : (prefixWord ++ tailWord_2082302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082302).length < 2 ^ (prefixWord ++ tailWord_2082302).sum := by decide
  have hdescent : baseEnd_2082302 < baseStart_2082302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082313 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 3]
def baseStart_2082313 : Nat := 118140960795 + 2082313 * 2 ^ 59
def prefixEnd_2082313 : Nat := 4983230072969 + 3 ^ 40 * 2082313 * 2
def baseEnd_2082313 : Nat := 475212196491474077560499

theorem tailTrace_2082313 : CollatzResearch.WordTrace tailWord_2082313 prefixEnd_2082313 475212196491474077560499 := by
  unfold tailWord_2082313
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948194505143106592299593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50632129670095404394866395 75948194505143106592299593)
  ·
    refine ⟨56961145878857329944224695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75948194505143106592299593 56961145878857329944224695)
    ·
      refine ⟨85441718818285994916337043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56961145878857329944224695 85441718818285994916337043)
      ·
        refine ⟨128162578227428992374505565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85441718818285994916337043 128162578227428992374505565)
        ·
          refine ⟨48060966835285872140439587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128162578227428992374505565 48060966835285872140439587)
          ·
            refine ⟨72091450252928808210659381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48060966835285872140439587 72091450252928808210659381)
            ·
              refine ⟨6758573461212075769749317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72091450252928808210659381 6758573461212075769749317)
              ·
                refine ⟨1267232523977264206827997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6758573461212075769749317 1267232523977264206827997)
                ·
                  refine ⟨475212196491474077560499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267232523977264206827997 475212196491474077560499)
                  ·
                    rfl

theorem cell21_2082313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_2082313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082313 prefixEnd_2082313 := by exact prefixLift 2082313
  have htrace : WordTrace (prefixWord ++ tailWord_2082313) baseStart_2082313 baseEnd_2082313 := by
    simpa [prefixWord, tailWord_2082313, baseEnd_2082313] using wordTrace_append hprefix tailTrace_2082313
  have hstable : (prefixWord ++ tailWord_2082313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082313).length < 2 ^ (prefixWord ++ tailWord_2082313).sum := by decide
  have hdescent : baseEnd_2082313 < baseStart_2082313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082479 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_2082479 : Nat := 118140960795 + 2082479 * 2 ^ 59
def prefixEnd_2082479 : Nat := 4983230072969 + 3 ^ 40 * 2082479 * 2
def baseEnd_2082479 : Nat := 475250079953094677793493

theorem tailTrace_2082479 : CollatzResearch.WordTrace tailWord_2082479 prefixEnd_2082479 475250079953094677793493 := by
  unfold tailWord_2082479
  simp only [CollatzResearch.WordTrace]
  refine ⟨75954249022541716942842491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50636166015027811295228327 75954249022541716942842491)
  ·
    refine ⟨113931373533812575414263737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75954249022541716942842491 113931373533812575414263737)
    ·
      refine ⟨85448530150359431560697803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113931373533812575414263737 85448530150359431560697803)
      ·
        refine ⟨128172795225539147341046705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85448530150359431560697803 128172795225539147341046705)
        ·
          refine ⟨96129596419154360505785029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128172795225539147341046705 96129596419154360505785029)
          ·
            refine ⟨18024299328591442594834693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96129596419154360505785029 18024299328591442594834693)
            ·
              refine ⟨3379556124110895486531505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18024299328591442594834693 3379556124110895486531505)
              ·
                refine ⟨2534667093083171614898629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379556124110895486531505 2534667093083171614898629)
                ·
                  refine ⟨475250079953094677793493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534667093083171614898629 475250079953094677793493)
                  ·
                    rfl

theorem cell21_2082479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_2082479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082479 prefixEnd_2082479 := by exact prefixLift 2082479
  have htrace : WordTrace (prefixWord ++ tailWord_2082479) baseStart_2082479 baseEnd_2082479 := by
    simpa [prefixWord, tailWord_2082479, baseEnd_2082479] using wordTrace_append hprefix tailTrace_2082479
  have hstable : (prefixWord ++ tailWord_2082479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082479).length < 2 ^ (prefixWord ++ tailWord_2082479).sum := by decide
  have hdescent : baseEnd_2082479 < baseStart_2082479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082482 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_2082482 : Nat := 118140960795 + 2082482 * 2 ^ 59
def prefixEnd_2082482 : Nat := 4983230072969 + 3 ^ 40 * 2082482 * 2
def baseEnd_2082482 : Nat := 475250764593967339243487

theorem tailTrace_2082482 : CollatzResearch.WordTrace tailWord_2082482 prefixEnd_2082482 475250764593967339243487 := by
  unfold tailWord_2082482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18988589610382712113800425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50636238961020565636801133 18988589610382712113800425)
  ·
    refine ⟨14241442207787034085350319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18988589610382712113800425 14241442207787034085350319)
    ·
      refine ⟨21362163311680551128025479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241442207787034085350319 21362163311680551128025479)
      ·
        refine ⟨32043244967520826692038219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21362163311680551128025479 32043244967520826692038219)
        ·
          refine ⟨48064867451281240038057329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043244967520826692038219 48064867451281240038057329)
          ·
            refine ⟨36048650588460930028542997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48064867451281240038057329 36048650588460930028542997)
            ·
              refine ⟨1689780496334106095087953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36048650588460930028542997 1689780496334106095087953)
              ·
                refine ⟨1267335372250579571315965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689780496334106095087953 1267335372250579571315965)
                ·
                  refine ⟨475250764593967339243487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267335372250579571315965 475250764593967339243487)
                  ·
                    rfl

theorem cell21_2082482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_2082482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082482 prefixEnd_2082482 := by exact prefixLift 2082482
  have htrace : WordTrace (prefixWord ++ tailWord_2082482) baseStart_2082482 baseEnd_2082482 := by
    simpa [prefixWord, tailWord_2082482, baseEnd_2082482] using wordTrace_append hprefix tailTrace_2082482
  have hstable : (prefixWord ++ tailWord_2082482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082482).length < 2 ^ (prefixWord ++ tailWord_2082482).sum := by decide
  have hdescent : baseEnd_2082482 < baseStart_2082482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082510 : List Nat := [4, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2082510 : Nat := 118140960795 + 2082510 * 2 ^ 59
def prefixEnd_2082510 : Nat := 4983230072969 + 3 ^ 40 * 2082510 * 2
def baseEnd_2082510 : Nat := 158419051525148504258921

theorem tailTrace_2082510 : CollatzResearch.WordTrace tailWord_2082510 prefixEnd_2082510 158419051525148504258921 := by
  unfold tailWord_2082510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494422460678676154652623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50636919790286272824813989 9494422460678676154652623)
  ·
    refine ⟨14241633691018014231978935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494422460678676154652623 14241633691018014231978935)
    ·
      refine ⟨21362450536527021347968403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241633691018014231978935 21362450536527021347968403)
      ·
        refine ⟨32043675804790532021952605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21362450536527021347968403 32043675804790532021952605)
        ·
          refine ⟨12016378426796449508232227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32043675804790532021952605 12016378426796449508232227)
          ·
            refine ⟨18024567640194674262348341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016378426796449508232227 18024567640194674262348341)
            ·
              refine ⟨1689803216268250712095157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18024567640194674262348341 1689803216268250712095157)
              ·
                refine ⟨158419051525148504258921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1689803216268250712095157 158419051525148504258921)
                ·
                  rfl

theorem cell21_2082510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2082510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082510 prefixEnd_2082510 := by exact prefixLift 2082510
  have htrace : WordTrace (prefixWord ++ tailWord_2082510) baseStart_2082510 baseEnd_2082510 := by
    simpa [prefixWord, tailWord_2082510, baseEnd_2082510] using wordTrace_append hprefix tailTrace_2082510
  have hstable : (prefixWord ++ tailWord_2082510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082510).length < 2 ^ (prefixWord ++ tailWord_2082510).sum := by decide
  have hdescent : baseEnd_2082510 < baseStart_2082510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082541 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2082541 : Nat := 118140960795 + 2082541 * 2 ^ 59
def prefixEnd_2082541 : Nat := 4983230072969 + 3 ^ 40 * 2082541 * 2
def baseEnd_2082541 : Nat := 475264229197796347760033

theorem tailTrace_2082541 : CollatzResearch.WordTrace tailWord_2082541 prefixEnd_2082541 475264229197796347760033 := by
  unfold tailWord_2082541
  simp only [CollatzResearch.WordTrace]
  refine ⟨75956510348317101531599477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50637673565544734354399651 75956510348317101531599477)
  ·
    refine ⟨7120922845154728268587451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75956510348317101531599477 7120922845154728268587451)
    ·
      refine ⟨10681384267732092402881177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120922845154728268587451 10681384267732092402881177)
      ·
        refine ⟨8011038200799069302160883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10681384267732092402881177 8011038200799069302160883)
        ·
          refine ⟨12016557301198603953241325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011038200799069302160883 12016557301198603953241325)
          ·
            refine ⟨4506208987949476482465497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12016557301198603953241325 4506208987949476482465497)
            ·
              refine ⟨3379656740962107361849123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506208987949476482465497 3379656740962107361849123)
              ·
                refine ⟨5069485111443161042773685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379656740962107361849123 5069485111443161042773685)
                ·
                  refine ⟨475264229197796347760033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5069485111443161042773685 475264229197796347760033)
                  ·
                    rfl

theorem cell21_2082541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2082541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082541 prefixEnd_2082541 := by exact prefixLift 2082541
  have htrace : WordTrace (prefixWord ++ tailWord_2082541) baseStart_2082541 baseEnd_2082541 := by
    simpa [prefixWord, tailWord_2082541, baseEnd_2082541] using wordTrace_append hprefix tailTrace_2082541
  have hstable : (prefixWord ++ tailWord_2082541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082541).length < 2 ^ (prefixWord ++ tailWord_2082541).sum := by decide
  have hdescent : baseEnd_2082541 < baseStart_2082541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082606 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2082606 : Nat := 118140960795 + 2082606 * 2 ^ 59
def prefixEnd_2082606 : Nat := 4983230072969 + 3 ^ 40 * 2082606 * 2
def baseEnd_2082606 : Nat := 475279063083370679176567

theorem tailTrace_2082606 : CollatzResearch.WordTrace tailWord_2082606 prefixEnd_2082606 475279063083370679176567 := by
  unfold tailWord_2082606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494860136635202204089459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50639254062054411755143781 9494860136635202204089459)
  ·
    refine ⟨14242290204952803306134189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494860136635202204089459 14242290204952803306134189)
    ·
      refine ⟨5340858826857301239800321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14242290204952803306134189 5340858826857301239800321)
      ·
        refine ⟨4005644120142975929850241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5340858826857301239800321 4005644120142975929850241)
        ·
          refine ⟨3004233090107231947387681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005644120142975929850241 3004233090107231947387681)
          ·
            refine ⟨2253174817580423960540761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004233090107231947387681 2253174817580423960540761)
            ·
              refine ⟨1689881113185317970405571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253174817580423960540761 1689881113185317970405571)
              ·
                refine ⟨2534821669777976955608357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689881113185317970405571 2534821669777976955608357)
                ·
                  refine ⟨475279063083370679176567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534821669777976955608357 475279063083370679176567)
                  ·
                    rfl

theorem cell21_2082606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2082606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082606 prefixEnd_2082606 := by exact prefixLift 2082606
  have htrace : WordTrace (prefixWord ++ tailWord_2082606) baseStart_2082606 baseEnd_2082606 := by
    simpa [prefixWord, tailWord_2082606, baseEnd_2082606] using wordTrace_append hprefix tailTrace_2082606
  have hstable : (prefixWord ++ tailWord_2082606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082606).length < 2 ^ (prefixWord ++ tailWord_2082606).sum := by decide
  have hdescent : baseEnd_2082606 < baseStart_2082606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082693 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 3]
def baseStart_2082693 : Nat := 118140960795 + 2082693 * 2 ^ 59
def prefixEnd_2082693 : Nat := 4983230072969 + 3 ^ 40 * 2082693 * 2
def baseEnd_2082693 : Nat := 475298917668677861226389

theorem tailTrace_2082693 : CollatzResearch.WordTrace tailWord_2082693 prefixEnd_2082693 475298917668677861226389 := by
  unfold tailWord_2082693
  simp only [CollatzResearch.WordTrace]
  refine ⟨75962054243766431491132733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50641369495844287660755155 75962054243766431491132733)
  ·
    refine ⟨28485770341412411809174775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75962054243766431491132733 28485770341412411809174775)
    ·
      refine ⟨42728655512118617713762163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28485770341412411809174775 42728655512118617713762163)
      ·
        refine ⟨64092983268177926570643245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42728655512118617713762163 64092983268177926570643245)
        ·
          refine ⟨24034868725566722463991217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64092983268177926570643245 24034868725566722463991217)
          ·
            refine ⟨18026151544175041847993413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24034868725566722463991217 18026151544175041847993413)
            ·
              refine ⟨3379903414532820346498765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18026151544175041847993413 3379903414532820346498765)
              ·
                refine ⟨1267463780449807629937037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3379903414532820346498765 1267463780449807629937037)
                ·
                  refine ⟨475298917668677861226389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267463780449807629937037 475298917668677861226389)
                  ·
                    rfl

theorem cell21_2082693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_2082693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082693 prefixEnd_2082693 := by exact prefixLift 2082693
  have htrace : WordTrace (prefixWord ++ tailWord_2082693) baseStart_2082693 baseEnd_2082693 := by
    simpa [prefixWord, tailWord_2082693, baseEnd_2082693] using wordTrace_append hprefix tailTrace_2082693
  have hstable : (prefixWord ++ tailWord_2082693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082693).length < 2 ^ (prefixWord ++ tailWord_2082693).sum := by decide
  have hdescent : baseEnd_2082693 < baseStart_2082693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082724 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2082724 : Nat := 118140960795 + 2082724 * 2 ^ 59
def prefixEnd_2082724 : Nat := 4983230072969 + 3 ^ 40 * 2082724 * 2
def baseEnd_2082724 : Nat := 475305992291028696209659

theorem tailTrace_2082724 : CollatzResearch.WordTrace tailWord_2082724 prefixEnd_2082724 475305992291028696209659 := by
  unfold tailWord_2082724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37981592453327061892755613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50642123271102749190340817 37981592453327061892755613)
  ·
    refine ⟨14243097169997648209783355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37981592453327061892755613 14243097169997648209783355)
    ·
      refine ⟨21364645754996472314675033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14243097169997648209783355 21364645754996472314675033)
      ·
        refine ⟨16023484316247354236006275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21364645754996472314675033 16023484316247354236006275)
        ·
          refine ⟨24035226474371031354009413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16023484316247354236006275 24035226474371031354009413)
          ·
            refine ⟨4506604963944568378876765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24035226474371031354009413 4506604963944568378876765)
            ·
              refine ⟨1689976861479213142078787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4506604963944568378876765 1689976861479213142078787)
              ·
                refine ⟨2534965292218819713118181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689976861479213142078787 2534965292218819713118181)
                ·
                  refine ⟨475305992291028696209659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534965292218819713118181 475305992291028696209659)
                  ·
                    rfl

theorem cell21_2082724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2082724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082724 prefixEnd_2082724 := by exact prefixLift 2082724
  have htrace : WordTrace (prefixWord ++ tailWord_2082724) baseStart_2082724 baseEnd_2082724 := by
    simpa [prefixWord, tailWord_2082724, baseEnd_2082724] using wordTrace_append hprefix tailTrace_2082724
  have hstable : (prefixWord ++ tailWord_2082724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082724).length < 2 ^ (prefixWord ++ tailWord_2082724).sum := by decide
  have hdescent : baseEnd_2082724 < baseStart_2082724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082735 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_2082735 : Nat := 118140960795 + 2082735 * 2 ^ 59
def prefixEnd_2082735 : Nat := 4983230072969 + 3 ^ 40 * 2082735 * 2
def baseEnd_2082735 : Nat := 475308502640895121526303

theorem tailTrace_2082735 : CollatzResearch.WordTrace tailWord_2082735 prefixEnd_2082735 475308502640895121526303 := by
  unfold tailWord_2082735
  simp only [CollatzResearch.WordTrace]
  refine ⟨75963586109614272664161659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50642390739742848442774439 75963586109614272664161659)
  ·
    refine ⟨113945379164421408996242489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75963586109614272664161659 113945379164421408996242489)
    ·
      refine ⟨85459034373316056747181867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113945379164421408996242489 85459034373316056747181867)
      ·
        refine ⟨128188551559974085120772801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85459034373316056747181867 128188551559974085120772801)
        ·
          refine ⟨96141413669980563840579601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128188551559974085120772801 96141413669980563840579601)
          ·
            refine ⟨72106060252485422880434701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96141413669980563840579601 72106060252485422880434701)
            ·
              refine ⟨27039772594682033580163013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72106060252485422880434701 27039772594682033580163013)
              ·
                refine ⟨5069957361502881296280565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27039772594682033580163013 5069957361502881296280565)
                ·
                  refine ⟨475308502640895121526303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5069957361502881296280565 475308502640895121526303)
                  ·
                    rfl

theorem cell21_2082735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_2082735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082735 prefixEnd_2082735 := by exact prefixLift 2082735
  have htrace : WordTrace (prefixWord ++ tailWord_2082735) baseStart_2082735 baseEnd_2082735 := by
    simpa [prefixWord, tailWord_2082735, baseEnd_2082735] using wordTrace_append hprefix tailTrace_2082735
  have hstable : (prefixWord ++ tailWord_2082735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082735).length < 2 ^ (prefixWord ++ tailWord_2082735).sum := by decide
  have hdescent : baseEnd_2082735 < baseStart_2082735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
