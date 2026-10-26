import V185TrunkScan23Chunk0353

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2094632 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2094632 : Nat := 118140960795 + 2094632 * 2 ^ 59
def prefixEnd_2094632 : Nat := 4983230072969 + 3 ^ 40 * 2094632 * 2
def baseEnd_2094632 : Nat := 1075553010288553976366969

theorem tailTrace_2094632 : CollatzResearch.WordTrace tailWord_2094632 prefixEnd_2094632 1075553010288553976366969 := by
  unfold tailWord_2094632
  simp only [CollatzResearch.WordTrace]
  refine ⟨38198752673756736754999075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50931670231675649006665433 38198752673756736754999075)
  ·
    refine ⟨57298129010635105132498613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38198752673756736754999075 57298129010635105132498613)
    ·
      refine ⟨5371699594747041106171745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57298129010635105132498613 5371699594747041106171745)
      ·
        refine ⟨4028774696060280829628809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5371699594747041106171745 4028774696060280829628809)
        ·
          refine ⟨3021581022045210622221607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4028774696060280829628809 3021581022045210622221607)
          ·
            refine ⟨4532371533067815933332411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021581022045210622221607 4532371533067815933332411)
            ·
              refine ⟨6798557299601723899998617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532371533067815933332411 6798557299601723899998617)
              ·
                refine ⟨5098917974701292924998963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798557299601723899998617 5098917974701292924998963)
                ·
                  refine ⟨7648376962051939387498445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098917974701292924998963 7648376962051939387498445)
                  ·
                    refine ⟨2868141360769477270311917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7648376962051939387498445 2868141360769477270311917)
                    ·
                      refine ⟨1075553010288553976366969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868141360769477270311917 1075553010288553976366969)
                      ·
                        rfl

theorem cell23_2094632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2094632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094632 prefixEnd_2094632 := by exact prefixLift 2094632
  have htrace : WordTrace (prefixWord ++ tailWord_2094632) baseStart_2094632 baseEnd_2094632 := by
    simpa [prefixWord, tailWord_2094632, baseEnd_2094632] using wordTrace_append hprefix tailTrace_2094632
  have hstable : (prefixWord ++ tailWord_2094632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094632).length < 2 ^ (prefixWord ++ tailWord_2094632).sum := by decide
  have hdescent : baseEnd_2094632 < baseStart_2094632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094668 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2094668 : Nat := 118140960795 + 2094668 * 2 ^ 59
def prefixEnd_2094668 : Nat := 4983230072969 + 3 ^ 40 * 2094668 * 2
def baseEnd_2094668 : Nat := 1075571495592115835516803

theorem tailTrace_2094668 : CollatzResearch.WordTrace tailWord_2094668 prefixEnd_2094668 1075571495592115835516803 := by
  unfold tailWord_2094668
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199409187691525829154329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50932545583588701105539105 38199409187691525829154329)
  ·
    refine ⟨28649556890768644371865747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38199409187691525829154329 28649556890768644371865747)
    ·
      refine ⟨42974335336152966557798621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28649556890768644371865747 42974335336152966557798621)
      ·
        refine ⟨16115375751057362459174483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42974335336152966557798621 16115375751057362459174483)
        ·
          refine ⟨24173063626586043688761725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115375751057362459174483 24173063626586043688761725)
          ·
            refine ⟨9064898859969766383285647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24173063626586043688761725 9064898859969766383285647)
            ·
              refine ⟨13597348289954649574928471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064898859969766383285647 13597348289954649574928471)
              ·
                refine ⟨20396022434931974362392707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597348289954649574928471 20396022434931974362392707)
                ·
                  refine ⟨30594033652397961543589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20396022434931974362392707 30594033652397961543589061)
                  ·
                    refine ⟨5736381309824617789422949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30594033652397961543589061 5736381309824617789422949)
                    ·
                      refine ⟨1075571495592115835516803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5736381309824617789422949 1075571495592115835516803)
                      ·
                        rfl

theorem cell23_2094668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2094668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094668 prefixEnd_2094668 := by exact prefixLift 2094668
  have htrace : WordTrace (prefixWord ++ tailWord_2094668) baseStart_2094668 baseEnd_2094668 := by
    simpa [prefixWord, tailWord_2094668, baseEnd_2094668] using wordTrace_append hprefix tailTrace_2094668
  have hstable : (prefixWord ++ tailWord_2094668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094668).length < 2 ^ (prefixWord ++ tailWord_2094668).sum := by decide
  have hdescent : baseEnd_2094668 < baseStart_2094668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094672 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2]
def baseStart_2094672 : Nat := 118140960795 + 2094672 * 2 ^ 59
def prefixEnd_2094672 : Nat := 4983230072969 + 3 ^ 40 * 2094672 * 2
def baseEnd_2094672 : Nat := 1075573549514733819866785

theorem tailTrace_2094672 : CollatzResearch.WordTrace tailWord_2094672 prefixEnd_2094672 1075573549514733819866785 := by
  unfold tailWord_2094672
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199482133684280170727135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50932642844912373560969513 38199482133684280170727135)
  ·
    refine ⟨57299223200526420256090703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38199482133684280170727135 57299223200526420256090703)
    ·
      refine ⟨85948834800789630384136055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57299223200526420256090703 85948834800789630384136055)
      ·
        refine ⟨128923252201184445576204083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85948834800789630384136055 128923252201184445576204083)
        ·
          refine ⟨193384878301776668364306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128923252201184445576204083 193384878301776668364306125)
          ·
            refine ⟨72519329363166250636614797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193384878301776668364306125 72519329363166250636614797)
            ·
              refine ⟨27194748511187343988730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72519329363166250636614797 27194748511187343988730549)
              ·
                refine ⟨2549507672923813498943489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27194748511187343988730549 2549507672923813498943489)
                ·
                  refine ⟨1912130754692860124207617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2549507672923813498943489 1912130754692860124207617)
                  ·
                    refine ⟨1434098066019645093155713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912130754692860124207617 1434098066019645093155713)
                    ·
                      refine ⟨1075573549514733819866785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434098066019645093155713 1075573549514733819866785)
                      ·
                        rfl

theorem cell23_2094672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2].length) (baseStart_2094672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094672 prefixEnd_2094672 := by exact prefixLift 2094672
  have htrace : WordTrace (prefixWord ++ tailWord_2094672) baseStart_2094672 baseEnd_2094672 := by
    simpa [prefixWord, tailWord_2094672, baseEnd_2094672] using wordTrace_append hprefix tailTrace_2094672
  have hstable : (prefixWord ++ tailWord_2094672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094672).length < 2 ^ (prefixWord ++ tailWord_2094672).sum := by decide
  have hdescent : baseEnd_2094672 < baseStart_2094672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094688 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2094688 : Nat := 118140960795 + 2094688 * 2 ^ 59
def prefixEnd_2094688 : Nat := 4983230072969 + 3 ^ 40 * 2094688 * 2
def baseEnd_2094688 : Nat := 1075581765205205757266711

theorem tailTrace_2094688 : CollatzResearch.WordTrace tailWord_2094688 prefixEnd_2094688 1075581765205205757266711 := by
  unfold tailWord_2094688
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199773917655297537018359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50933031890207063382691145 38199773917655297537018359)
  ·
    refine ⟨57299660876482946305527539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38199773917655297537018359 57299660876482946305527539)
    ·
      refine ⟨85949491314724419458291309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57299660876482946305527539 85949491314724419458291309)
      ·
        refine ⟨32231059243021657296859241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85949491314724419458291309 32231059243021657296859241)
        ·
          refine ⟨24173294432266242972644431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32231059243021657296859241 24173294432266242972644431)
          ·
            refine ⟨36259941648399364458966647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173294432266242972644431 36259941648399364458966647)
            ·
              refine ⟨54389912472599046688449971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36259941648399364458966647 54389912472599046688449971)
              ·
                refine ⟨81584868708898570032674957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54389912472599046688449971 81584868708898570032674957)
                ·
                  refine ⟨30594325765836963762253109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81584868708898570032674957 30594325765836963762253109)
                  ·
                    refine ⟨2868218040547215352711229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30594325765836963762253109 2868218040547215352711229)
                    ·
                      refine ⟨1075581765205205757266711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868218040547215352711229 1075581765205205757266711)
                      ·
                        rfl

theorem cell23_2094688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2094688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094688 prefixEnd_2094688 := by exact prefixLift 2094688
  have htrace : WordTrace (prefixWord ++ tailWord_2094688) baseStart_2094688 baseEnd_2094688 := by
    simpa [prefixWord, tailWord_2094688, baseEnd_2094688] using wordTrace_append hprefix tailTrace_2094688
  have hstable : (prefixWord ++ tailWord_2094688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094688).length < 2 ^ (prefixWord ++ tailWord_2094688).sum := by decide
  have hdescent : baseEnd_2094688 < baseStart_2094688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094695 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 5]
def baseStart_2094695 : Nat := 118140960795 + 2094695 * 2 ^ 59
def prefixEnd_2094695 : Nat := 4983230072969 + 3 ^ 40 * 2094695 * 2
def baseEnd_2094695 : Nat := 119509484396643025542131

theorem tailTrace_2094695 : CollatzResearch.WordTrace tailWord_2094695 prefixEnd_2094695 119509484396643025542131 := by
  unfold tailWord_2094695
  simp only [CollatzResearch.WordTrace]
  refine ⟨76399803146285235269541539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50933202097523490179694359 76399803146285235269541539)
  ·
    refine ⟨114599704719427852904312309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76399803146285235269541539 114599704719427852904312309)
    ·
      refine ⟨10743722317446361209779279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114599704719427852904312309 10743722317446361209779279)
      ·
        refine ⟨16115583476169541814668919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743722317446361209779279 16115583476169541814668919)
        ·
          refine ⟨24173375214254312722003379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115583476169541814668919 24173375214254312722003379)
          ·
            refine ⟨36260062821381469083005069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173375214254312722003379 36260062821381469083005069)
            ·
              refine ⟨13597523558018050906126901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36260062821381469083005069 13597523558018050906126901)
              ·
                refine ⟨1274767833564192272449397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13597523558018050906126901 1274767833564192272449397)
                ·
                  refine ⟨119509484396643025542131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274767833564192272449397 119509484396643025542131)
                  ·
                    rfl

theorem cell23_2094695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 5].length) (baseStart_2094695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094695 prefixEnd_2094695 := by exact prefixLift 2094695
  have htrace : WordTrace (prefixWord ++ tailWord_2094695) baseStart_2094695 baseEnd_2094695 := by
    simpa [prefixWord, tailWord_2094695, baseEnd_2094695] using wordTrace_append hprefix tailTrace_2094695
  have hstable : (prefixWord ++ tailWord_2094695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094695).length < 2 ^ (prefixWord ++ tailWord_2094695).sum := by decide
  have hdescent : baseEnd_2094695 < baseStart_2094695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094706 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2094706 : Nat := 118140960795 + 2094706 * 2 ^ 59
def prefixEnd_2094706 : Nat := 4983230072969 + 3 ^ 40 * 2094706 * 2
def baseEnd_2094706 : Nat := 1075591007856986686841629

theorem tailTrace_2094706 : CollatzResearch.WordTrace tailWord_2094706 prefixEnd_2094706 1075591007856986686841629 := by
  unfold tailWord_2094706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19100051087311346037047993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50933469566163589432127981 19100051087311346037047993)
  ·
    refine ⟨14325038315483509527785995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19100051087311346037047993 14325038315483509527785995)
    ·
      refine ⟨21487557473225264291678993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325038315483509527785995 21487557473225264291678993)
      ·
        refine ⟨16115668104918948218759245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21487557473225264291678993 16115668104918948218759245)
        ·
          refine ⟨6043375539344605582034717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16115668104918948218759245 6043375539344605582034717)
          ·
            refine ⟨2266265827254227093263019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6043375539344605582034717 2266265827254227093263019)
            ·
              refine ⟨3399398740881340639894529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266265827254227093263019 3399398740881340639894529)
              ·
                refine ⟨2549549055661005479920897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3399398740881340639894529 2549549055661005479920897)
                ·
                  refine ⟨1912161791745754109940673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2549549055661005479920897 1912161791745754109940673)
                  ·
                    refine ⟨1434121343809315582455505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912161791745754109940673 1434121343809315582455505)
                    ·
                      refine ⟨1075591007856986686841629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434121343809315582455505 1075591007856986686841629)
                      ·
                        rfl

theorem cell23_2094706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2094706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094706 prefixEnd_2094706 := by exact prefixLift 2094706
  have htrace : WordTrace (prefixWord ++ tailWord_2094706) baseStart_2094706 baseEnd_2094706 := by
    simpa [prefixWord, tailWord_2094706, baseEnd_2094706] using wordTrace_append hprefix tailTrace_2094706
  have hstable : (prefixWord ++ tailWord_2094706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094706).length < 2 ^ (prefixWord ++ tailWord_2094706).sum := by decide
  have hdescent : baseEnd_2094706 < baseStart_2094706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 4, 2]
def baseStart_2094745 : Nat := 118140960795 + 2094745 * 2 ^ 59
def prefixEnd_2094745 : Nat := 4983230072969 + 3 ^ 40 * 2094745 * 2
def baseEnd_2094745 : Nat := 1075611033602512034253949

theorem tailTrace_2094745 : CollatzResearch.WordTrace tailWord_2094745 prefixEnd_2094745 1075611033602512034253949 := by
  unfold tailWord_2094745
  simp only [CollatzResearch.WordTrace]
  refine ⟨76401626796104093808861689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50934417864069395872574459 76401626796104093808861689)
  ·
    refine ⟨57301220097078070356646267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76401626796104093808861689 57301220097078070356646267)
    ·
      refine ⟨85951830145617105534969401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57301220097078070356646267 85951830145617105534969401)
      ·
        refine ⟨64463872609212829151227051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85951830145617105534969401 64463872609212829151227051)
        ·
          refine ⟨96695808913819243726840577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64463872609212829151227051 96695808913819243726840577)
          ·
            refine ⟨72521856685364432795130433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96695808913819243726840577 72521856685364432795130433)
            ·
              refine ⟨54391392514023324596347825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72521856685364432795130433 54391392514023324596347825)
              ·
                refine ⟨40793544385517493447260869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54391392514023324596347825 40793544385517493447260869)
                ·
                  refine ⟨7648789572284530021361413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40793544385517493447260869 7648789572284530021361413)
                  ·
                    refine ⟨1434148044803349379005265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648789572284530021361413 1434148044803349379005265)
                    ·
                      refine ⟨1075611033602512034253949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434148044803349379005265 1075611033602512034253949)
                      ·
                        rfl

theorem cell23_2094745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_2094745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094745 prefixEnd_2094745 := by exact prefixLift 2094745
  have htrace : WordTrace (prefixWord ++ tailWord_2094745) baseStart_2094745 baseEnd_2094745 := by
    simpa [prefixWord, tailWord_2094745, baseEnd_2094745] using wordTrace_append hprefix tailTrace_2094745
  have hstable : (prefixWord ++ tailWord_2094745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094745).length < 2 ^ (prefixWord ++ tailWord_2094745).sum := by decide
  have hdescent : baseEnd_2094745 < baseStart_2094745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094768 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 8]
def baseStart_2094768 : Nat := 118140960795 + 2094768 * 2 ^ 59
def prefixEnd_2094768 : Nat := 4983230072969 + 3 ^ 40 * 2094768 * 2
def baseEnd_2094768 : Nat := 119513649295285049362927

theorem tailTrace_2094768 : CollatzResearch.WordTrace tailWord_2094768 prefixEnd_2094768 119513649295285049362927 := by
  unfold tailWord_2094768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201232837510384368474479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50934977116680512491299305 38201232837510384368474479)
  ·
    refine ⟨57301849256265576552711719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38201232837510384368474479 57301849256265576552711719)
    ·
      refine ⟨85952773884398364829067579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57301849256265576552711719 85952773884398364829067579)
      ·
        refine ⟨128929160826597547243601369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85952773884398364829067579 128929160826597547243601369)
        ·
          refine ⟨96696870619948160432701027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128929160826597547243601369 96696870619948160432701027)
          ·
            refine ⟨145045305929922240649051541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96696870619948160432701027 145045305929922240649051541)
            ·
              refine ⟨6798998715465105030424291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145045305929922240649051541 6798998715465105030424291)
              ·
                refine ⟨10198498073197657545636437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798998715465105030424291 10198498073197657545636437)
                ·
                  refine ⟨119513649295285049362927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10198498073197657545636437 119513649295285049362927)
                  ·
                    rfl

theorem cell23_2094768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_2094768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094768 prefixEnd_2094768 := by exact prefixLift 2094768
  have htrace : WordTrace (prefixWord ++ tailWord_2094768) baseStart_2094768 baseEnd_2094768 := by
    simpa [prefixWord, tailWord_2094768, baseEnd_2094768] using wordTrace_append hprefix tailTrace_2094768
  have hstable : (prefixWord ++ tailWord_2094768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094768).length < 2 ^ (prefixWord ++ tailWord_2094768).sum := by decide
  have hdescent : baseEnd_2094768 < baseStart_2094768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094835 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4]
def baseStart_2094835 : Nat := 118140960795 + 2094835 * 2 ^ 59
def prefixEnd_2094835 : Nat := 4983230072969 + 3 ^ 40 * 2094835 * 2
def baseEnd_2094835 : Nat := 1075657246861416682128535

theorem tailTrace_2094835 : CollatzResearch.WordTrace tailWord_2094835 prefixEnd_2094835 1075657246861416682128535 := by
  unfold tailWord_2094835
  simp only [CollatzResearch.WordTrace]
  refine ⟨76404909365778039179637959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50936606243852026119758639 76404909365778039179637959)
  ·
    refine ⟨114607364048667058769456939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76404909365778039179637959 114607364048667058769456939)
    ·
      refine ⟨171911046073000588154185409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114607364048667058769456939 171911046073000588154185409)
      ·
        refine ⟨128933284554750441115639057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171911046073000588154185409 128933284554750441115639057)
        ·
          refine ⟨96699963416062830836729293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128933284554750441115639057 96699963416062830836729293)
          ·
            refine ⟨36262486281023561563773485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96699963416062830836729293 36262486281023561563773485)
            ·
              refine ⟨13598432355383835586415057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36262486281023561563773485 13598432355383835586415057)
              ·
                refine ⟨10198824266537876689811293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13598432355383835586415057 10198824266537876689811293)
                ·
                  refine ⟨3824559099951703758679235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10198824266537876689811293 3824559099951703758679235)
                  ·
                    refine ⟨5736838649927555638018853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824559099951703758679235 5736838649927555638018853)
                    ·
                      refine ⟨1075657246861416682128535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5736838649927555638018853 1075657246861416682128535)
                      ·
                        rfl

theorem cell23_2094835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_2094835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094835 prefixEnd_2094835 := by exact prefixLift 2094835
  have htrace : WordTrace (prefixWord ++ tailWord_2094835) baseStart_2094835 baseEnd_2094835 := by
    simpa [prefixWord, tailWord_2094835, baseEnd_2094835] using wordTrace_append hprefix tailTrace_2094835
  have hstable : (prefixWord ++ tailWord_2094835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094835).length < 2 ^ (prefixWord ++ tailWord_2094835).sum := by decide
  have hdescent : baseEnd_2094835 < baseStart_2094835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094846 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2094846 : Nat := 118140960795 + 2094846 * 2 ^ 59
def prefixEnd_2094846 : Nat := 4983230072969 + 3 ^ 40 * 2094846 * 2
def baseEnd_2094846 : Nat := 1075662895148616139090985

theorem tailTrace_2094846 : CollatzResearch.WordTrace tailWord_2094846 prefixEnd_2094846 1075662895148616139090985 := by
  unfold tailWord_2094846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550663821092273507286049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50936873712492125372192261 9550663821092273507286049)
  ·
    refine ⟨7162997865819205130464537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9550663821092273507286049 7162997865819205130464537)
    ·
      refine ⟨5372248399364403847848403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162997865819205130464537 5372248399364403847848403)
      ·
        refine ⟨8058372599046605771772605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372248399364403847848403 8058372599046605771772605)
        ·
          refine ⟨3021889724642477164414727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8058372599046605771772605 3021889724642477164414727)
          ·
            refine ⟨4532834586963715746622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021889724642477164414727 4532834586963715746622091)
            ·
              refine ⟨6799251880445573619933137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532834586963715746622091 6799251880445573619933137)
              ·
                refine ⟨5099438910334180214949853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799251880445573619933137 5099438910334180214949853)
                ·
                  refine ⟨1912289591375317580606195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5099438910334180214949853 1912289591375317580606195)
                  ·
                    refine ⟨2868434387062976370909293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912289591375317580606195 2868434387062976370909293)
                    ·
                      refine ⟨1075662895148616139090985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868434387062976370909293 1075662895148616139090985)
                      ·
                        rfl

theorem cell23_2094846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2094846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094846 prefixEnd_2094846 := by exact prefixLift 2094846
  have htrace : WordTrace (prefixWord ++ tailWord_2094846) baseStart_2094846 baseEnd_2094846 := by
    simpa [prefixWord, tailWord_2094846, baseEnd_2094846] using wordTrace_append hprefix tailTrace_2094846
  have hstable : (prefixWord ++ tailWord_2094846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094846).length < 2 ^ (prefixWord ++ tailWord_2094846).sum := by decide
  have hdescent : baseEnd_2094846 < baseStart_2094846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094852 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2094852 : Nat := 118140960795 + 2094852 * 2 ^ 59
def prefixEnd_2094852 : Nat := 4983230072969 + 3 ^ 40 * 2094852 * 2
def baseEnd_2094852 : Nat := 1075665976032543115615957

theorem tailTrace_2094852 : CollatzResearch.WordTrace tailWord_2094852 prefixEnd_2094852 1075665976032543115615957 := by
  unfold tailWord_2094852
  simp only [CollatzResearch.WordTrace]
  refine ⟨38202764703358225541503405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50937019604477634055337873 38202764703358225541503405)
  ·
    refine ⟨14326036763759334578063777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38202764703358225541503405 14326036763759334578063777)
    ·
      refine ⟨10744527572819500933547833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14326036763759334578063777 10744527572819500933547833)
      ·
        refine ⟨8058395679614625700160875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10744527572819500933547833 8058395679614625700160875)
        ·
          refine ⟨12087593519421938550241313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058395679614625700160875 12087593519421938550241313)
          ·
            refine ⟨9065695139566453912680985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087593519421938550241313 9065695139566453912680985)
            ·
              refine ⟨6799271354674840434510739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065695139566453912680985 6799271354674840434510739)
              ·
                refine ⟨10198907032012260651766109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799271354674840434510739 10198907032012260651766109)
                ·
                  refine ⟨3824590137004597744412291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10198907032012260651766109 3824590137004597744412291)
                  ·
                    refine ⟨5736885205506896616618437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824590137004597744412291 5736885205506896616618437)
                    ·
                      refine ⟨1075665976032543115615957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5736885205506896616618437 1075665976032543115615957)
                      ·
                        rfl

theorem cell23_2094852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2094852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094852 prefixEnd_2094852 := by exact prefixLift 2094852
  have htrace : WordTrace (prefixWord ++ tailWord_2094852) baseStart_2094852 baseEnd_2094852 := by
    simpa [prefixWord, tailWord_2094852, baseEnd_2094852] using wordTrace_append hprefix tailTrace_2094852
  have hstable : (prefixWord ++ tailWord_2094852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094852).length < 2 ^ (prefixWord ++ tailWord_2094852).sum := by decide
  have hdescent : baseEnd_2094852 < baseStart_2094852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094866 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2094866 : Nat := 118140960795 + 2094866 * 2 ^ 59
def prefixEnd_2094866 : Nat := 4983230072969 + 3 ^ 40 * 2094866 * 2
def baseEnd_2094866 : Nat := 358557721587235353613631

theorem tailTrace_2094866 : CollatzResearch.WordTrace tailWord_2094866 prefixEnd_2094866 358557721587235353613631 := by
  unfold tailWord_2094866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101510007166432868504113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50937360019110487649344301 19101510007166432868504113)
  ·
    refine ⟨14326132505374824651378085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19101510007166432868504113 14326132505374824651378085)
    ·
      refine ⟨2686149844757779622133391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14326132505374824651378085 2686149844757779622133391)
      ·
        refine ⟨4029224767136669433200087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686149844757779622133391 4029224767136669433200087)
        ·
          refine ⟨6043837150705004149800131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029224767136669433200087 6043837150705004149800131)
          ·
            refine ⟨9065755726057506224700197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043837150705004149800131 9065755726057506224700197)
            ·
              refine ⟨1699829198635782417131287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9065755726057506224700197 1699829198635782417131287)
              ·
                refine ⟨2549743797953673625696931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699829198635782417131287 2549743797953673625696931)
                ·
                  refine ⟨3824615696930510438545397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549743797953673625696931 3824615696930510438545397)
                  ·
                    refine ⟨358557721587235353613631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3824615696930510438545397 358557721587235353613631)
                    ·
                      rfl

theorem cell23_2094866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2094866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094866 prefixEnd_2094866 := by exact prefixLift 2094866
  have htrace : WordTrace (prefixWord ++ tailWord_2094866) baseStart_2094866 baseEnd_2094866 := by
    simpa [prefixWord, tailWord_2094866, baseEnd_2094866] using wordTrace_append hprefix tailTrace_2094866
  have hstable : (prefixWord ++ tailWord_2094866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094866).length < 2 ^ (prefixWord ++ tailWord_2094866).sum := by decide
  have hdescent : baseEnd_2094866 < baseStart_2094866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094869 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_2094869 : Nat := 118140960795 + 2094869 * 2 ^ 59
def prefixEnd_2094869 : Nat := 4983230072969 + 3 ^ 40 * 2094869 * 2
def baseEnd_2094869 : Nat := 1075674705203669549103379

theorem tailTrace_2094869 : CollatzResearch.WordTrace tailWord_2094869 prefixEnd_2094869 1075674705203669549103379 := by
  unfold tailWord_2094869
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406149447654862986375661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50937432965103241990917107 76406149447654862986375661)
  ·
    refine ⟨28652306042870573619890873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76406149447654862986375661 28652306042870573619890873)
    ·
      refine ⟨21489229532152930214918155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28652306042870573619890873 21489229532152930214918155)
      ·
        refine ⟨32233844298229395322377233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21489229532152930214918155 32233844298229395322377233)
        ·
          refine ⟨24175383223672046491782925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32233844298229395322377233 24175383223672046491782925)
          ·
            refine ⟨9065768708877017434418597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24175383223672046491782925 9065768708877017434418597)
            ·
              refine ⟨1699831632914440768953487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9065768708877017434418597 1699831632914440768953487)
              ·
                refine ⟨2549747449371661153430231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699831632914440768953487 2549747449371661153430231)
                ·
                  refine ⟨3824621174057491730145347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549747449371661153430231 3824621174057491730145347)
                  ·
                    refine ⟨5736931761086237595218021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824621174057491730145347 5736931761086237595218021)
                    ·
                      refine ⟨1075674705203669549103379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5736931761086237595218021 1075674705203669549103379)
                      ·
                        rfl

theorem cell23_2094869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_2094869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094869 prefixEnd_2094869 := by exact prefixLift 2094869
  have htrace : WordTrace (prefixWord ++ tailWord_2094869) baseStart_2094869 baseEnd_2094869 := by
    simpa [prefixWord, tailWord_2094869, baseEnd_2094869] using wordTrace_append hprefix tailTrace_2094869
  have hstable : (prefixWord ++ tailWord_2094869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094869).length < 2 ^ (prefixWord ++ tailWord_2094869).sum := by decide
  have hdescent : baseEnd_2094869 < baseStart_2094869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094899 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 4]
def baseStart_2094899 : Nat := 118140960795 + 2094899 * 2 ^ 59
def prefixEnd_2094899 : Nat := 4983230072969 + 3 ^ 40 * 2094899 * 2
def baseEnd_2094899 : Nat := 1075690109623304431728241

theorem tailTrace_2094899 : CollatzResearch.WordTrace tailWord_2094899 prefixEnd_2094899 1075690109623304431728241 := by
  unfold tailWord_2094899
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407243637546178109967751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50938162425030785406645167 76407243637546178109967751)
  ·
    refine ⟨114610865456319267164951627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76407243637546178109967751 114610865456319267164951627)
    ·
      refine ⟨171916298184478900747427441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114610865456319267164951627 171916298184478900747427441)
      ·
        refine ⟨128937223638359175560570581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171916298184478900747427441 128937223638359175560570581)
        ·
          refine ⟨3021966179024043177200873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128937223638359175560570581 3021966179024043177200873)
          ·
            refine ⟨2266474634268032382900655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021966179024043177200873 2266474634268032382900655)
            ·
              refine ⟨3399711951402048574350983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266474634268032382900655 3399711951402048574350983)
              ·
                refine ⟨5099567927103072861526475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399711951402048574350983 5099567927103072861526475)
                ·
                  refine ⟨7649351890654609292289713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099567927103072861526475 7649351890654609292289713)
                  ·
                    refine ⟨5737013917990956969217285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649351890654609292289713 5737013917990956969217285)
                    ·
                      refine ⟨1075690109623304431728241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5737013917990956969217285 1075690109623304431728241)
                      ·
                        rfl

theorem cell23_2094899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_2094899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094899 prefixEnd_2094899 := by exact prefixLift 2094899
  have htrace : WordTrace (prefixWord ++ tailWord_2094899) baseStart_2094899 baseEnd_2094899 := by
    simpa [prefixWord, tailWord_2094899, baseEnd_2094899] using wordTrace_append hprefix tailTrace_2094899
  have hstable : (prefixWord ++ tailWord_2094899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094899).length < 2 ^ (prefixWord ++ tailWord_2094899).sum := by decide
  have hdescent : baseEnd_2094899 < baseStart_2094899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094909 : List Nat := [1, 4, 1, 4, 1, 3, 2, 7]
def baseStart_2094909 : Nat := 118140960795 + 2094909 * 2 ^ 59
def prefixEnd_2094909 : Nat := 4983230072969 + 3 ^ 40 * 2094909 * 2
def baseEnd_2094909 : Nat := 39840564608512940466785

theorem tailTrace_2094909 : CollatzResearch.WordTrace tailWord_2094909 prefixEnd_2094909 39840564608512940466785 := by
  unfold tailWord_2094909
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407608367509949817831781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50938405578339966545221187 76407608367509949817831781)
  ·
    refine ⟨14326426568908115590843459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76407608367509949817831781 14326426568908115590843459)
    ·
      refine ⟨21489639853362173386265189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14326426568908115590843459 21489639853362173386265189)
      ·
        refine ⟨4029307472505407509924723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21489639853362173386265189 4029307472505407509924723)
        ·
          refine ⟨6043961208758111264887085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029307472505407509924723 6043961208758111264887085)
          ·
            refine ⟨2266485453284291724332657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6043961208758111264887085 2266485453284291724332657)
            ·
              refine ⟨1699864089963218793249493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266485453284291724332657 1699864089963218793249493)
              ·
                refine ⟨39840564608512940466785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1699864089963218793249493 39840564608512940466785)
                ·
                  rfl

theorem cell23_2094909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 7].length) (baseStart_2094909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094909 prefixEnd_2094909 := by exact prefixLift 2094909
  have htrace : WordTrace (prefixWord ++ tailWord_2094909) baseStart_2094909 baseEnd_2094909 := by
    simpa [prefixWord, tailWord_2094909, baseEnd_2094909] using wordTrace_append hprefix tailTrace_2094909
  have hstable : (prefixWord ++ tailWord_2094909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094909).length < 2 ^ (prefixWord ++ tailWord_2094909).sum := by decide
  have hdescent : baseEnd_2094909 < baseStart_2094909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094915 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_2094915 : Nat := 118140960795 + 2094915 * 2 ^ 59
def prefixEnd_2094915 : Nat := 4983230072969 + 3 ^ 40 * 2094915 * 2
def baseEnd_2094915 : Nat := 1075698325313776369128167

theorem tailTrace_2094915 : CollatzResearch.WordTrace tailWord_2094915 prefixEnd_2094915 1075698325313776369128167 := by
  unfold tailWord_2094915
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407827205488212842550199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50938551470325475228366799 76407827205488212842550199)
  ·
    refine ⟨114611740808232319263825299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76407827205488212842550199 114611740808232319263825299)
    ·
      refine ⟨171917611212348478895737949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114611740808232319263825299 171917611212348478895737949)
      ·
        refine ⟨64469104204630679585901731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171917611212348478895737949 64469104204630679585901731)
        ·
          refine ⟨96703656306946019378852597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64469104204630679585901731 96703656306946019378852597)
          ·
            refine ⟨9065967778776189316767431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96703656306946019378852597 9065967778776189316767431)
            ·
              refine ⟨13598951668164283975151147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065967778776189316767431 13598951668164283975151147)
              ·
                refine ⟨20398427502246425962726721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598951668164283975151147 20398427502246425962726721)
                ·
                  refine ⟨15298820626684819472045041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20398427502246425962726721 15298820626684819472045041)
                  ·
                    refine ⟨11474115470013614604033781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15298820626684819472045041 11474115470013614604033781)
                    ·
                      refine ⟨1075698325313776369128167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11474115470013614604033781 1075698325313776369128167)
                      ·
                        rfl

theorem cell23_2094915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_2094915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094915 prefixEnd_2094915 := by exact prefixLift 2094915
  have htrace : WordTrace (prefixWord ++ tailWord_2094915) baseStart_2094915 baseEnd_2094915 := by
    simpa [prefixWord, tailWord_2094915, baseEnd_2094915] using wordTrace_append hprefix tailTrace_2094915
  have hstable : (prefixWord ++ tailWord_2094915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094915).length < 2 ^ (prefixWord ++ tailWord_2094915).sum := by decide
  have hdescent : baseEnd_2094915 < baseStart_2094915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094945 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2094945 : Nat := 118140960795 + 2094945 * 2 ^ 59
def prefixEnd_2094945 : Nat := 4983230072969 + 3 ^ 40 * 2094945 * 2
def baseEnd_2094945 : Nat := 1075713729733411251753029

theorem tailTrace_2094945 : CollatzResearch.WordTrace tailWord_2094945 prefixEnd_2094945 1075713729733411251753029 := by
  unfold tailWord_2094945
  simp only [CollatzResearch.WordTrace]
  refine ⟨76408921395379527966142289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50939280930253018644094859 76408921395379527966142289)
  ·
    refine ⟨57306691046534645974606717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76408921395379527966142289 57306691046534645974606717)
    ·
      refine ⟨21490009142450492240477519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57306691046534645974606717 21490009142450492240477519)
      ·
        refine ⟨32235013713675738360716279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21490009142450492240477519 32235013713675738360716279)
        ·
          refine ⟨48352520570513607541074419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32235013713675738360716279 48352520570513607541074419)
          ·
            refine ⟨72528780855770411311611629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48352520570513607541074419 72528780855770411311611629)
            ·
              refine ⟨27198292820913904241854361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72528780855770411311611629 27198292820913904241854361)
              ·
                refine ⟨20398719615685428181390771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27198292820913904241854361 20398719615685428181390771)
                ·
                  refine ⟨30598079423528142272086157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398719615685428181390771 30598079423528142272086157)
                  ·
                    refine ⟨11474279783823053352032309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30598079423528142272086157 11474279783823053352032309)
                    ·
                      refine ⟨1075713729733411251753029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11474279783823053352032309 1075713729733411251753029)
                      ·
                        rfl

theorem cell23_2094945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2094945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094945 prefixEnd_2094945 := by exact prefixLift 2094945
  have htrace : WordTrace (prefixWord ++ tailWord_2094945) baseStart_2094945 baseEnd_2094945 := by
    simpa [prefixWord, tailWord_2094945, baseEnd_2094945] using wordTrace_append hprefix tailTrace_2094945
  have hstable : (prefixWord ++ tailWord_2094945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094945).length < 2 ^ (prefixWord ++ tailWord_2094945).sum := by decide
  have hdescent : baseEnd_2094945 < baseStart_2094945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094955 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_2094955 : Nat := 118140960795 + 2094955 * 2 ^ 59
def prefixEnd_2094955 : Nat := 4983230072969 + 3 ^ 40 * 2094955 * 2
def baseEnd_2094955 : Nat := 1075718864539956212627983

theorem tailTrace_2094955 : CollatzResearch.WordTrace tailWord_2094955 prefixEnd_2094955 1075718864539956212627983 := by
  unfold tailWord_2094955
  simp only [CollatzResearch.WordTrace]
  refine ⟨76409286125343299674006319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50939524083562199782670879 76409286125343299674006319)
  ·
    refine ⟨114613929188014949511009479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76409286125343299674006319 114613929188014949511009479)
    ·
      refine ⟨171920893782022424266514219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114613929188014949511009479 171920893782022424266514219)
      ·
        refine ⟨257881340673033636399771329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171920893782022424266514219 257881340673033636399771329)
        ·
          refine ⟨193411005504775227299828497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257881340673033636399771329 193411005504775227299828497)
          ·
            refine ⟨145058254128581420474871373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193411005504775227299828497 145058254128581420474871373)
            ·
              refine ⟨54396845298218032678076765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145058254128581420474871373 54396845298218032678076765)
              ·
                refine ⟨20398816986831762254278787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54396845298218032678076765 20398816986831762254278787)
                ·
                  refine ⟨30598225480247643381418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398816986831762254278787 30598225480247643381418181)
                  ·
                    refine ⟨5737167277546433134015909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30598225480247643381418181 5737167277546433134015909)
                    ·
                      refine ⟨1075718864539956212627983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5737167277546433134015909 1075718864539956212627983)
                      ·
                        rfl

theorem cell23_2094955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_2094955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094955 prefixEnd_2094955 := by exact prefixLift 2094955
  have htrace : WordTrace (prefixWord ++ tailWord_2094955) baseStart_2094955 baseEnd_2094955 := by
    simpa [prefixWord, tailWord_2094955, baseEnd_2094955] using wordTrace_append hprefix tailTrace_2094955
  have hstable : (prefixWord ++ tailWord_2094955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094955).length < 2 ^ (prefixWord ++ tailWord_2094955).sum := by decide
  have hdescent : baseEnd_2094955 < baseStart_2094955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094999 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 5]
def baseStart_2094999 : Nat := 118140960795 + 2094999 * 2 ^ 59
def prefixEnd_2094999 : Nat := 4983230072969 + 3 ^ 40 * 2094999 * 2
def baseEnd_2094999 : Nat := 119526828632083782275309

theorem tailTrace_2094999 : CollatzResearch.WordTrace tailWord_2094999 prefixEnd_2094999 119526828632083782275309 := by
  unfold tailWord_2094999
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410890937183895188608051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50940593958122596792405367 76410890937183895188608051)
  ·
    refine ⟨114616336405775842782912077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76410890937183895188608051 114616336405775842782912077)
    ·
      refine ⟨42981126152165941043592029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114616336405775842782912077 42981126152165941043592029)
      ·
        refine ⟨16117922307062227891347011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42981126152165941043592029 16117922307062227891347011)
        ·
          refine ⟨24176883460593341837020517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16117922307062227891347011 24176883460593341837020517)
          ·
            refine ⟨4533165648861251594441347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24176883460593341837020517 4533165648861251594441347)
            ·
              refine ⟨6799748473291877391662021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533165648861251594441347 6799748473291877391662021)
              ·
                refine ⟨1274952838742227010936629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6799748473291877391662021 1274952838742227010936629)
                ·
                  refine ⟨119526828632083782275309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274952838742227010936629 119526828632083782275309)
                  ·
                    rfl

theorem cell23_2094999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 5].length) (baseStart_2094999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094999 prefixEnd_2094999 := by exact prefixLift 2094999
  have htrace : WordTrace (prefixWord ++ tailWord_2094999) baseStart_2094999 baseEnd_2094999 := by
    simpa [prefixWord, tailWord_2094999, baseEnd_2094999] using wordTrace_append hprefix tailTrace_2094999
  have hstable : (prefixWord ++ tailWord_2094999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094999).length < 2 ^ (prefixWord ++ tailWord_2094999).sum := by decide
  have hdescent : baseEnd_2094999 < baseStart_2094999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095016 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 7]
def baseStart_2095016 : Nat := 118140960795 + 2095016 * 2 ^ 59
def prefixEnd_2095016 : Nat := 4983230072969 + 3 ^ 40 * 2095016 * 2
def baseEnd_2095016 : Nat := 119527798539986719329467

theorem tailTrace_2095016 : CollatzResearch.WordTrace tailWord_2095016 prefixEnd_2095016 119527798539986719329467 := by
  unfold tailWord_2095016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38205755489061153545988451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50941007318748204727984601 38205755489061153545988451)
  ·
    refine ⟨57308633233591730318982677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38205755489061153545988451 57308633233591730318982677)
    ·
      refine ⟨2686342182824612358702313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57308633233591730318982677 2686342182824612358702313)
      ·
        refine ⟨2014756637118459269026735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686342182824612358702313 2014756637118459269026735)
        ·
          refine ⟨3022134955677688903540103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014756637118459269026735 3022134955677688903540103)
          ·
            refine ⟨4533202433516533355310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022134955677688903540103 4533202433516533355310155)
            ·
              refine ⟨6799803650274800032965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533202433516533355310155 6799803650274800032965233)
              ·
                refine ⟨5099852737706100024723925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799803650274800032965233 5099852737706100024723925)
                ·
                  refine ⟨119527798539986719329467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5099852737706100024723925 119527798539986719329467)
                  ·
                    rfl

theorem cell23_2095016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_2095016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095016 prefixEnd_2095016 := by exact prefixLift 2095016
  have htrace : WordTrace (prefixWord ++ tailWord_2095016) baseStart_2095016 baseEnd_2095016 := by
    simpa [prefixWord, tailWord_2095016, baseEnd_2095016] using wordTrace_append hprefix tailTrace_2095016
  have hstable : (prefixWord ++ tailWord_2095016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095016).length < 2 ^ (prefixWord ++ tailWord_2095016).sum := by decide
  have hdescent : baseEnd_2095016 < baseStart_2095016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095029 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2095029 : Nat := 118140960795 + 2095029 * 2 ^ 59
def prefixEnd_2095029 : Nat := 4983230072969 + 3 ^ 40 * 2095029 * 2
def baseEnd_2095029 : Nat := 358585620702796307700881

theorem tailTrace_2095029 : CollatzResearch.WordTrace tailWord_2095029 prefixEnd_2095029 358585620702796307700881 := by
  unfold tailWord_2095029
  simp only [CollatzResearch.WordTrace]
  refine ⟨76411985127075210312200141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50941323418050140208133427 76411985127075210312200141)
  ·
    refine ⟨28654494422653203867075053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76411985127075210312200141 28654494422653203867075053)
    ·
      refine ⟨10745435408494951450153145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28654494422653203867075053 10745435408494951450153145)
      ·
        refine ⟨8059076556371213587614859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10745435408494951450153145 8059076556371213587614859)
        ·
          refine ⟨12088614834556820381422289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059076556371213587614859 12088614834556820381422289)
          ·
            refine ⟨9066461125917615286066717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12088614834556820381422289 9066461125917615286066717)
            ·
              refine ⟨3399922922219105732275019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9066461125917615286066717 3399922922219105732275019)
              ·
                refine ⟨5099884383328658598412529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399922922219105732275019 5099884383328658598412529)
                ·
                  refine ⟨3824913287496493948809397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099884383328658598412529 3824913287496493948809397)
                  ·
                    refine ⟨358585620702796307700881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3824913287496493948809397 358585620702796307700881)
                    ·
                      rfl

theorem cell23_2095029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2095029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095029 prefixEnd_2095029 := by exact prefixLift 2095029
  have htrace : WordTrace (prefixWord ++ tailWord_2095029) baseStart_2095029 baseEnd_2095029 := by
    simpa [prefixWord, tailWord_2095029, baseEnd_2095029] using wordTrace_append hprefix tailTrace_2095029
  have hstable : (prefixWord ++ tailWord_2095029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095029).length < 2 ^ (prefixWord ++ tailWord_2095029).sum := by decide
  have hdescent : baseEnd_2095029 < baseStart_2095029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095032 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2095032 : Nat := 118140960795 + 2095032 * 2 ^ 59
def prefixEnd_2095032 : Nat := 4983230072969 + 3 ^ 40 * 2095032 * 2
def baseEnd_2095032 : Nat := 1075758402550352411365129

theorem tailTrace_2095032 : CollatzResearch.WordTrace tailWord_2095032 prefixEnd_2095032 1075758402550352411365129 := by
  unfold tailWord_2095032
  simp only [CollatzResearch.WordTrace]
  refine ⟨38206047273032170912279675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50941396364042894549706233 38206047273032170912279675)
  ·
    refine ⟨57309070909548256368419513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38206047273032170912279675 57309070909548256368419513)
    ·
      refine ⟨42981803182161192276314635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57309070909548256368419513 42981803182161192276314635)
      ·
        refine ⟨64472704773241788414471953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42981803182161192276314635 64472704773241788414471953)
        ·
          refine ⟨48354528579931341310853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64472704773241788414471953 48354528579931341310853965)
          ·
            refine ⟨18132948217474252991570237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48354528579931341310853965 18132948217474252991570237)
            ·
              refine ⟨6799855581552844871838839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18132948217474252991570237 6799855581552844871838839)
              ·
                refine ⟨10199783372329267307758259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799855581552844871838839 10199783372329267307758259)
                ·
                  refine ⟨15299675058493900961637389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199783372329267307758259 15299675058493900961637389)
                  ·
                    refine ⟨5737378146935212860614021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15299675058493900961637389 5737378146935212860614021)
                    ·
                      refine ⟨1075758402550352411365129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5737378146935212860614021 1075758402550352411365129)
                      ·
                        rfl

theorem cell23_2095032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2095032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095032 prefixEnd_2095032 := by exact prefixLift 2095032
  have htrace : WordTrace (prefixWord ++ tailWord_2095032) baseStart_2095032 baseEnd_2095032 := by
    simpa [prefixWord, tailWord_2095032, baseEnd_2095032] using wordTrace_append hprefix tailTrace_2095032
  have hstable : (prefixWord ++ tailWord_2095032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095032).length < 2 ^ (prefixWord ++ tailWord_2095032).sum := by decide
  have hdescent : baseEnd_2095032 < baseStart_2095032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095072 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 6]
def baseStart_2095072 : Nat := 118140960795 + 2095072 * 2 ^ 59
def prefixEnd_2095072 : Nat := 4983230072969 + 3 ^ 40 * 2095072 * 2
def baseEnd_2095072 : Nat := 119530993530725806096105

theorem tailTrace_2095072 : CollatzResearch.WordTrace tailWord_2095072 prefixEnd_2095072 119530993530725806096105 := by
  unfold tailWord_2095072
  simp only [CollatzResearch.WordTrace]
  refine ⟨38206776732959714328007735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50942368977279619104010313 38206776732959714328007735)
  ·
    refine ⟨57310165099439571492011603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38206776732959714328007735 57310165099439571492011603)
    ·
      refine ⟨85965247649159357238017405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57310165099439571492011603 85965247649159357238017405)
      ·
        refine ⟨32236967868434758964256527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85965247649159357238017405 32236967868434758964256527)
        ·
          refine ⟨48355451802652138446384791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32236967868434758964256527 48355451802652138446384791)
          ·
            refine ⟨72533177703978207669577187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48355451802652138446384791 72533177703978207669577187)
            ·
              refine ⟨108799766555967311504365781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72533177703978207669577187 108799766555967311504365781)
              ·
                refine ⟨2549994528655483863383573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108799766555967311504365781 2549994528655483863383573)
                ·
                  refine ⟨119530993530725806096105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2549994528655483863383573 119530993530725806096105)
                  ·
                    rfl

theorem cell23_2095072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_2095072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095072 prefixEnd_2095072 := by exact prefixLift 2095072
  have htrace : WordTrace (prefixWord ++ tailWord_2095072) baseStart_2095072 baseEnd_2095072 := by
    simpa [prefixWord, tailWord_2095072, baseEnd_2095072] using wordTrace_append hprefix tailTrace_2095072
  have hstable : (prefixWord ++ tailWord_2095072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095072).length < 2 ^ (prefixWord ++ tailWord_2095072).sum := by decide
  have hdescent : baseEnd_2095072 < baseStart_2095072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095099 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 3]
def baseStart_2095099 : Nat := 118140960795 + 2095099 * 2 ^ 59
def prefixEnd_2095099 : Nat := 4983230072969 + 3 ^ 40 * 2095099 * 2
def baseEnd_2095099 : Nat := 1075792805754203649227321

theorem tailTrace_2095099 : CollatzResearch.WordTrace tailWord_2095099 prefixEnd_2095099 1075792805754203649227321 := by
  unfold tailWord_2095099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76414538236821612267248351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50943025491214408178165567 76414538236821612267248351)
  ·
    refine ⟨114621807355232418400872527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76414538236821612267248351 114621807355232418400872527)
    ·
      refine ⟨171932711032848627601308791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114621807355232418400872527 171932711032848627601308791)
      ·
        refine ⟨257899066549272941401963187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171932711032848627601308791 257899066549272941401963187)
        ·
          refine ⟨386848599823909412102944781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257899066549272941401963187 386848599823909412102944781)
          ·
            refine ⟨145068224933966029538604293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386848599823909412102944781 145068224933966029538604293)
            ·
              refine ⟨27200292175118630538488305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145068224933966029538604293 27200292175118630538488305)
              ·
                refine ⟨20400219131338972903866229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27200292175118630538488305 20400219131338972903866229)
                ·
                  refine ⟨1912520543563028709737459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20400219131338972903866229 1912520543563028709737459)
                  ·
                    refine ⟨2868780815344543064606189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912520543563028709737459 2868780815344543064606189)
                    ·
                      refine ⟨1075792805754203649227321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868780815344543064606189 1075792805754203649227321)
                      ·
                        rfl

theorem cell23_2095099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 3].length) (baseStart_2095099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095099 prefixEnd_2095099 := by exact prefixLift 2095099
  have htrace : WordTrace (prefixWord ++ tailWord_2095099) baseStart_2095099 baseEnd_2095099 := by
    simpa [prefixWord, tailWord_2095099, baseEnd_2095099] using wordTrace_append hprefix tailTrace_2095099
  have hstable : (prefixWord ++ tailWord_2095099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095099).length < 2 ^ (prefixWord ++ tailWord_2095099).sum := by decide
  have hdescent : baseEnd_2095099 < baseStart_2095099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095139 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2095139 : Nat := 118140960795 + 2095139 * 2 ^ 59
def prefixEnd_2095139 : Nat := 4983230072969 + 3 ^ 40 * 2095139 * 2
def baseEnd_2095139 : Nat := 1075813344980383492727137

theorem tailTrace_2095139 : CollatzResearch.WordTrace tailWord_2095139 prefixEnd_2095139 1075813344980383492727137 := by
  unfold tailWord_2095139
  simp only [CollatzResearch.WordTrace]
  refine ⟨76415997156676699098704471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50943998104451132732469647 76415997156676699098704471)
  ·
    refine ⟨114623995735015048648056707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76415997156676699098704471 114623995735015048648056707)
    ·
      refine ⟨171935993602522572972085061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114623995735015048648056707 171935993602522572972085061)
      ·
        refine ⟨32237998800472982432265949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171935993602522572972085061 32237998800472982432265949)
        ·
          refine ⟨12089249550177368412099731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32237998800472982432265949 12089249550177368412099731)
          ·
            refine ⟨18133874325266052618149597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089249550177368412099731 18133874325266052618149597)
            ·
              refine ⟨6800202871974769731806099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18133874325266052618149597 6800202871974769731806099)
              ·
                refine ⟨10200304307962154597709149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800202871974769731806099 10200304307962154597709149)
                ·
                  refine ⟨3825114115485807974140931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10200304307962154597709149 3825114115485807974140931)
                  ·
                    refine ⟨5737671173228711961211397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825114115485807974140931 5737671173228711961211397)
                    ·
                      refine ⟨1075813344980383492727137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5737671173228711961211397 1075813344980383492727137)
                      ·
                        rfl

theorem cell23_2095139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2095139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095139 prefixEnd_2095139 := by exact prefixLift 2095139
  have htrace : WordTrace (prefixWord ++ tailWord_2095139) baseStart_2095139 baseEnd_2095139 := by
    simpa [prefixWord, tailWord_2095139, baseEnd_2095139] using wordTrace_append hprefix tailTrace_2095139
  have hstable : (prefixWord ++ tailWord_2095139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095139).length < 2 ^ (prefixWord ++ tailWord_2095139).sum := by decide
  have hdescent : baseEnd_2095139 < baseStart_2095139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095159 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_2095159 : Nat := 118140960795 + 2095159 * 2 ^ 59
def prefixEnd_2095159 : Nat := 4983230072969 + 3 ^ 40 * 2095159 * 2
def baseEnd_2095159 : Nat := 1075823614593473414477045

theorem tailTrace_2095159 : CollatzResearch.WordTrace tailWord_2095159 prefixEnd_2095159 1075823614593473414477045 := by
  unfold tailWord_2095159
  simp only [CollatzResearch.WordTrace]
  refine ⟨76416726616604242514432531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50944484411069495009621687 76416726616604242514432531)
  ·
    refine ⟨114625089924906363771648797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76416726616604242514432531 114625089924906363771648797)
    ·
      refine ⟨42984408721839886414368299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114625089924906363771648797 42984408721839886414368299)
      ·
        refine ⟨64476613082759829621552449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42984408721839886414368299 64476613082759829621552449)
        ·
          refine ⟨48357459812069872216164337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64476613082759829621552449 48357459812069872216164337)
          ·
            refine ⟨36268094859052404162123253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48357459812069872216164337 36268094859052404162123253)
            ·
              refine ⟨3400133893036162890199055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36268094859052404162123253 3400133893036162890199055)
              ·
                refine ⟨5100200839554244335298583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400133893036162890199055 5100200839554244335298583)
                ·
                  refine ⟨7650301259331366502947875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100200839554244335298583 7650301259331366502947875)
                  ·
                    refine ⟨11475451888997049754421813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650301259331366502947875 11475451888997049754421813)
                    ·
                      refine ⟨1075823614593473414477045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11475451888997049754421813 1075823614593473414477045)
                      ·
                        rfl

theorem cell23_2095159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_2095159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095159 prefixEnd_2095159 := by exact prefixLift 2095159
  have htrace : WordTrace (prefixWord ++ tailWord_2095159) baseStart_2095159 baseEnd_2095159 := by
    simpa [prefixWord, tailWord_2095159, baseEnd_2095159] using wordTrace_append hprefix tailTrace_2095159
  have hstable : (prefixWord ++ tailWord_2095159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095159).length < 2 ^ (prefixWord ++ tailWord_2095159).sum := by decide
  have hdescent : baseEnd_2095159 < baseStart_2095159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095196 : List Nat := [2, 2, 4, 1, 1, 3, 3, 7]
def baseStart_2095196 : Nat := 118140960795 + 2095196 * 2 ^ 59
def prefixEnd_2095196 : Nat := 4983230072969 + 3 ^ 40 * 2095196 * 2
def baseEnd_2095196 : Nat := 39846022717692213693125

theorem tailTrace_2095196 : CollatzResearch.WordTrace tailWord_2095196 prefixEnd_2095196 39846022717692213693125 := by
  unfold tailWord_2095196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209038058735098916764721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50945384078313465222352961 38209038058735098916764721)
  ·
    refine ⟨28656778544051324187573541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38209038058735098916764721 28656778544051324187573541)
    ·
      refine ⟨5373145977009623285170039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28656778544051324187573541 5373145977009623285170039)
      ·
        refine ⟨8059718965514434927755059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373145977009623285170039 8059718965514434927755059)
        ·
          refine ⟨12089578448271652391632589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059718965514434927755059 12089578448271652391632589)
          ·
            refine ⟨4533591918101869646862221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12089578448271652391632589 4533591918101869646862221)
            ·
              refine ⟨1700096969288201117573333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4533591918101869646862221 1700096969288201117573333)
              ·
                refine ⟨39846022717692213693125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1700096969288201117573333 39846022717692213693125)
                ·
                  rfl

theorem cell23_2095196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 7].length) (baseStart_2095196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095196 prefixEnd_2095196 := by exact prefixLift 2095196
  have htrace : WordTrace (prefixWord ++ tailWord_2095196) baseStart_2095196 baseEnd_2095196 := by
    simpa [prefixWord, tailWord_2095196, baseEnd_2095196] using wordTrace_append hprefix tailTrace_2095196
  have hstable : (prefixWord ++ tailWord_2095196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095196).length < 2 ^ (prefixWord ++ tailWord_2095196).sum := by decide
  have hdescent : baseEnd_2095196 < baseStart_2095196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095223 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_2095223 : Nat := 118140960795 + 2095223 * 2 ^ 59
def prefixEnd_2095223 : Nat := 4983230072969 + 3 ^ 40 * 2095223 * 2
def baseEnd_2095223 : Nat := 1075856477355361164076751

theorem tailTrace_2095223 : CollatzResearch.WordTrace tailWord_2095223 prefixEnd_2095223 1075856477355361164076751 := by
  unfold tailWord_2095223
  simp only [CollatzResearch.WordTrace]
  refine ⟨76419060888372381444762323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50946040592248254296508215 76419060888372381444762323)
  ·
    refine ⟨114628591332558572167143485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76419060888372381444762323 114628591332558572167143485)
    ·
      refine ⟨42985721749709464562678807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114628591332558572167143485 42985721749709464562678807)
      ·
        refine ⟨64478582624564196844018211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42985721749709464562678807 64478582624564196844018211)
        ·
          refine ⟨96717873936846295266027317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64478582624564196844018211 96717873936846295266027317)
          ·
            refine ⟨9067300681579340181190061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96717873936846295266027317 9067300681579340181190061)
            ·
              refine ⟨3400237755592252567946273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067300681579340181190061 3400237755592252567946273)
              ·
                refine ⟨2550178316694189425959705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400237755592252567946273 2550178316694189425959705)
                ·
                  refine ⟨1912633737520642069469779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550178316694189425959705 1912633737520642069469779)
                  ·
                    refine ⟨2868950606280963104204669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912633737520642069469779 2868950606280963104204669)
                    ·
                      refine ⟨1075856477355361164076751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868950606280963104204669 1075856477355361164076751)
                      ·
                        rfl

theorem cell23_2095223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_2095223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095223 prefixEnd_2095223 := by exact prefixLift 2095223
  have htrace : WordTrace (prefixWord ++ tailWord_2095223) baseStart_2095223 baseEnd_2095223 := by
    simpa [prefixWord, tailWord_2095223, baseEnd_2095223] using wordTrace_append hprefix tailTrace_2095223
  have hstable : (prefixWord ++ tailWord_2095223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095223).length < 2 ^ (prefixWord ++ tailWord_2095223).sum := by decide
  have hdescent : baseEnd_2095223 < baseStart_2095223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095239 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2095239 : Nat := 118140960795 + 2095239 * 2 ^ 59
def prefixEnd_2095239 : Nat := 4983230072969 + 3 ^ 40 * 2095239 * 2
def baseEnd_2095239 : Nat := 358621564348611033825559

theorem tailTrace_2095239 : CollatzResearch.WordTrace tailWord_2095239 prefixEnd_2095239 358621564348611033825559 := by
  unfold tailWord_2095239
  simp only [CollatzResearch.WordTrace]
  refine ⟨76419644456314416177344771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50946429637542944118229847 76419644456314416177344771)
  ·
    refine ⟨114629466684471624266017157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76419644456314416177344771 114629466684471624266017157)
    ·
      refine ⟨21493025003338429549878217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114629466684471624266017157 21493025003338429549878217)
      ·
        refine ⟨16119768752503822162408663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21493025003338429549878217 16119768752503822162408663)
        ·
          refine ⟨24179653128755733243612995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16119768752503822162408663 24179653128755733243612995)
          ·
            refine ⟨36269479693133599865419493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24179653128755733243612995 36269479693133599865419493)
            ·
              refine ⟨6800527442462549974766155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36269479693133599865419493 6800527442462549974766155)
              ·
                refine ⟨10200791163693824962149233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800527442462549974766155 10200791163693824962149233)
                ·
                  refine ⟨7650593372770368721611925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200791163693824962149233 7650593372770368721611925)
                  ·
                    refine ⟨358621564348611033825559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7650593372770368721611925 358621564348611033825559)
                    ·
                      rfl

theorem cell23_2095239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2095239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095239 prefixEnd_2095239 := by exact prefixLift 2095239
  have htrace : WordTrace (prefixWord ++ tailWord_2095239) baseStart_2095239 baseEnd_2095239 := by
    simpa [prefixWord, tailWord_2095239, baseEnd_2095239] using wordTrace_append hprefix tailTrace_2095239
  have hstable : (prefixWord ++ tailWord_2095239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095239).length < 2 ^ (prefixWord ++ tailWord_2095239).sum := by decide
  have hdescent : baseEnd_2095239 < baseStart_2095239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095250 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2095250 : Nat := 118140960795 + 2095250 * 2 ^ 59
def prefixEnd_2095250 : Nat := 4983230072969 + 3 ^ 40 * 2095250 * 2
def baseEnd_2095250 : Nat := 1075870341333032558439127

theorem tailTrace_2095250 : CollatzResearch.WordTrace tailWord_2095250 prefixEnd_2095250 1075870341333032558439127 := by
  unfold tailWord_2095250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19105011414818641263998801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50946697106183043370663469 19105011414818641263998801)
  ·
    refine ⟨14328758561113980947999101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19105011414818641263998801 14328758561113980947999101)
    ·
      refine ⟨5373284460417742855499663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14328758561113980947999101 5373284460417742855499663)
      ·
        refine ⟨8059926690626614283249495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373284460417742855499663 8059926690626614283249495)
        ·
          refine ⟨12089890035939921424874243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059926690626614283249495 12089890035939921424874243)
          ·
            refine ⟨18134835053909882137311365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089890035939921424874243 18134835053909882137311365)
            ·
              refine ⟨3400281572608102900745881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18134835053909882137311365 3400281572608102900745881)
              ·
                refine ⟨2550211179456077175559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400281572608102900745881 2550211179456077175559411)
                ·
                  refine ⟨3825316769184115763339117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550211179456077175559411 3825316769184115763339117)
                  ·
                    refine ⟨1434493788444043411252169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825316769184115763339117 1434493788444043411252169)
                    ·
                      refine ⟨1075870341333032558439127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434493788444043411252169 1075870341333032558439127)
                      ·
                        rfl

theorem cell23_2095250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2095250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095250 prefixEnd_2095250 := by exact prefixLift 2095250
  have htrace : WordTrace (prefixWord ++ tailWord_2095250) baseStart_2095250 baseEnd_2095250 := by
    simpa [prefixWord, tailWord_2095250, baseEnd_2095250] using wordTrace_append hprefix tailTrace_2095250
  have hstable : (prefixWord ++ tailWord_2095250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095250).length < 2 ^ (prefixWord ++ tailWord_2095250).sum := by decide
  have hdescent : baseEnd_2095250 < baseStart_2095250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095266 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2095266 : Nat := 118140960795 + 2095266 * 2 ^ 59
def prefixEnd_2095266 : Nat := 4983230072969 + 3 ^ 40 * 2095266 * 2
def baseEnd_2095266 : Nat := 1075878557023504495839053

theorem tailTrace_2095266 : CollatzResearch.WordTrace tailWord_2095266 prefixEnd_2095266 1075878557023504495839053 := by
  unfold tailWord_2095266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19105157306804149947144413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50947086151477733192385101 19105157306804149947144413)
  ·
    refine ⟨7164433990051556230179155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19105157306804149947144413 7164433990051556230179155)
    ·
      refine ⟨10746650985077334345268733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7164433990051556230179155 10746650985077334345268733)
      ·
        refine ⟨4029994119404000379475775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10746650985077334345268733 4029994119404000379475775)
        ·
          refine ⟨6044991179106000569213663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029994119404000379475775 6044991179106000569213663)
          ·
            refine ⟨9067486768659000853820495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044991179106000569213663 9067486768659000853820495)
            ·
              refine ⟨13601230152988501280730743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067486768659000853820495 13601230152988501280730743)
              ·
                refine ⟨20401845229482751921096115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13601230152988501280730743 20401845229482751921096115)
                ·
                  refine ⟨30602767844224127881644173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20401845229482751921096115 30602767844224127881644173)
                  ·
                    refine ⟨11476037941584047955616565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30602767844224127881644173 11476037941584047955616565)
                    ·
                      refine ⟨1075878557023504495839053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11476037941584047955616565 1075878557023504495839053)
                      ·
                        rfl

theorem cell23_2095266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2095266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095266 prefixEnd_2095266 := by exact prefixLift 2095266
  have htrace : WordTrace (prefixWord ++ tailWord_2095266) baseStart_2095266 baseEnd_2095266 := by
    simpa [prefixWord, tailWord_2095266, baseEnd_2095266] using wordTrace_append hprefix tailTrace_2095266
  have hstable : (prefixWord ++ tailWord_2095266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095266).length < 2 ^ (prefixWord ++ tailWord_2095266).sum := by decide
  have hdescent : baseEnd_2095266 < baseStart_2095266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095339 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_2095339 : Nat := 118140960795 + 2095339 * 2 ^ 59
def prefixEnd_2095339 : Nat := 4983230072969 + 3 ^ 40 * 2095339 * 2
def baseEnd_2095339 : Nat := 1075916041111282710226217

theorem tailTrace_2095339 : CollatzResearch.WordTrace tailWord_2095339 prefixEnd_2095339 1075916041111282710226217 := by
  unfold tailWord_2095339
  simp only [CollatzResearch.WordTrace]
  refine ⟨76423291755952133255985071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50948861170634755503990047 76423291755952133255985071)
  ·
    refine ⟨114634937633928199883977607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76423291755952133255985071 114634937633928199883977607)
    ·
      refine ⟨171952406450892299825966411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114634937633928199883977607 171952406450892299825966411)
      ·
        refine ⟨257928609676338449738949617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171952406450892299825966411 257928609676338449738949617)
        ·
          refine ⟨193446457257253837304212213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257928609676338449738949617 193446457257253837304212213)
          ·
            refine ⟨18135605367867547247269895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193446457257253837304212213 18135605367867547247269895)
            ·
              refine ⟨27203408051801320870904843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135605367867547247269895 27203408051801320870904843)
              ·
                refine ⟨40805112077701981306357265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27203408051801320870904843 40805112077701981306357265)
                ·
                  refine ⟨30603834058276485979767949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40805112077701981306357265 30603834058276485979767949)
                  ·
                    refine ⟨11476437771853682242412981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30603834058276485979767949 11476437771853682242412981)
                    ·
                      refine ⟨1075916041111282710226217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11476437771853682242412981 1075916041111282710226217)
                      ·
                        rfl

theorem cell23_2095339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_2095339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095339 prefixEnd_2095339 := by exact prefixLift 2095339
  have htrace : WordTrace (prefixWord ++ tailWord_2095339) baseStart_2095339 baseEnd_2095339 := by
    simpa [prefixWord, tailWord_2095339, baseEnd_2095339] using wordTrace_append hprefix tailTrace_2095339
  have hstable : (prefixWord ++ tailWord_2095339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095339).length < 2 ^ (prefixWord ++ tailWord_2095339).sum := by decide
  have hdescent : baseEnd_2095339 < baseStart_2095339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095367 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 2, 5]
def baseStart_2095367 : Nat := 118140960795 + 2095367 * 2 ^ 59
def prefixEnd_2095367 : Nat := 4983230072969 + 3 ^ 40 * 2095367 * 2
def baseEnd_2095367 : Nat := 358643472856536200225363

theorem tailTrace_2095367 : CollatzResearch.WordTrace tailWord_2095367 prefixEnd_2095367 358643472856536200225363 := by
  unfold tailWord_2095367
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424312999850694038004355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50949541999900462692002903 76424312999850694038004355)
  ·
    refine ⟨114636469499776041057006533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76424312999850694038004355 114636469499776041057006533)
    ·
      refine ⟨21494338031208007698188725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114636469499776041057006533 21494338031208007698188725)
      ·
        refine ⟨2015094190425750721705193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21494338031208007698188725 2015094190425750721705193)
        ·
          refine ⟨1511320642819313041278895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015094190425750721705193 1511320642819313041278895)
          ·
            refine ⟨2266980964228969561918343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511320642819313041278895 2266980964228969561918343)
            ·
              refine ⟨3400471446343454342877515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266980964228969561918343 3400471446343454342877515)
              ·
                refine ⟨5100707169515181514316273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400471446343454342877515 5100707169515181514316273)
                ·
                  refine ⟨3825530377136386135737205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100707169515181514316273 3825530377136386135737205)
                  ·
                    refine ⟨358643472856536200225363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825530377136386135737205 358643472856536200225363)
                    ·
                      rfl

theorem cell23_2095367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_2095367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095367 prefixEnd_2095367 := by exact prefixLift 2095367
  have htrace : WordTrace (prefixWord ++ tailWord_2095367) baseStart_2095367 baseEnd_2095367 := by
    simpa [prefixWord, tailWord_2095367, baseEnd_2095367] using wordTrace_append hprefix tailTrace_2095367
  have hstable : (prefixWord ++ tailWord_2095367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095367).length < 2 ^ (prefixWord ++ tailWord_2095367).sum := by decide
  have hdescent : baseEnd_2095367 < baseStart_2095367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_2095379 : Nat := 118140960795 + 2095379 * 2 ^ 59
def prefixEnd_2095379 : Nat := 4983230072969 + 3 ^ 40 * 2095379 * 2
def baseEnd_2095379 : Nat := 1075936580337462553726033

theorem tailTrace_2095379 : CollatzResearch.WordTrace tailWord_2095379 prefixEnd_2095379 1075936580337462553726033 := by
  unfold tailWord_2095379
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424750675807220087441191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50949833783871480058294127 76424750675807220087441191)
  ·
    refine ⟨114637126013710830131161787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76424750675807220087441191 114637126013710830131161787)
    ·
      refine ⟨171955689020566245196742681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114637126013710830131161787 171955689020566245196742681)
      ·
        refine ⟨128966766765424683897557011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171955689020566245196742681 128966766765424683897557011)
        ·
          refine ⟨193450150148137025846335517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128966766765424683897557011 193450150148137025846335517)
          ·
            refine ⟨72543806305551384692375819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193450150148137025846335517 72543806305551384692375819)
            ·
              refine ⟨108815709458327077038563729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72543806305551384692375819 108815709458327077038563729)
              ·
                refine ⟨81611782093745307778922797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108815709458327077038563729 81611782093745307778922797)
                ·
                  refine ⟨30604418285154490417096049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81611782093745307778922797 30604418285154490417096049)
                  ·
                    refine ⟨22953313713865867812822037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30604418285154490417096049 22953313713865867812822037)
                    ·
                      refine ⟨1075936580337462553726033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22953313713865867812822037 1075936580337462553726033)
                      ·
                        rfl

theorem cell23_2095379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_2095379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095379 prefixEnd_2095379 := by exact prefixLift 2095379
  have htrace : WordTrace (prefixWord ++ tailWord_2095379) baseStart_2095379 baseEnd_2095379 := by
    simpa [prefixWord, tailWord_2095379, baseEnd_2095379] using wordTrace_append hprefix tailTrace_2095379
  have hstable : (prefixWord ++ tailWord_2095379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095379).length < 2 ^ (prefixWord ++ tailWord_2095379).sum := by decide
  have hdescent : baseEnd_2095379 < baseStart_2095379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095396 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2095396 : Nat := 118140960795 + 2095396 * 2 ^ 59
def prefixEnd_2095396 : Nat := 4983230072969 + 3 ^ 40 * 2095396 * 2
def baseEnd_2095396 : Nat := 1075945309508588987213455

theorem tailTrace_2095396 : CollatzResearch.WordTrace tailWord_2095396 prefixEnd_2095396 1075945309508588987213455 := by
  unfold tailWord_2095396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38212685358372815995405021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50950247144497087993873361 38212685358372815995405021)
  ·
    refine ⟨14329757009389805998276883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38212685358372815995405021 14329757009389805998276883)
    ·
      refine ⟨21494635514084708997415325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329757009389805998276883 21494635514084708997415325)
      ·
        refine ⟨8060488317781765874030747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21494635514084708997415325 8060488317781765874030747)
        ·
          refine ⟨12090732476672648811046121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060488317781765874030747 12090732476672648811046121)
          ·
            refine ⟨9068049357504486608284591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090732476672648811046121 9068049357504486608284591)
            ·
              refine ⟨13602074036256729912426887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068049357504486608284591 13602074036256729912426887)
              ·
                refine ⟨20403111054385094868640331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602074036256729912426887 20403111054385094868640331)
                ·
                  refine ⟨30604666581577642302960497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20403111054385094868640331 30604666581577642302960497)
                  ·
                    refine ⟨22953499936183231727220373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30604666581577642302960497 22953499936183231727220373)
                    ·
                      refine ⟨1075945309508588987213455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22953499936183231727220373 1075945309508588987213455)
                      ·
                        rfl

theorem cell23_2095396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2095396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095396 prefixEnd_2095396 := by exact prefixLift 2095396
  have htrace : WordTrace (prefixWord ++ tailWord_2095396) baseStart_2095396 baseEnd_2095396 := by
    simpa [prefixWord, tailWord_2095396, baseEnd_2095396] using wordTrace_append hprefix tailTrace_2095396
  have hstable : (prefixWord ++ tailWord_2095396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095396).length < 2 ^ (prefixWord ++ tailWord_2095396).sum := by decide
  have hdescent : baseEnd_2095396 < baseStart_2095396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095410 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_2095410 : Nat := 118140960795 + 2095410 * 2 ^ 59
def prefixEnd_2095410 : Nat := 4983230072969 + 3 ^ 40 * 2095410 * 2
def baseEnd_2095410 : Nat := 119550277581972436937599

theorem tailTrace_2095410 : CollatzResearch.WordTrace tailWord_2095410 prefixEnd_2095410 119550277581972436937599 := by
  unfold tailWord_2095410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106470334673728095454921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50950587559129941587879789 19106470334673728095454921)
  ·
    refine ⟨14329852751005296071591191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19106470334673728095454921 14329852751005296071591191)
    ·
      refine ⟨21494779126507944107386787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329852751005296071591191 21494779126507944107386787)
      ·
        refine ⟨32242168689761916161080181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21494779126507944107386787 32242168689761916161080181)
        ·
          refine ⟨3022703314665179640101267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32242168689761916161080181 3022703314665179640101267)
          ·
            refine ⟨4534054971997769460151901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022703314665179640101267 4534054971997769460151901)
            ·
              refine ⟨1700270614499163547556963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4534054971997769460151901 1700270614499163547556963)
              ·
                refine ⟨2550405921748745321335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700270614499163547556963 2550405921748745321335445)
                ·
                  refine ⟨119550277581972436937599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2550405921748745321335445 119550277581972436937599)
                  ·
                    rfl

theorem cell23_2095410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_2095410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095410 prefixEnd_2095410 := by exact prefixLift 2095410
  have htrace : WordTrace (prefixWord ++ tailWord_2095410) baseStart_2095410 baseEnd_2095410 := by
    simpa [prefixWord, tailWord_2095410, baseEnd_2095410] using wordTrace_append hprefix tailTrace_2095410
  have hstable : (prefixWord ++ tailWord_2095410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095410).length < 2 ^ (prefixWord ++ tailWord_2095410).sum := by decide
  have hdescent : baseEnd_2095410 < baseStart_2095410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095413 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_2095413 : Nat := 118140960795 + 2095413 * 2 ^ 59
def prefixEnd_2095413 : Nat := 4983230072969 + 3 ^ 40 * 2095413 * 2
def baseEnd_2095413 : Nat := 1075954038679715420700877

theorem tailTrace_2095413 : CollatzResearch.WordTrace tailWord_2095413 prefixEnd_2095413 1075954038679715420700877 := by
  unfold tailWord_2095413
  simp only [CollatzResearch.WordTrace]
  refine ⟨76425990757684043894178893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50950660505122695929452595 76425990757684043894178893)
  ·
    refine ⟨28659746534131516460317085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76425990757684043894178893 28659746534131516460317085)
    ·
      refine ⟨10747404950299318672618907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28659746534131516460317085 10747404950299318672618907)
      ·
        refine ⟨16121107425448978008928361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747404950299318672618907 16121107425448978008928361)
        ·
          refine ⟨12090830569086733506696271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16121107425448978008928361 12090830569086733506696271)
          ·
            refine ⟨18136245853630100260044407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090830569086733506696271 18136245853630100260044407)
            ·
              refine ⟨27204368780445150390066611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18136245853630100260044407 27204368780445150390066611)
              ·
                refine ⟨40806553170667725585099917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27204368780445150390066611 40806553170667725585099917)
                ·
                  refine ⟨15302457439000397094412469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40806553170667725585099917 15302457439000397094412469)
                  ·
                    refine ⟨1434605384906287227601169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15302457439000397094412469 1434605384906287227601169)
                    ·
                      refine ⟨1075954038679715420700877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434605384906287227601169 1075954038679715420700877)
                      ·
                        rfl

theorem cell23_2095413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_2095413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095413 prefixEnd_2095413 := by exact prefixLift 2095413
  have htrace : WordTrace (prefixWord ++ tailWord_2095413) baseStart_2095413 baseEnd_2095413 := by
    simpa [prefixWord, tailWord_2095413, baseEnd_2095413] using wordTrace_append hprefix tailTrace_2095413
  have hstable : (prefixWord ++ tailWord_2095413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095413).length < 2 ^ (prefixWord ++ tailWord_2095413).sum := by decide
  have hdescent : baseEnd_2095413 < baseStart_2095413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095423 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 1, 5]
def baseStart_2095423 : Nat := 118140960795 + 2095423 * 2 ^ 59
def prefixEnd_2095423 : Nat := 4983230072969 + 3 ^ 40 * 2095423 * 2
def baseEnd_2095423 : Nat := 358653057828753460525277

theorem tailTrace_2095423 : CollatzResearch.WordTrace tailWord_2095423 prefixEnd_2095423 358653057828753460525277 := by
  unfold tailWord_2095423
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426355487647815602042923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50950903658431877068028615 76426355487647815602042923)
  ·
    refine ⟨114639533231471723403064385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76426355487647815602042923 114639533231471723403064385)
    ·
      refine ⟨85979649923603792552298289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114639533231471723403064385 85979649923603792552298289)
      ·
        refine ⟨64484737442702844414223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85979649923603792552298289 64484737442702844414223717)
        ·
          refine ⟨12090888270506783327666947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64484737442702844414223717 12090888270506783327666947)
          ·
            refine ⟨18136332405760174991500421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090888270506783327666947 18136332405760174991500421)
            ·
              refine ⟨3400562326080032810906329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18136332405760174991500421 3400562326080032810906329)
              ·
                refine ⟨2550421744560024608179747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400562326080032810906329 2550421744560024608179747)
                ·
                  refine ⟨3825632616840036912269621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550421744560024608179747 3825632616840036912269621)
                  ·
                    refine ⟨358653057828753460525277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825632616840036912269621 358653057828753460525277)
                    ·
                      rfl

theorem cell23_2095423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_2095423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095423 prefixEnd_2095423 := by exact prefixLift 2095423
  have htrace : WordTrace (prefixWord ++ tailWord_2095423) baseStart_2095423 baseEnd_2095423 := by
    simpa [prefixWord, tailWord_2095423, baseEnd_2095423] using wordTrace_append hprefix tailTrace_2095423
  have hstable : (prefixWord ++ tailWord_2095423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095423).length < 2 ^ (prefixWord ++ tailWord_2095423).sum := by decide
  have hdescent : baseEnd_2095423 < baseStart_2095423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095436 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_2095436 : Nat := 118140960795 + 2095436 * 2 ^ 59
def prefixEnd_2095436 : Nat := 4983230072969 + 3 ^ 40 * 2095436 * 2
def baseEnd_2095436 : Nat := 358655282911589610237757

theorem tailTrace_2095436 : CollatzResearch.WordTrace tailWord_2095436 prefixEnd_2095436 358655282911589610237757 := by
  unfold tailWord_2095436
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213414818300359411133081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50951219757733812548177441 38213414818300359411133081)
  ·
    refine ⟨28660061113725269558349811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38213414818300359411133081 28660061113725269558349811)
    ·
      refine ⟨42990091670587904337524717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28660061113725269558349811 42990091670587904337524717)
      ·
        refine ⟨16121284376470464126571769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42990091670587904337524717 16121284376470464126571769)
        ·
          refine ⟨12090963282352848094928827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16121284376470464126571769 12090963282352848094928827)
          ·
            refine ⟨18136444923529272142393241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090963282352848094928827 18136444923529272142393241)
            ·
              refine ⟨13602333692646954106794931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18136444923529272142393241 13602333692646954106794931)
              ·
                refine ⟨20403500538970431160192397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602333692646954106794931 20403500538970431160192397)
                ·
                  refine ⟨7651312702113911685072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20403500538970431160192397 7651312702113911685072149)
                  ·
                    refine ⟨358655282911589610237757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7651312702113911685072149 358655282911589610237757)
                    ·
                      rfl

theorem cell23_2095436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_2095436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095436 prefixEnd_2095436 := by exact prefixLift 2095436
  have htrace : WordTrace (prefixWord ++ tailWord_2095436) baseStart_2095436 baseEnd_2095436 := by
    simpa [prefixWord, tailWord_2095436, baseEnd_2095436] using wordTrace_append hprefix tailTrace_2095436
  have hstable : (prefixWord ++ tailWord_2095436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095436).length < 2 ^ (prefixWord ++ tailWord_2095436).sum := by decide
  have hdescent : baseEnd_2095436 < baseStart_2095436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095463 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2095463 : Nat := 118140960795 + 2095463 * 2 ^ 59
def prefixEnd_2095463 : Nat := 4983230072969 + 3 ^ 40 * 2095463 * 2
def baseEnd_2095463 : Nat := 1075979712712440225075647

theorem tailTrace_2095463 : CollatzResearch.WordTrace tailWord_2095463 prefixEnd_2095463 1075979712712440225075647 := by
  unfold tailWord_2095463
  simp only [CollatzResearch.WordTrace]
  refine ⟨76427814407502902433499043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50951876271668601622332695 76427814407502902433499043)
  ·
    refine ⟨114641721611254353650248565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76427814407502902433499043 114641721611254353650248565)
    ·
      refine ⟨10747661401055095654710803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114641721611254353650248565 10747661401055095654710803)
      ·
        refine ⟨16121492101582643482066205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747661401055095654710803 16121492101582643482066205)
        ·
          refine ⟨6045559538093491305774827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16121492101582643482066205 6045559538093491305774827)
          ·
            refine ⟨9068339307140236958662241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045559538093491305774827 9068339307140236958662241)
            ·
              refine ⟨6801254480355177718996681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068339307140236958662241 6801254480355177718996681)
              ·
                refine ⟨5100940860266383289247511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801254480355177718996681 5100940860266383289247511)
                ·
                  refine ⟨7651411290399574933871267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100940860266383289247511 7651411290399574933871267)
                  ·
                    refine ⟨11477116935599362400806901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651411290399574933871267 11477116935599362400806901)
                    ·
                      refine ⟨1075979712712440225075647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11477116935599362400806901 1075979712712440225075647)
                      ·
                        rfl

theorem cell23_2095463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2095463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095463 prefixEnd_2095463 := by exact prefixLift 2095463
  have htrace : WordTrace (prefixWord ++ tailWord_2095463) baseStart_2095463 baseEnd_2095463 := by
    simpa [prefixWord, tailWord_2095463, baseEnd_2095463] using wordTrace_append hprefix tailTrace_2095463
  have hstable : (prefixWord ++ tailWord_2095463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095463).length < 2 ^ (prefixWord ++ tailWord_2095463).sum := by decide
  have hdescent : baseEnd_2095463 < baseStart_2095463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095477 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2095477 : Nat := 118140960795 + 2095477 * 2 ^ 59
def prefixEnd_2095477 : Nat := 4983230072969 + 3 ^ 40 * 2095477 * 2
def baseEnd_2095477 : Nat := 1075986901441603170300583

theorem tailTrace_2095477 : CollatzResearch.WordTrace tailWord_2095477 prefixEnd_2095477 1075986901441603170300583 := by
  unfold tailWord_2095477
  simp only [CollatzResearch.WordTrace]
  refine ⟨76428325029452182824508685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50952216686301455216339123 76428325029452182824508685)
  ·
    refine ⟨28660621886044568559190757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76428325029452182824508685 28660621886044568559190757)
    ·
      refine ⟨5373866603633356604848267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28660621886044568559190757 5373866603633356604848267)
      ·
        refine ⟨8060799905450034907272401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373866603633356604848267 8060799905450034907272401)
        ·
          refine ⟨6045599929087526180454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060799905450034907272401 6045599929087526180454301)
          ·
            refine ⟨2267099973407822317670363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6045599929087526180454301 2267099973407822317670363)
            ·
              refine ⟨3400649960111733476505545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267099973407822317670363 3400649960111733476505545)
              ·
                refine ⟨2550487470083800107379159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400649960111733476505545 2550487470083800107379159)
                ·
                  refine ⟨3825731205125700161068739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550487470083800107379159 3825731205125700161068739)
                  ·
                    refine ⟨5738596807688550241603109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825731205125700161068739 5738596807688550241603109)
                    ·
                      refine ⟨1075986901441603170300583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5738596807688550241603109 1075986901441603170300583)
                      ·
                        rfl

theorem cell23_2095477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2095477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095477 prefixEnd_2095477 := by exact prefixLift 2095477
  have htrace : WordTrace (prefixWord ++ tailWord_2095477) baseStart_2095477 baseEnd_2095477 := by
    simpa [prefixWord, tailWord_2095477, baseEnd_2095477] using wordTrace_append hprefix tailTrace_2095477
  have hstable : (prefixWord ++ tailWord_2095477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095477).length < 2 ^ (prefixWord ++ tailWord_2095477).sum := by decide
  have hdescent : baseEnd_2095477 < baseStart_2095477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095497 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 1, 2, 3]
def baseStart_2095497 : Nat := 118140960795 + 2095497 * 2 ^ 59
def prefixEnd_2095497 : Nat := 4983230072969 + 3 ^ 40 * 2095497 * 2
def baseEnd_2095497 : Nat := 1075997171054693092050491

theorem tailTrace_2095497 : CollatzResearch.WordTrace tailWord_2095497 prefixEnd_2095497 1075997171054693092050491 := by
  unfold tailWord_2095497
  simp only [CollatzResearch.WordTrace]
  refine ⟨76429054489379726240236745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50952702992919817493491163 76429054489379726240236745)
  ·
    refine ⟨57321790867034794680177559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76429054489379726240236745 57321790867034794680177559)
    ·
      refine ⟨85982686300552192020266339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57321790867034794680177559 85982686300552192020266339)
      ·
        refine ⟨128974029450828288030399509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85982686300552192020266339 128974029450828288030399509)
        ·
          refine ⟨6045657630507576001424977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128974029450828288030399509 6045657630507576001424977)
          ·
            refine ⟨4534243222880682001068733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6045657630507576001424977 4534243222880682001068733)
            ·
              refine ⟨1700341208580255750400775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4534243222880682001068733 1700341208580255750400775)
              ·
                refine ⟨2550511812870383625601163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700341208580255750400775 2550511812870383625601163)
                ·
                  refine ⟨3825767719305575438401745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550511812870383625601163 3825767719305575438401745)
                  ·
                    refine ⟨2869325789479181578801309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3825767719305575438401745 2869325789479181578801309)
                    ·
                      refine ⟨1075997171054693092050491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2869325789479181578801309 1075997171054693092050491)
                      ·
                        rfl

theorem cell23_2095497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 2, 3].length) (baseStart_2095497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095497 prefixEnd_2095497 := by exact prefixLift 2095497
  have htrace : WordTrace (prefixWord ++ tailWord_2095497) baseStart_2095497 baseEnd_2095497 := by
    simpa [prefixWord, tailWord_2095497, baseEnd_2095497] using wordTrace_append hprefix tailTrace_2095497
  have hstable : (prefixWord ++ tailWord_2095497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095497).length < 2 ^ (prefixWord ++ tailWord_2095497).sum := by decide
  have hdescent : baseEnd_2095497 < baseStart_2095497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095520 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2]
def baseStart_2095520 : Nat := 118140960795 + 2095520 * 2 ^ 59
def prefixEnd_2095520 : Nat := 4983230072969 + 3 ^ 40 * 2095520 * 2
def baseEnd_2095520 : Nat := 1076008981109746502062885

theorem tailTrace_2095520 : CollatzResearch.WordTrace tailWord_2095520 prefixEnd_2095520 1076008981109746502062885 := by
  unfold tailWord_2095520
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214946684148200584162007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50953262245530934112216009 38214946684148200584162007)
  ·
    refine ⟨57322420026222300876243011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38214946684148200584162007 57322420026222300876243011)
    ·
      refine ⟨85983630039333451314364517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57322420026222300876243011 85983630039333451314364517)
      ·
        refine ⟨16121930632375022121443347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85983630039333451314364517 16121930632375022121443347)
        ·
          refine ⟨24182895948562533182165021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121930632375022121443347 24182895948562533182165021)
          ·
            refine ⟨9068585980710949943311883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24182895948562533182165021 9068585980710949943311883)
            ·
              refine ⟨13602878971066424914967825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068585980710949943311883 13602878971066424914967825)
              ·
                refine ⟨10202159228299818686225869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602878971066424914967825 10202159228299818686225869)
                ·
                  refine ⟨3825809710612432007334701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10202159228299818686225869 3825809710612432007334701)
                  ·
                    refine ⟨1434678641479662002750513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825809710612432007334701 1434678641479662002750513)
                    ·
                      refine ⟨1076008981109746502062885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434678641479662002750513 1076008981109746502062885)
                      ·
                        rfl

theorem cell23_2095520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_2095520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095520 prefixEnd_2095520 := by exact prefixLift 2095520
  have htrace : WordTrace (prefixWord ++ tailWord_2095520) baseStart_2095520 baseEnd_2095520 := by
    simpa [prefixWord, tailWord_2095520, baseEnd_2095520] using wordTrace_append hprefix tailTrace_2095520
  have hstable : (prefixWord ++ tailWord_2095520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095520).length < 2 ^ (prefixWord ++ tailWord_2095520).sum := by decide
  have hdescent : baseEnd_2095520 < baseStart_2095520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095527 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2095527 : Nat := 118140960795 + 2095527 * 2 ^ 59
def prefixEnd_2095527 : Nat := 4983230072969 + 3 ^ 40 * 2095527 * 2
def baseEnd_2095527 : Nat := 1076012575474327974675353

theorem tailTrace_2095527 : CollatzResearch.WordTrace tailWord_2095527 prefixEnd_2095527 1076012575474327974675353 := by
  unfold tailWord_2095527
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430148679271041363828835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50953432452847360909219223 76430148679271041363828835)
  ·
    refine ⟨114645223018906562045743253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76430148679271041363828835 114645223018906562045743253)
    ·
      refine ⟨5373994829011245095894215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114645223018906562045743253 5373994829011245095894215)
      ·
        refine ⟨8060992243516867643841323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373994829011245095894215 8060992243516867643841323)
        ·
          refine ⟨12091488365275301465761985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060992243516867643841323 12091488365275301465761985)
          ·
            refine ⟨9068616273956476099321489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091488365275301465761985 9068616273956476099321489)
            ·
              refine ⟨6801462205467357074491117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068616273956476099321489 6801462205467357074491117)
              ·
                refine ⟨2550548327050258902934169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6801462205467357074491117 2550548327050258902934169)
                ·
                  refine ⟨1912911245287694177200627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550548327050258902934169 1912911245287694177200627)
                  ·
                    refine ⟨2869366867931541265800941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912911245287694177200627 2869366867931541265800941)
                    ·
                      refine ⟨1076012575474327974675353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2869366867931541265800941 1076012575474327974675353)
                      ·
                        rfl

theorem cell23_2095527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2095527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095527 prefixEnd_2095527 := by exact prefixLift 2095527
  have htrace : WordTrace (prefixWord ++ tailWord_2095527) baseStart_2095527 baseEnd_2095527 := by
    simpa [prefixWord, tailWord_2095527, baseEnd_2095527] using wordTrace_append hprefix tailTrace_2095527
  have hstable : (prefixWord ++ tailWord_2095527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095527).length < 2 ^ (prefixWord ++ tailWord_2095527).sum := by decide
  have hdescent : baseEnd_2095527 < baseStart_2095527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095573 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 7]
def baseStart_2095573 : Nat := 118140960795 + 2095573 * 2 ^ 59
def prefixEnd_2095573 : Nat := 4983230072969 + 3 ^ 40 * 2095573 * 2
def baseEnd_2095573 : Nat := 119559577287159421633349

theorem tailTrace_2095573 : CollatzResearch.WordTrace tailWord_2095573 prefixEnd_2095573 119559577287159421633349 := by
  unfold tailWord_2095573
  simp only [CollatzResearch.WordTrace]
  refine ⟨76431826437104391220003373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50954550958069594146668915 76431826437104391220003373)
  ·
    refine ⟨28661934913914146707501265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76431826437104391220003373 28661934913914146707501265)
    ·
      refine ⟨21496451185435610030625949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28661934913914146707501265 21496451185435610030625949)
      ·
        refine ⟨8061169194538353761484731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21496451185435610030625949 8061169194538353761484731)
        ·
          refine ⟨12091753791807530642227097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061169194538353761484731 12091753791807530642227097)
          ·
            refine ⟨9068815343855647981670323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091753791807530642227097 9068815343855647981670323)
            ·
              refine ⟨13603223015783471972505485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068815343855647981670323 13603223015783471972505485)
              ·
                refine ⟨5101208630918801989689557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13603223015783471972505485 5101208630918801989689557)
                ·
                  refine ⟨119559577287159421633349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5101208630918801989689557 119559577287159421633349)
                  ·
                    rfl

theorem cell23_2095573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_2095573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095573 prefixEnd_2095573 := by exact prefixLift 2095573
  have htrace : WordTrace (prefixWord ++ tailWord_2095573) baseStart_2095573 baseEnd_2095573 := by
    simpa [prefixWord, tailWord_2095573, baseEnd_2095573] using wordTrace_append hprefix tailTrace_2095573
  have hstable : (prefixWord ++ tailWord_2095573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095573).length < 2 ^ (prefixWord ++ tailWord_2095573).sum := by decide
  have hdescent : baseEnd_2095573 < baseStart_2095573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095584 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2]
def baseStart_2095584 : Nat := 118140960795 + 2095584 * 2 ^ 59
def prefixEnd_2095584 : Nat := 4983230072969 + 3 ^ 40 * 2095584 * 2
def baseEnd_2095584 : Nat := 1076041843871634251662591

theorem tailTrace_2095584 : CollatzResearch.WordTrace tailWord_2095584 prefixEnd_2095584 1076041843871634251662591 := by
  unfold tailWord_2095584
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216113820032270049326903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50954818426709693399102537 38216113820032270049326903)
  ·
    refine ⟨57324170730048405073990355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38216113820032270049326903 57324170730048405073990355)
    ·
      refine ⟨85986256095072607610985533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57324170730048405073990355 85986256095072607610985533)
      ·
        refine ⟨32244846035652227854119575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85986256095072607610985533 32244846035652227854119575)
        ·
          refine ⟨48367269053478341781179363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32244846035652227854119575 48367269053478341781179363)
          ·
            refine ⟨72550903580217512671769045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48367269053478341781179363 72550903580217512671769045)
            ·
              refine ⟨1700411802661347953244587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72550903580217512671769045 1700411802661347953244587)
              ·
                refine ⟨2550617703992021929866881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700411802661347953244587 2550617703992021929866881)
                ·
                  refine ⟨1912963277994016447400161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550617703992021929866881 1912963277994016447400161)
                  ·
                    refine ⟨1434722458495512335550121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912963277994016447400161 1434722458495512335550121)
                    ·
                      refine ⟨1076041843871634251662591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434722458495512335550121 1076041843871634251662591)
                      ·
                        rfl

theorem cell23_2095584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_2095584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095584 prefixEnd_2095584 := by exact prefixLift 2095584
  have htrace : WordTrace (prefixWord ++ tailWord_2095584) baseStart_2095584 baseEnd_2095584 := by
    simpa [prefixWord, tailWord_2095584, baseEnd_2095584] using wordTrace_append hprefix tailTrace_2095584
  have hstable : (prefixWord ++ tailWord_2095584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095584).length < 2 ^ (prefixWord ++ tailWord_2095584).sum := by decide
  have hdescent : baseEnd_2095584 < baseStart_2095584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095603 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 2, 5]
def baseStart_2095603 : Nat := 118140960795 + 2095603 * 2 ^ 59
def prefixEnd_2095603 : Nat := 4983230072969 + 3 ^ 40 * 2095603 * 2
def baseEnd_2095603 : Nat := 358683866668023225775001

theorem tailTrace_2095603 : CollatzResearch.WordTrace tailWord_2095603 prefixEnd_2095603 358683866668023225775001 := by
  unfold tailWord_2095603
  simp only [CollatzResearch.WordTrace]
  refine ⟨76432920626995706343595463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50955280417997137562396975 76432920626995706343595463)
  ·
    refine ⟨114649380940493559515393195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76432920626995706343595463 114649380940493559515393195)
    ·
      refine ⟨171974071410740339273089793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114649380940493559515393195 171974071410740339273089793)
      ·
        refine ⟨128980553558055254454817345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171974071410740339273089793 128980553558055254454817345)
        ·
          refine ⟨96735415168541440841113009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128980553558055254454817345 96735415168541440841113009)
          ·
            refine ⟨72551561376406080630834757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96735415168541440841113009 72551561376406080630834757)
            ·
              refine ⟨13603417758076140118281517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72551561376406080630834757 13603417758076140118281517)
              ·
                refine ⟨5101281659278552544355569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13603417758076140118281517 5101281659278552544355569)
                ·
                  refine ⟨3825961244458914408266677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101281659278552544355569 3825961244458914408266677)
                  ·
                    refine ⟨358683866668023225775001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825961244458914408266677 358683866668023225775001)
                    ·
                      rfl

theorem cell23_2095603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].length) (baseStart_2095603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095603 prefixEnd_2095603 := by exact prefixLift 2095603
  have htrace : WordTrace (prefixWord ++ tailWord_2095603) baseStart_2095603 baseEnd_2095603 := by
    simpa [prefixWord, tailWord_2095603, baseEnd_2095603] using wordTrace_append hprefix tailTrace_2095603
  have hstable : (prefixWord ++ tailWord_2095603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095603).length < 2 ^ (prefixWord ++ tailWord_2095603).sum := by decide
  have hdescent : baseEnd_2095603 < baseStart_2095603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095613 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2095613 : Nat := 118140960795 + 2095613 * 2 ^ 59
def prefixEnd_2095613 : Nat := 4983230072969 + 3 ^ 40 * 2095613 * 2
def baseEnd_2095613 : Nat := 1076056734810614638199957

theorem tailTrace_2095613 : CollatzResearch.WordTrace tailWord_2095613 prefixEnd_2095613 1076056734810614638199957 := by
  unfold tailWord_2095613
  simp only [CollatzResearch.WordTrace]
  refine ⟨76433285356959478051459493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50955523571306318700972995 76433285356959478051459493)
  ·
    refine ⟨14331241004429902134648655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76433285356959478051459493 14331241004429902134648655)
    ·
      refine ⟨21496861506644853201972983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331241004429902134648655 21496861506644853201972983)
      ·
        refine ⟨32245292259967279802959475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496861506644853201972983 32245292259967279802959475)
        ·
          refine ⟨48367938389950919704439213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32245292259967279802959475 48367938389950919704439213)
          ·
            refine ⟨18137976896231594889164705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48367938389950919704439213 18137976896231594889164705)
            ·
              refine ⟨13603482672173696166873529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18137976896231594889164705 13603482672173696166873529)
              ·
                refine ⟨10202612004130272125155147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13603482672173696166873529 10202612004130272125155147)
                ·
                  refine ⟨15303918006195408187732721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202612004130272125155147 15303918006195408187732721)
                  ·
                    refine ⟨11477938504646556140799541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15303918006195408187732721 11477938504646556140799541)
                    ·
                      refine ⟨1076056734810614638199957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11477938504646556140799541 1076056734810614638199957)
                      ·
                        rfl

theorem cell23_2095613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2095613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095613 prefixEnd_2095613 := by exact prefixLift 2095613
  have htrace : WordTrace (prefixWord ++ tailWord_2095613) baseStart_2095613 baseEnd_2095613 := by
    simpa [prefixWord, tailWord_2095613, baseEnd_2095613] using wordTrace_append hprefix tailTrace_2095613
  have hstable : (prefixWord ++ tailWord_2095613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095613).length < 2 ^ (prefixWord ++ tailWord_2095613).sum := by decide
  have hdescent : baseEnd_2095613 < baseStart_2095613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095620 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_2095620 : Nat := 118140960795 + 2095620 * 2 ^ 59
def prefixEnd_2095620 : Nat := 4983230072969 + 3 ^ 40 * 2095620 * 2
def baseEnd_2095620 : Nat := 358686776391732036937475

theorem tailTrace_2095620 : CollatzResearch.WordTrace tailWord_2095620 prefixEnd_2095620 358686776391732036937475 := by
  unfold tailWord_2095620
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216770333967059123482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50955693778622745497976209 38216770333967059123482157)
  ·
    refine ⟨14331288875237647171305809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38216770333967059123482157 14331288875237647171305809)
    ·
      refine ⟨10748466656428235378479357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14331288875237647171305809 10748466656428235378479357)
      ·
        refine ⟨4030674996160588266929759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10748466656428235378479357 4030674996160588266929759)
        ·
          refine ⟨6046012494240882400394639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030674996160588266929759 6046012494240882400394639)
          ·
            refine ⟨9069018741361323600591959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046012494240882400394639 9069018741361323600591959)
            ·
              refine ⟨13603528112041985400887939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069018741361323600591959 13603528112041985400887939)
              ·
                refine ⟨20405292168062978101331909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603528112041985400887939 20405292168062978101331909)
                ·
                  refine ⟨3825992281511808393999733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20405292168062978101331909 3825992281511808393999733)
                  ·
                    refine ⟨358686776391732036937475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825992281511808393999733 358686776391732036937475)
                    ·
                      rfl

theorem cell23_2095620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_2095620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095620 prefixEnd_2095620 := by exact prefixLift 2095620
  have htrace : WordTrace (prefixWord ++ tailWord_2095620) baseStart_2095620 baseEnd_2095620 := by
    simpa [prefixWord, tailWord_2095620, baseEnd_2095620] using wordTrace_append hprefix tailTrace_2095620
  have hstable : (prefixWord ++ tailWord_2095620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095620).length < 2 ^ (prefixWord ++ tailWord_2095620).sum := by decide
  have hdescent : baseEnd_2095620 < baseStart_2095620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095630 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2095630 : Nat := 118140960795 + 2095630 * 2 ^ 59
def prefixEnd_2095630 : Nat := 4983230072969 + 3 ^ 40 * 2095630 * 2
def baseEnd_2095630 : Nat := 1076065463981741071687379

theorem tailTrace_2095630 : CollatzResearch.WordTrace tailWord_2095630 prefixEnd_2095630 1076065463981741071687379 := by
  unfold tailWord_2095630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554238174737236244353543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50955936931931926636552229 9554238174737236244353543)
  ·
    refine ⟨14331357262105854366530315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554238174737236244353543 14331357262105854366530315)
    ·
      refine ⟨21497035893158781549795473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331357262105854366530315 21497035893158781549795473)
      ·
        refine ⟨16122776919869086162346605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21497035893158781549795473 16122776919869086162346605)
        ·
          refine ⟨6046041344950907310879977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16122776919869086162346605 6046041344950907310879977)
          ·
            refine ⟨4534531008713180483159983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6046041344950907310879977 4534531008713180483159983)
            ·
              refine ⟨6801796513069770724739975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534531008713180483159983 6801796513069770724739975)
              ·
                refine ⟨10202694769604656087109963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801796513069770724739975 10202694769604656087109963)
                ·
                  refine ⟨15304042154406984130664945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202694769604656087109963 15304042154406984130664945)
                  ·
                    refine ⟨11478031615805238097998709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15304042154406984130664945 11478031615805238097998709)
                    ·
                      refine ⟨1076065463981741071687379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11478031615805238097998709 1076065463981741071687379)
                      ·
                        rfl

theorem cell23_2095630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2095630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095630 prefixEnd_2095630 := by exact prefixLift 2095630
  have htrace : WordTrace (prefixWord ++ tailWord_2095630) baseStart_2095630 baseEnd_2095630 := by
    simpa [prefixWord, tailWord_2095630, baseEnd_2095630] using wordTrace_append hprefix tailTrace_2095630
  have hstable : (prefixWord ++ tailWord_2095630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095630).length < 2 ^ (prefixWord ++ tailWord_2095630).sum := by decide
  have hdescent : baseEnd_2095630 < baseStart_2095630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095650 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2095650 : Nat := 118140960795 + 2095650 * 2 ^ 59
def prefixEnd_2095650 : Nat := 4983230072969 + 3 ^ 40 * 2095650 * 2
def baseEnd_2095650 : Nat := 358691911198276997812429

theorem tailTrace_2095650 : CollatzResearch.WordTrace tailWord_2095650 prefixEnd_2095650 358691911198276997812429 := by
  unfold tailWord_2095650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108658714456358342639101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50956423238550288913704269 19108658714456358342639101)
  ·
    refine ⟨7165747017921134378489663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19108658714456358342639101 7165747017921134378489663)
    ·
      refine ⟨10748620526881701567734495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165747017921134378489663 10748620526881701567734495)
      ·
        refine ⟨16122930790322552351601743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748620526881701567734495 16122930790322552351601743)
        ·
          refine ⟨24184396185483828527402615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16122930790322552351601743 24184396185483828527402615)
          ·
            refine ⟨36276594278225742791103923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184396185483828527402615 36276594278225742791103923)
            ·
              refine ⟨54414891417338614186655885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36276594278225742791103923 54414891417338614186655885)
              ·
                refine ⟨20405584281501980319995957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54414891417338614186655885 20405584281501980319995957)
                ·
                  refine ⟨1913023526390810654999621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20405584281501980319995957 1913023526390810654999621)
                  ·
                    refine ⟨358691911198276997812429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913023526390810654999621 358691911198276997812429)
                    ·
                      rfl

theorem cell23_2095650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2095650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095650 prefixEnd_2095650 := by exact prefixLift 2095650
  have htrace : WordTrace (prefixWord ++ tailWord_2095650) baseStart_2095650 baseEnd_2095650 := by
    simpa [prefixWord, tailWord_2095650, baseEnd_2095650] using wordTrace_append hprefix tailTrace_2095650
  have hstable : (prefixWord ++ tailWord_2095650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095650).length < 2 ^ (prefixWord ++ tailWord_2095650).sum := by decide
  have hdescent : baseEnd_2095650 < baseStart_2095650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095653 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_2095653 : Nat := 118140960795 + 2095653 * 2 ^ 59
def prefixEnd_2095653 : Nat := 4983230072969 + 3 ^ 40 * 2095653 * 2
def baseEnd_2095653 : Nat := 1076077274036794481699773

theorem tailTrace_2095653 : CollatzResearch.WordTrace tailWord_2095653 prefixEnd_2095653 1076077274036794481699773 := by
  unfold tailWord_2095653
  simp only [CollatzResearch.WordTrace]
  refine ⟨76434744276814564882915613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50956496184543043255277075 76434744276814564882915613)
  ·
    refine ⟨28663029103805461831093355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76434744276814564882915613 28663029103805461831093355)
    ·
      refine ⟨42994543655708192746640033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28663029103805461831093355 42994543655708192746640033)
      ·
        refine ⟨32245907741781144559980025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42994543655708192746640033 32245907741781144559980025)
        ·
          refine ⟨24184430806335858419985019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32245907741781144559980025 24184430806335858419985019)
          ·
            refine ⟨36276646209503787629977529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184430806335858419985019 36276646209503787629977529)
            ·
              refine ⟨27207484657127840722483147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36276646209503787629977529 27207484657127840722483147)
              ·
                refine ⟨40811226985691761083724721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27207484657127840722483147 40811226985691761083724721)
                ·
                  refine ⟨30608420239268820812793541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40811226985691761083724721 30608420239268820812793541)
                  ·
                    refine ⟨5739078794862903902398789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30608420239268820812793541 5739078794862903902398789)
                    ·
                      refine ⟨1076077274036794481699773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5739078794862903902398789 1076077274036794481699773)
                      ·
                        rfl

theorem cell23_2095653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_2095653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095653 prefixEnd_2095653 := by exact prefixLift 2095653
  have htrace : WordTrace (prefixWord ++ tailWord_2095653) baseStart_2095653 baseEnd_2095653 := by
    simpa [prefixWord, tailWord_2095653, baseEnd_2095653] using wordTrace_append hprefix tailTrace_2095653
  have hstable : (prefixWord ++ tailWord_2095653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095653).length < 2 ^ (prefixWord ++ tailWord_2095653).sum := by decide
  have hdescent : baseEnd_2095653 < baseStart_2095653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095667 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 1, 4]
def baseStart_2095667 : Nat := 118140960795 + 2095667 * 2 ^ 59
def prefixEnd_2095667 : Nat := 4983230072969 + 3 ^ 40 * 2095667 * 2
def baseEnd_2095667 : Nat := 358694820921985808974903

theorem tailTrace_2095667 : CollatzResearch.WordTrace tailWord_2095667 prefixEnd_2095667 358694820921985808974903 := by
  unfold tailWord_2095667
  simp only [CollatzResearch.WordTrace]
  refine ⟨76435254898763845273925255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50956836599175896849283503 76435254898763845273925255)
  ·
    refine ⟨114652882348145767910887883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76435254898763845273925255 114652882348145767910887883)
    ·
      refine ⟨171979323522218651866331825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114652882348145767910887883 171979323522218651866331825)
      ·
        refine ⟨128984492641663988899748869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171979323522218651866331825 128984492641663988899748869)
        ·
          refine ⟨24184592370311997918702913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128984492641663988899748869 24184592370311997918702913)
          ·
            refine ⟨18138444277733998439027185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184592370311997918702913 18138444277733998439027185)
            ·
              refine ⟨13603833208300498829270389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18138444277733998439027185 13603833208300498829270389)
              ·
                refine ⟨1275359363278171765244099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13603833208300498829270389 1275359363278171765244099)
                ·
                  refine ⟨1913039044917257647866149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275359363278171765244099 1913039044917257647866149)
                  ·
                    refine ⟨358694820921985808974903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913039044917257647866149 358694820921985808974903)
                    ·
                      rfl

theorem cell23_2095667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 4].length) (baseStart_2095667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095667 prefixEnd_2095667 := by exact prefixLift 2095667
  have htrace : WordTrace (prefixWord ++ tailWord_2095667) baseStart_2095667 baseEnd_2095667 := by
    simpa [prefixWord, tailWord_2095667, baseEnd_2095667] using wordTrace_append hprefix tailTrace_2095667
  have hstable : (prefixWord ++ tailWord_2095667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095667).length < 2 ^ (prefixWord ++ tailWord_2095667).sum := by decide
  have hdescent : baseEnd_2095667 < baseStart_2095667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095677 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2095677 : Nat := 118140960795 + 2095677 * 2 ^ 59
def prefixEnd_2095677 : Nat := 4983230072969 + 3 ^ 40 * 2095677 * 2
def baseEnd_2095677 : Nat := 1076089597572502387799663

theorem tailTrace_2095677 : CollatzResearch.WordTrace tailWord_2095677 prefixEnd_2095677 1076089597572502387799663 := by
  unfold tailWord_2095677
  simp only [CollatzResearch.WordTrace]
  refine ⟨76435619628727616981789285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50957079752485077987859523 76435619628727616981789285)
  ·
    refine ⟨14331678680386428184085491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76435619628727616981789285 14331678680386428184085491)
    ·
      refine ⟨21497518020579642276128237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331678680386428184085491 21497518020579642276128237)
      ·
        refine ⟨8061569257717365853548089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21497518020579642276128237 8061569257717365853548089)
        ·
          refine ⟨6046176943288024390161067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8061569257717365853548089 6046176943288024390161067)
          ·
            refine ⟨9069265414932036585241601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046176943288024390161067 9069265414932036585241601)
            ·
              refine ⟨6801949061199027438931201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069265414932036585241601 6801949061199027438931201)
              ·
                refine ⟨5101461795899270579198401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801949061199027438931201 5101461795899270579198401)
                ·
                  refine ⟨3826096346924452934398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101461795899270579198401 3826096346924452934398801)
                  ·
                    refine ⟨2869572260193339700799101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826096346924452934398801 2869572260193339700799101)
                    ·
                      refine ⟨1076089597572502387799663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2869572260193339700799101 1076089597572502387799663)
                      ·
                        rfl

theorem cell23_2095677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2095677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095677 prefixEnd_2095677 := by exact prefixLift 2095677
  have htrace : WordTrace (prefixWord ++ tailWord_2095677) baseStart_2095677 baseEnd_2095677 := by
    simpa [prefixWord, tailWord_2095677, baseEnd_2095677] using wordTrace_append hprefix tailTrace_2095677
  have hstable : (prefixWord ++ tailWord_2095677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095677).length < 2 ^ (prefixWord ++ tailWord_2095677).sum := by decide
  have hdescent : baseEnd_2095677 < baseStart_2095677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095703 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2095703 : Nat := 118140960795 + 2095703 * 2 ^ 59
def prefixEnd_2095703 : Nat := 4983230072969 + 3 ^ 40 * 2095703 * 2
def baseEnd_2095703 : Nat := 1076102948069519286074543

theorem tailTrace_2095703 : CollatzResearch.WordTrace tailWord_2095703 prefixEnd_2095703 1076102948069519286074543 := by
  unfold tailWord_2095703
  simp only [CollatzResearch.WordTrace]
  refine ⟨76436567926633423422235763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50957711951088948948157175 76436567926633423422235763)
  ·
    refine ⟨114654851889950135133353645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76436567926633423422235763 114654851889950135133353645)
    ·
      refine ⟨42995569458731300675007617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114654851889950135133353645 42995569458731300675007617)
      ·
        refine ⟨32246677094048475506255713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42995569458731300675007617 32246677094048475506255713)
        ·
          refine ⟨24185007820536356629691785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32246677094048475506255713 24185007820536356629691785)
          ·
            refine ⟨18138755865402267472268839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24185007820536356629691785 18138755865402267472268839)
            ·
              refine ⟨27208133798103401208403259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138755865402267472268839 27208133798103401208403259)
              ·
                refine ⟨40812200697155101812604889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27208133798103401208403259 40812200697155101812604889)
                ·
                  refine ⟨30609150522866326359453667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40812200697155101812604889 30609150522866326359453667)
                  ·
                    refine ⟨45913725784299489539180501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30609150522866326359453667 45913725784299489539180501)
                    ·
                      refine ⟨1076102948069519286074543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45913725784299489539180501 1076102948069519286074543)
                      ·
                        rfl

theorem cell23_2095703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2095703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095703 prefixEnd_2095703 := by exact prefixLift 2095703
  have htrace : WordTrace (prefixWord ++ tailWord_2095703) baseStart_2095703 baseEnd_2095703 := by
    simpa [prefixWord, tailWord_2095703, baseEnd_2095703] using wordTrace_append hprefix tailTrace_2095703
  have hstable : (prefixWord ++ tailWord_2095703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095703).length < 2 ^ (prefixWord ++ tailWord_2095703).sum := by decide
  have hdescent : baseEnd_2095703 < baseStart_2095703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 6]
def baseStart_2095723 : Nat := 118140960795 + 2095723 * 2 ^ 59
def prefixEnd_2095723 : Nat := 4983230072969 + 3 ^ 40 * 2095723 * 2
def baseEnd_2095723 : Nat := 358704405894203069274817

theorem tailTrace_2095723 : CollatzResearch.WordTrace tailWord_2095723 prefixEnd_2095723 358704405894203069274817 := by
  unfold tailWord_2095723
  simp only [CollatzResearch.WordTrace]
  refine ⟨76437297386560966837963823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50958198257707311225309215 76437297386560966837963823)
  ·
    refine ⟨114655946079841450256945735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76437297386560966837963823 114655946079841450256945735)
    ·
      refine ⟨171983919119762175385418603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114655946079841450256945735 171983919119762175385418603)
      ·
        refine ⟨257975878679643263078127905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171983919119762175385418603 257975878679643263078127905)
        ·
          refine ⟨193481909009732447308595929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257975878679643263078127905 193481909009732447308595929)
          ·
            refine ⟨145111431757299335481446947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193481909009732447308595929 145111431757299335481446947)
            ·
              refine ⟨217667147635949003222170421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145111431757299335481446947 217667147635949003222170421)
              ·
                refine ⟨20406295090870219052078477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217667147635949003222170421 20406295090870219052078477)
                ·
                  refine ⟨7652360659076332144529429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20406295090870219052078477 7652360659076332144529429)
                  ·
                    refine ⟨358704405894203069274817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7652360659076332144529429 358704405894203069274817)
                    ·
                      rfl

theorem cell23_2095723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_2095723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095723 prefixEnd_2095723 := by exact prefixLift 2095723
  have htrace : WordTrace (prefixWord ++ tailWord_2095723) baseStart_2095723 baseEnd_2095723 := by
    simpa [prefixWord, tailWord_2095723, baseEnd_2095723] using wordTrace_append hprefix tailTrace_2095723
  have hstable : (prefixWord ++ tailWord_2095723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095723).length < 2 ^ (prefixWord ++ tailWord_2095723).sum := by decide
  have hdescent : baseEnd_2095723 < baseStart_2095723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095724 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_2095724 : Nat := 118140960795 + 2095724 * 2 ^ 59
def prefixEnd_2095724 : Nat := 4983230072969 + 3 ^ 40 * 2095724 * 2
def baseEnd_2095724 : Nat := 1076113731163263703911947

theorem tailTrace_2095724 : CollatzResearch.WordTrace tailWord_2095724 prefixEnd_2095724 1076113731163263703911947 := by
  unfold tailWord_2095724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218666929778672004375113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50958222573038229339166817 38218666929778672004375113)
  ·
    refine ⟨28664000197334004003281335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38218666929778672004375113 28664000197334004003281335)
    ·
      refine ⟨42996000296001006004922003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28664000197334004003281335 42996000296001006004922003)
      ·
        refine ⟨64494000444001509007383005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42996000296001006004922003 64494000444001509007383005)
        ·
          refine ⟨24185250166500565877768627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64494000444001509007383005 24185250166500565877768627)
          ·
            refine ⟨36277875249750848816652941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24185250166500565877768627 36277875249750848816652941)
            ·
              refine ⟨13604203218656568306244853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36277875249750848816652941 13604203218656568306244853)
              ·
                refine ⟨1275394051749053278710455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13604203218656568306244853 1275394051749053278710455)
                ·
                  refine ⟨1913091077623579918065683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275394051749053278710455 1913091077623579918065683)
                  ·
                    refine ⟨2869636616435369877098525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913091077623579918065683 2869636616435369877098525)
                    ·
                      refine ⟨1076113731163263703911947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2869636616435369877098525 1076113731163263703911947)
                      ·
                        rfl

theorem cell23_2095724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_2095724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095724 prefixEnd_2095724 := by exact prefixLift 2095724
  have htrace : WordTrace (prefixWord ++ tailWord_2095724) baseStart_2095724 baseEnd_2095724 := by
    simpa [prefixWord, tailWord_2095724, baseEnd_2095724] using wordTrace_append hprefix tailTrace_2095724
  have hstable : (prefixWord ++ tailWord_2095724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095724).length < 2 ^ (prefixWord ++ tailWord_2095724).sum := by decide
  have hdescent : baseEnd_2095724 < baseStart_2095724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095727 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 1, 5]
def baseStart_2095727 : Nat := 118140960795 + 2095727 * 2 ^ 59
def prefixEnd_2095727 : Nat := 4983230072969 + 3 ^ 40 * 2095727 * 2
def baseEnd_2095727 : Nat := 358705090535075730724811

theorem tailTrace_2095727 : CollatzResearch.WordTrace tailWord_2095727 prefixEnd_2095727 358705090535075730724811 := by
  unfold tailWord_2095727
  simp only [CollatzResearch.WordTrace]
  refine ⟨76437443278546475521109435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50958295519030983680739623 76437443278546475521109435)
  ·
    refine ⟨114656164917819713281664153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76437443278546475521109435 114656164917819713281664153)
    ·
      refine ⟨85992123688364784961248115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114656164917819713281664153 85992123688364784961248115)
      ·
        refine ⟨128988185532547177441872173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85992123688364784961248115 128988185532547177441872173)
        ·
          refine ⟨48370569574705191540702065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128988185532547177441872173 48370569574705191540702065)
          ·
            refine ⟨36277927181028893655526549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48370569574705191540702065 36277927181028893655526549)
            ·
              refine ⟨1700527836610729390102807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36277927181028893655526549 1700527836610729390102807)
              ·
                refine ⟨2550791754916094085154211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700527836610729390102807 2550791754916094085154211)
                ·
                  refine ⟨3826187632374141127731317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550791754916094085154211 3826187632374141127731317)
                  ·
                    refine ⟨358705090535075730724811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3826187632374141127731317 358705090535075730724811)
                    ·
                      rfl

theorem cell23_2095727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_2095727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095727 prefixEnd_2095727 := by exact prefixLift 2095727
  have htrace : WordTrace (prefixWord ++ tailWord_2095727) baseStart_2095727 baseEnd_2095727 := by
    simpa [prefixWord, tailWord_2095727, baseEnd_2095727] using wordTrace_append hprefix tailTrace_2095727
  have hstable : (prefixWord ++ tailWord_2095727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095727).length < 2 ^ (prefixWord ++ tailWord_2095727).sum := by decide
  have hdescent : baseEnd_2095727 < baseStart_2095727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095753 : List Nat := [1, 2, 1, 1, 4, 1, 1, 12]
def baseStart_2095753 : Nat := 118140960795 + 2095753 * 2 ^ 59
def prefixEnd_2095753 : Nat := 4983230072969 + 3 ^ 40 * 2095753 * 2
def baseEnd_2095753 : Nat := 39856615633416447794419

theorem tailTrace_2095753 : CollatzResearch.WordTrace tailWord_2095753 prefixEnd_2095753 39856615633416447794419 := by
  unfold tailWord_2095753
  simp only [CollatzResearch.WordTrace]
  refine ⟨76438391576452281961555913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50958927717634854641037275 76438391576452281961555913)
  ·
    refine ⟨57328793682339211471166935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76438391576452281961555913 57328793682339211471166935)
    ·
      refine ⟨85993190523508817206750403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57328793682339211471166935 85993190523508817206750403)
      ·
        refine ⟨128989785785263225810125605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85993190523508817206750403 128989785785263225810125605)
        ·
          refine ⟨24185584834736854839398551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128989785785263225810125605 24185584834736854839398551)
          ·
            refine ⟨36278377252105282259097827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24185584834736854839398551 36278377252105282259097827)
            ·
              refine ⟨54417565878157923388646741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36278377252105282259097827 54417565878157923388646741)
              ·
                refine ⟨39856615633416447794419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 54417565878157923388646741 39856615633416447794419)
                ·
                  rfl

theorem cell23_2095753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 12].length) (baseStart_2095753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095753 prefixEnd_2095753 := by exact prefixLift 2095753
  have htrace : WordTrace (prefixWord ++ tailWord_2095753) baseStart_2095753 baseEnd_2095753 := by
    simpa [prefixWord, tailWord_2095753, baseEnd_2095753] using wordTrace_append hprefix tailTrace_2095753
  have hstable : (prefixWord ++ tailWord_2095753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095753).length < 2 ^ (prefixWord ++ tailWord_2095753).sum := by decide
  have hdescent : baseEnd_2095753 < baseStart_2095753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_2095763 : Nat := 118140960795 + 2095763 * 2 ^ 59
def prefixEnd_2095763 : Nat := 4983230072969 + 3 ^ 40 * 2095763 * 2
def baseEnd_2095763 : Nat := 1076133756908789051324267

theorem tailTrace_2095763 : CollatzResearch.WordTrace tailWord_2095763 prefixEnd_2095763 1076133756908789051324267 := by
  unfold tailWord_2095763
  simp only [CollatzResearch.WordTrace]
  refine ⟨76438756306416053669419943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50959170870944035779613295 76438756306416053669419943)
  ·
    refine ⟨114658134459624080504129915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76438756306416053669419943 114658134459624080504129915)
    ·
      refine ⟨171987201689436120756194873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114658134459624080504129915 171987201689436120756194873)
      ·
        refine ⟨128990401267077090567146155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171987201689436120756194873 128990401267077090567146155)
        ·
          refine ⟨193485601900615635850719233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128990401267077090567146155 193485601900615635850719233)
          ·
            refine ⟨145114201425461726888039425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193485601900615635850719233 145114201425461726888039425)
            ·
              refine ⟨108835651069096295166029569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145114201425461726888039425 108835651069096295166029569)
              ·
                refine ⟨81626738301822221374522177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108835651069096295166029569 81626738301822221374522177)
                ·
                  refine ⟨61220053726366666030891633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81626738301822221374522177 61220053726366666030891633)
                  ·
                    refine ⟨45915040294774999523168725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61220053726366666030891633 45915040294774999523168725)
                    ·
                      refine ⟨1076133756908789051324267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45915040294774999523168725 1076133756908789051324267)
                      ·
                        rfl

theorem cell23_2095763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_2095763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095763 prefixEnd_2095763 := by exact prefixLift 2095763
  have htrace : WordTrace (prefixWord ++ tailWord_2095763) baseStart_2095763 baseEnd_2095763 := by
    simpa [prefixWord, tailWord_2095763, baseEnd_2095763] using wordTrace_append hprefix tailTrace_2095763
  have hstable : (prefixWord ++ tailWord_2095763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095763).length < 2 ^ (prefixWord ++ tailWord_2095763).sum := by decide
  have hdescent : baseEnd_2095763 < baseStart_2095763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095764 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2095764 : Nat := 118140960795 + 2095764 * 2 ^ 59
def prefixEnd_2095764 : Nat := 4983230072969 + 3 ^ 40 * 2095764 * 2
def baseEnd_2095764 : Nat := 1076134270389443547411763

theorem tailTrace_2095764 : CollatzResearch.WordTrace tailWord_2095764 prefixEnd_2095764 1076134270389443547411763 := by
  unfold tailWord_2095764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38219396389706215420103173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50959195186274953893470897 38219396389706215420103173)
  ·
    refine ⟨7166136823069915391269345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38219396389706215420103173 7166136823069915391269345)
    ·
      refine ⟨5374602617302436543452009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7166136823069915391269345 5374602617302436543452009)
      ·
        refine ⟨4030951962976827407589007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5374602617302436543452009 4030951962976827407589007)
        ·
          refine ⟨6046427944465241111383511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030951962976827407589007 6046427944465241111383511)
          ·
            refine ⟨9069641916697861667075267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046427944465241111383511 9069641916697861667075267)
            ·
              refine ⟨13604462875046792500612901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069641916697861667075267 13604462875046792500612901)
              ·
                refine ⟨2550836789071273593864919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13604462875046792500612901 2550836789071273593864919)
                ·
                  refine ⟨3826255183606910390797379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550836789071273593864919 3826255183606910390797379)
                  ·
                    refine ⟨5739382775410365586196069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3826255183606910390797379 5739382775410365586196069)
                    ·
                      refine ⟨1076134270389443547411763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5739382775410365586196069 1076134270389443547411763)
                      ·
                        rfl

theorem cell23_2095764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2095764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095764 prefixEnd_2095764 := by exact prefixLift 2095764
  have htrace : WordTrace (prefixWord ++ tailWord_2095764) baseStart_2095764 baseEnd_2095764 := by
    simpa [prefixWord, tailWord_2095764, baseEnd_2095764] using wordTrace_append hprefix tailTrace_2095764
  have hstable : (prefixWord ++ tailWord_2095764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095764).length < 2 ^ (prefixWord ++ tailWord_2095764).sum := by decide
  have hdescent : baseEnd_2095764 < baseStart_2095764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095850 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2095850 : Nat := 118140960795 + 2095850 * 2 ^ 59
def prefixEnd_2095850 : Nat := 4983230072969 + 3 ^ 40 * 2095850 * 2
def baseEnd_2095850 : Nat := 1076178429725730210936367

theorem tailTrace_2095850 : CollatzResearch.WordTrace tailWord_2095850 prefixEnd_2095850 1076178429725730210936367 := by
  unfold tailWord_2095850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110482364275216881959251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50961286304733911685224669 19110482364275216881959251)
  ·
    refine ⟨28665723546412825322938877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19110482364275216881959251 28665723546412825322938877)
    ·
      refine ⟨10749646329904809496102079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28665723546412825322938877 10749646329904809496102079)
      ·
        refine ⟨16124469494857214244153119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10749646329904809496102079 16124469494857214244153119)
        ·
          refine ⟨24186704242285821366229679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124469494857214244153119 24186704242285821366229679)
          ·
            refine ⟨36280056363428732049344519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24186704242285821366229679 36280056363428732049344519)
            ·
              refine ⟨54420084545143098074016779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36280056363428732049344519 54420084545143098074016779)
              ·
                refine ⟨81630126817714647111025169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54420084545143098074016779 81630126817714647111025169)
                ·
                  refine ⟨61222595113285985333268877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81630126817714647111025169 61222595113285985333268877)
                  ·
                    refine ⟨22958473167482244499975829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61222595113285985333268877 22958473167482244499975829)
                    ·
                      refine ⟨1076178429725730210936367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22958473167482244499975829 1076178429725730210936367)
                      ·
                        rfl

theorem cell23_2095850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2095850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095850 prefixEnd_2095850 := by exact prefixLift 2095850
  have htrace : WordTrace (prefixWord ++ tailWord_2095850) baseStart_2095850 baseEnd_2095850 := by
    simpa [prefixWord, tailWord_2095850, baseEnd_2095850] using wordTrace_append hprefix tailTrace_2095850
  have hstable : (prefixWord ++ tailWord_2095850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095850).length < 2 ^ (prefixWord ++ tailWord_2095850).sum := by decide
  have hdescent : baseEnd_2095850 < baseStart_2095850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095897 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 7, 2]
def baseStart_2095897 : Nat := 118140960795 + 2095897 * 2 ^ 59
def prefixEnd_2095897 : Nat := 4983230072969 + 3 ^ 40 * 2095897 * 2
def baseEnd_2095897 : Nat := 1076202563316491527048651

theorem tailTrace_2095897 : CollatzResearch.WordTrace tailWord_2095897 prefixEnd_2095897 1076202563316491527048651 := by
  unfold tailWord_2095897
  simp only [CollatzResearch.WordTrace]
  refine ⟨76443643687930594554797945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50962429125287063036531963 76443643687930594554797945)
  ·
    refine ⟨57332732765947945916098459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76443643687930594554797945 57332732765947945916098459)
    ·
      refine ⟨85999099148921918874147689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57332732765947945916098459 85999099148921918874147689)
      ·
        refine ⟨64499324361691439155610767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85999099148921918874147689 64499324361691439155610767)
        ·
          refine ⟨96748986542537158733416151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64499324361691439155610767 96748986542537158733416151)
          ·
            refine ⟨145123479813805738100124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96748986542537158733416151 145123479813805738100124227)
            ·
              refine ⟨217685219720708607150186341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145123479813805738100124227 217685219720708607150186341)
              ·
                refine ⟨40815978697632863840659939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217685219720708607150186341 40815978697632863840659939)
                ·
                  refine ⟨61223968046449295760989909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40815978697632863840659939 61223968046449295760989909)
                  ·
                    refine ⟨1434936751088655369398201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61223968046449295760989909 1434936751088655369398201)
                    ·
                      refine ⟨1076202563316491527048651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434936751088655369398201 1076202563316491527048651)
                      ·
                        rfl

theorem cell23_2095897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_2095897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095897 prefixEnd_2095897 := by exact prefixLift 2095897
  have htrace : WordTrace (prefixWord ++ tailWord_2095897) baseStart_2095897 baseEnd_2095897 := by
    simpa [prefixWord, tailWord_2095897, baseEnd_2095897] using wordTrace_append hprefix tailTrace_2095897
  have hstable : (prefixWord ++ tailWord_2095897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095897).length < 2 ^ (prefixWord ++ tailWord_2095897).sum := by decide
  have hdescent : baseEnd_2095897 < baseStart_2095897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095947 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3]
def baseStart_2095947 : Nat := 118140960795 + 2095947 * 2 ^ 59
def prefixEnd_2095947 : Nat := 4983230072969 + 3 ^ 40 * 2095947 * 2
def baseEnd_2095947 : Nat := 1076228237349216331423421

theorem tailTrace_2095947 : CollatzResearch.WordTrace tailWord_2095947 prefixEnd_2095947 1076228237349216331423421 := by
  unfold tailWord_2095947
  simp only [CollatzResearch.WordTrace]
  refine ⟨76445467337749453094118095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50963644891832968729412063 76445467337749453094118095)
  ·
    refine ⟨114668201006624179641177143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76445467337749453094118095 114668201006624179641177143)
    ·
      refine ⟨172002301509936269461765715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114668201006624179641177143 172002301509936269461765715)
      ·
        refine ⟨258003452264904404192648573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172002301509936269461765715 258003452264904404192648573)
        ·
          refine ⟨96751294599339151572243215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258003452264904404192648573 96751294599339151572243215)
          ·
            refine ⟨145126941899008727358364823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96751294599339151572243215 145126941899008727358364823)
            ·
              refine ⟨217690412848513091037547235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145126941899008727358364823 217690412848513091037547235)
              ·
                refine ⟨326535619272769636556320853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217690412848513091037547235 326535619272769636556320853)
                ·
                  refine ⟨3826589288352769178394385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 326535619272769636556320853 3826589288352769178394385)
                  ·
                    refine ⟨2869941966264576883795789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826589288352769178394385 2869941966264576883795789)
                    ·
                      refine ⟨1076228237349216331423421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2869941966264576883795789 1076228237349216331423421)
                      ·
                        rfl

theorem cell23_2095947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].length) (baseStart_2095947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095947 prefixEnd_2095947 := by exact prefixLift 2095947
  have htrace : WordTrace (prefixWord ++ tailWord_2095947) baseStart_2095947 baseEnd_2095947 := by
    simpa [prefixWord, tailWord_2095947, baseEnd_2095947] using wordTrace_append hprefix tailTrace_2095947
  have hstable : (prefixWord ++ tailWord_2095947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095947).length < 2 ^ (prefixWord ++ tailWord_2095947).sum := by decide
  have hdescent : baseEnd_2095947 < baseStart_2095947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095967 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 6]
def baseStart_2095967 : Nat := 118140960795 + 2095967 * 2 ^ 59
def prefixEnd_2095967 : Nat := 4983230072969 + 3 ^ 40 * 2095967 * 2
def baseEnd_2095967 : Nat := 119582056329145139241481

theorem tailTrace_2095967 : CollatzResearch.WordTrace tailWord_2095967 prefixEnd_2095967 119582056329145139241481 := by
  unfold tailWord_2095967
  simp only [CollatzResearch.WordTrace]
  refine ⟨76446196797676996509846155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50964131198451331006564103 76446196797676996509846155)
  ·
    refine ⟨114669295196515494764769233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76446196797676996509846155 114669295196515494764769233)
    ·
      refine ⟨86001971397386621073576925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114669295196515494764769233 86001971397386621073576925)
      ·
        refine ⟨32250739274019982902591347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86001971397386621073576925 32250739274019982902591347)
        ·
          refine ⟨48376108911029974353887021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32250739274019982902591347 48376108911029974353887021)
          ·
            refine ⟨18141040841636240382707633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48376108911029974353887021 18141040841636240382707633)
            ·
              refine ⟨13605780631227180287030725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18141040841636240382707633 13605780631227180287030725)
              ·
                refine ⟨2551083868355096303818261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13605780631227180287030725 2551083868355096303818261)
                ·
                  refine ⟨119582056329145139241481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2551083868355096303818261 119582056329145139241481)
                  ·
                    rfl

theorem cell23_2095967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 6].length) (baseStart_2095967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095967 prefixEnd_2095967 := by exact prefixLift 2095967
  have htrace : WordTrace (prefixWord ++ tailWord_2095967) baseStart_2095967 baseEnd_2095967 := by
    simpa [prefixWord, tailWord_2095967, baseEnd_2095967] using wordTrace_append hprefix tailTrace_2095967
  have hstable : (prefixWord ++ tailWord_2095967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095967).length < 2 ^ (prefixWord ++ tailWord_2095967).sum := by decide
  have hdescent : baseEnd_2095967 < baseStart_2095967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095971 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 3, 4]
def baseStart_2095971 : Nat := 118140960795 + 2095971 * 2 ^ 59
def prefixEnd_2095971 : Nat := 4983230072969 + 3 ^ 40 * 2095971 * 2
def baseEnd_2095971 : Nat := 358746853628308079174437

theorem tailTrace_2095971 : CollatzResearch.WordTrace tailWord_2095971 prefixEnd_2095971 358746853628308079174437 := by
  unfold tailWord_2095971
  simp only [CollatzResearch.WordTrace]
  refine ⟨76446342689662505192991767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50964228459775003461994511 76446342689662505192991767)
  ·
    refine ⟨114669514034493757789487651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76446342689662505192991767 114669514034493757789487651)
    ·
      refine ⟨172004271051740636684231477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114669514034493757789487651 172004271051740636684231477)
      ·
        refine ⟨16125400411100684689146701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172004271051740636684231477 16125400411100684689146701)
        ·
          refine ⟨6047025154162756758430013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16125400411100684689146701 6047025154162756758430013)
          ·
            refine ⟨2267634432811033784411255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047025154162756758430013 2267634432811033784411255)
            ·
              refine ⟨3401451649216550676616883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267634432811033784411255 3401451649216550676616883)
              ·
                refine ⟨5102177473824826014925325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401451649216550676616883 5102177473824826014925325)
                ·
                  refine ⟨1913316552684309755596997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5102177473824826014925325 1913316552684309755596997)
                  ·
                    refine ⟨358746853628308079174437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913316552684309755596997 358746853628308079174437)
                    ·
                      rfl

theorem cell23_2095971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 4].length) (baseStart_2095971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095971 prefixEnd_2095971 := by exact prefixLift 2095971
  have htrace : WordTrace (prefixWord ++ tailWord_2095971) baseStart_2095971 baseEnd_2095971 := by
    simpa [prefixWord, tailWord_2095971, baseEnd_2095971] using wordTrace_append hprefix tailTrace_2095971
  have hstable : (prefixWord ++ tailWord_2095971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095971).length < 2 ^ (prefixWord ++ tailWord_2095971).sum := by decide
  have hdescent : baseEnd_2095971 < baseStart_2095971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095984 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 6]
def baseStart_2095984 : Nat := 118140960795 + 2095984 * 2 ^ 59
def prefixEnd_2095984 : Nat := 4983230072969 + 3 ^ 40 * 2095984 * 2
def baseEnd_2095984 : Nat := 119583026237048076295639

theorem tailTrace_2095984 : CollatzResearch.WordTrace tailWord_2095984 prefixEnd_2095984 119583026237048076295639 := by
  unfold tailWord_2095984
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223408419307704206607503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50964544559076938942143337 38223408419307704206607503)
  ·
    refine ⟨57335112628961556309911255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38223408419307704206607503 57335112628961556309911255)
    ·
      refine ⟨86002668943442334464866883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57335112628961556309911255 86002668943442334464866883)
      ·
        refine ⟨129004003415163501697300325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86002668943442334464866883 129004003415163501697300325)
        ·
          refine ⟨24188250640343156568243811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129004003415163501697300325 24188250640343156568243811)
          ·
            refine ⟨36282375960514734852365717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188250640343156568243811 36282375960514734852365717)
            ·
              refine ⟨1700736373149128196204643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36282375960514734852365717 1700736373149128196204643)
              ·
                refine ⟨2551104559723692294306965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700736373149128196204643 2551104559723692294306965)
                ·
                  refine ⟨119583026237048076295639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2551104559723692294306965 119583026237048076295639)
                  ·
                    rfl

theorem cell23_2095984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_2095984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095984 prefixEnd_2095984 := by exact prefixLift 2095984
  have htrace : WordTrace (prefixWord ++ tailWord_2095984) baseStart_2095984 baseEnd_2095984 := by
    simpa [prefixWord, tailWord_2095984, baseEnd_2095984] using wordTrace_append hprefix tailTrace_2095984
  have hstable : (prefixWord ++ tailWord_2095984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095984).length < 2 ^ (prefixWord ++ tailWord_2095984).sum := by decide
  have hdescent : baseEnd_2095984 < baseStart_2095984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095994 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_2095994 : Nat := 118140960795 + 2095994 * 2 ^ 59
def prefixEnd_2095994 : Nat := 4983230072969 + 3 ^ 40 * 2095994 * 2
def baseEnd_2095994 : Nat := 1076252370939977647535705

theorem tailTrace_2095994 : CollatzResearch.WordTrace tailWord_2095994 prefixEnd_2095994 1076252370939977647535705 := by
  unfold tailWord_2095994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111795392144795030269759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50964787712386120080719357 19111795392144795030269759)
  ·
    refine ⟨28667693088217192545404639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19111795392144795030269759 28667693088217192545404639)
    ·
      refine ⟨43001539632325788818106959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28667693088217192545404639 43001539632325788818106959)
      ·
        refine ⟨64502309448488683227160439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43001539632325788818106959 64502309448488683227160439)
        ·
          refine ⟨96753464172733024840740659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64502309448488683227160439 96753464172733024840740659)
          ·
            refine ⟨145130196259099537261110989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96753464172733024840740659 145130196259099537261110989)
            ·
              refine ⟨54423823597162326472916621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145130196259099537261110989 54423823597162326472916621)
              ·
                refine ⟨20408933848935872427343733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54423823597162326472916621 20408933848935872427343733)
                ·
                  refine ⟨1913337548337738040063475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20408933848935872427343733 1913337548337738040063475)
                  ·
                    refine ⟨2870006322506607060095213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913337548337738040063475 2870006322506607060095213)
                    ·
                      refine ⟨1076252370939977647535705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870006322506607060095213 1076252370939977647535705)
                      ·
                        rfl

theorem cell23_2095994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_2095994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2095994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2095994 prefixEnd_2095994 := by exact prefixLift 2095994
  have htrace : WordTrace (prefixWord ++ tailWord_2095994) baseStart_2095994 baseEnd_2095994 := by
    simpa [prefixWord, tailWord_2095994, baseEnd_2095994] using wordTrace_append hprefix tailTrace_2095994
  have hstable : (prefixWord ++ tailWord_2095994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095994).length < 2 ^ (prefixWord ++ tailWord_2095994).sum := by decide
  have hdescent : baseEnd_2095994 < baseStart_2095994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096021 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_2096021 : Nat := 118140960795 + 2096021 * 2 ^ 59
def prefixEnd_2096021 : Nat := 4983230072969 + 3 ^ 40 * 2096021 * 2
def baseEnd_2096021 : Nat := 1076266234917649041898081

theorem tailTrace_2096021 : CollatzResearch.WordTrace tailWord_2096021 prefixEnd_2096021 1076266234917649041898081 := by
  unfold tailWord_2096021
  simp only [CollatzResearch.WordTrace]
  refine ⟨76448166339481363732311917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50965444226320909154874611 76448166339481363732311917)
  ·
    refine ⟨28668062377305511399616969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76448166339481363732311917 28668062377305511399616969)
    ·
      refine ⟨21501046782979133549712727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28668062377305511399616969 21501046782979133549712727)
      ·
        refine ⟨32251570174468700324569091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21501046782979133549712727 32251570174468700324569091)
        ·
          refine ⟨48377355261703050486853637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251570174468700324569091 48377355261703050486853637)
          ·
            refine ⟨9070754111569321966285057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48377355261703050486853637 9070754111569321966285057)
            ·
              refine ⟨6803065583676991474713793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070754111569321966285057 6803065583676991474713793)
              ·
                refine ⟨5102299187757743606035345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803065583676991474713793 5102299187757743606035345)
                ·
                  refine ⟨3826724390818307704526509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102299187757743606035345 3826724390818307704526509)
                  ·
                    refine ⟨1435021646556865389197441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826724390818307704526509 1435021646556865389197441)
                    ·
                      refine ⟨1076266234917649041898081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435021646556865389197441 1076266234917649041898081)
                      ·
                        rfl

theorem cell23_2096021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_2096021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096021 prefixEnd_2096021 := by exact prefixLift 2096021
  have htrace : WordTrace (prefixWord ++ tailWord_2096021) baseStart_2096021 baseEnd_2096021 := by
    simpa [prefixWord, tailWord_2096021, baseEnd_2096021] using wordTrace_append hprefix tailTrace_2096021
  have hstable : (prefixWord ++ tailWord_2096021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096021).length < 2 ^ (prefixWord ++ tailWord_2096021).sum := by decide
  have hdescent : baseEnd_2096021 < baseStart_2096021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096022 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2096022 : Nat := 118140960795 + 2096022 * 2 ^ 59
def prefixEnd_2096022 : Nat := 4983230072969 + 3 ^ 40 * 2096022 * 2
def baseEnd_2096022 : Nat := 358755582799434512661859

theorem tailTrace_2096022 : CollatzResearch.WordTrace tailWord_2096022 prefixEnd_2096022 358755582799434512661859 := by
  unfold tailWord_2096022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778012675779858806443645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50965468541651827268732213 4778012675779858806443645)
  ·
    refine ⟨1791754753417447052416367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4778012675779858806443645 1791754753417447052416367)
    ·
      refine ⟨2687632130126170578624551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791754753417447052416367 2687632130126170578624551)
      ·
        refine ⟨4031448195189255867936827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687632130126170578624551 4031448195189255867936827)
        ·
          refine ⟨6047172292783883801905241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031448195189255867936827 6047172292783883801905241)
          ·
            refine ⟨4535379219587912851428931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047172292783883801905241 4535379219587912851428931)
            ·
              refine ⟨6803068829381869277143397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535379219587912851428931 6803068829381869277143397)
              ·
                refine ⟨1275575405509100489464387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6803068829381869277143397 1275575405509100489464387)
                ·
                  refine ⟨1913363108263650734196581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275575405509100489464387 1913363108263650734196581)
                  ·
                    refine ⟨358755582799434512661859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913363108263650734196581 358755582799434512661859)
                    ·
                      rfl

theorem cell23_2096022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2096022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096022 prefixEnd_2096022 := by exact prefixLift 2096022
  have htrace : WordTrace (prefixWord ++ tailWord_2096022) baseStart_2096022 baseEnd_2096022 := by
    simpa [prefixWord, tailWord_2096022, baseEnd_2096022] using wordTrace_append hprefix tailTrace_2096022
  have hstable : (prefixWord ++ tailWord_2096022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096022).length < 2 ^ (prefixWord ++ tailWord_2096022).sum := by decide
  have hdescent : baseEnd_2096022 < baseStart_2096022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096045 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2096045 : Nat := 118140960795 + 2096045 * 2 ^ 59
def prefixEnd_2096045 : Nat := 4983230072969 + 3 ^ 40 * 2096045 * 2
def baseEnd_2096045 : Nat := 1076278558453356947997971

theorem tailTrace_2096045 : CollatzResearch.WordTrace tailWord_2096045 prefixEnd_2096045 1076278558453356947997971 := by
  unfold tailWord_2096045
  simp only [CollatzResearch.WordTrace]
  refine ⟨76449041691394415831185589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50966027794262943887457059 76449041691394415831185589)
  ·
    refine ⟨7167097658568226484173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76449041691394415831185589 7167097658568226484173649)
    ·
      refine ⟨5375323243926169863130237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167097658568226484173649 5375323243926169863130237)
      ·
        refine ⟨2015746216472313698673839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5375323243926169863130237 2015746216472313698673839)
        ·
          refine ⟨3023619324708470548010759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015746216472313698673839 3023619324708470548010759)
          ·
            refine ⟨4535428987062705822016139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023619324708470548010759 4535428987062705822016139)
            ·
              refine ⟨6803143480594058733024209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535428987062705822016139 6803143480594058733024209)
              ·
                refine ⟨5102357610445544049768157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803143480594058733024209 5102357610445544049768157)
                ·
                  refine ⟨1913384103917079018663059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5102357610445544049768157 1913384103917079018663059)
                  ·
                    refine ⟨2870076155875618527994589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913384103917079018663059 2870076155875618527994589)
                    ·
                      refine ⟨1076278558453356947997971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870076155875618527994589 1076278558453356947997971)
                      ·
                        rfl

theorem cell23_2096045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2096045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096045 prefixEnd_2096045 := by exact prefixLift 2096045
  have htrace : WordTrace (prefixWord ++ tailWord_2096045) baseStart_2096045 baseEnd_2096045 := by
    simpa [prefixWord, tailWord_2096045, baseEnd_2096045] using wordTrace_append hprefix tailTrace_2096045
  have hstable : (prefixWord ++ tailWord_2096045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096045).length < 2 ^ (prefixWord ++ tailWord_2096045).sum := by decide
  have hdescent : baseEnd_2096045 < baseStart_2096045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096064 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_2096064 : Nat := 118140960795 + 2096064 * 2 ^ 59
def prefixEnd_2096064 : Nat := 4983230072969 + 3 ^ 40 * 2096064 * 2
def baseEnd_2096064 : Nat := 1076288314585792373660383

theorem tailTrace_2096064 : CollatzResearch.WordTrace tailWord_2096064 prefixEnd_2096064 1076288314585792373660383 := by
  unfold tailWord_2096064
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224867339162791038063623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50966489785550388050751497 38224867339162791038063623)
  ·
    refine ⟨57337301008744186557095435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38224867339162791038063623 57337301008744186557095435)
    ·
      refine ⟨86005951513116279835643153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57337301008744186557095435 86005951513116279835643153)
      ·
        refine ⟨64504463634837209876732365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86005951513116279835643153 64504463634837209876732365)
        ·
          refine ⟨24189173863063953703774637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64504463634837209876732365 24189173863063953703774637)
          ·
            refine ⟨9070940198648982638915489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189173863063953703774637 9070940198648982638915489)
            ·
              refine ⟨6803205148986736979186617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070940198648982638915489 6803205148986736979186617)
              ·
                refine ⟨5102403861740052734389963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803205148986736979186617 5102403861740052734389963)
                ·
                  refine ⟨7653605792610079101584945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102403861740052734389963 7653605792610079101584945)
                  ·
                    refine ⟨5740204344457559326188709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653605792610079101584945 5740204344457559326188709)
                    ·
                      refine ⟨1076288314585792373660383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740204344457559326188709 1076288314585792373660383)
                      ·
                        rfl

theorem cell23_2096064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_2096064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096064 prefixEnd_2096064 := by exact prefixLift 2096064
  have htrace : WordTrace (prefixWord ++ tailWord_2096064) baseStart_2096064 baseEnd_2096064 := by
    simpa [prefixWord, tailWord_2096064, baseEnd_2096064] using wordTrace_append hprefix tailTrace_2096064
  have hstable : (prefixWord ++ tailWord_2096064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096064).length < 2 ^ (prefixWord ++ tailWord_2096064).sum := by decide
  have hdescent : baseEnd_2096064 < baseStart_2096064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096078 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2096078 : Nat := 118140960795 + 2096078 * 2 ^ 59
def prefixEnd_2096078 : Nat := 4983230072969 + 3 ^ 40 * 2096078 * 2
def baseEnd_2096078 : Nat := 358765167771651772961773

theorem tailTrace_2096078 : CollatzResearch.WordTrace tailWord_2096078 prefixEnd_2096078 358765167771651772961773 := by
  unfold tailWord_2096078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556280662534357808392111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50966830200183241644757925 9556280662534357808392111)
  ·
    refine ⟨14334420993801536712588167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9556280662534357808392111 14334420993801536712588167)
    ·
      refine ⟨21501631490702305068882251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14334420993801536712588167 21501631490702305068882251)
      ·
        refine ⟨32252447236053457603323377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21501631490702305068882251 32252447236053457603323377)
        ·
          refine ⟨24189335427040093202492533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252447236053457603323377 24189335427040093202492533)
          ·
            refine ⟨2267750196285008737733675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24189335427040093202492533 2267750196285008737733675)
            ·
              refine ⟨3401625294427513106600513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267750196285008737733675 3401625294427513106600513)
              ·
                refine ⟨2551218970820634829950385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401625294427513106600513 2551218970820634829950385)
                ·
                  refine ⟨1913414228115476122462789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551218970820634829950385 1913414228115476122462789)
                  ·
                    refine ⟨358765167771651772961773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913414228115476122462789 358765167771651772961773)
                    ·
                      rfl

theorem cell23_2096078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2096078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096078 prefixEnd_2096078 := by exact prefixLift 2096078
  have htrace : WordTrace (prefixWord ++ tailWord_2096078) baseStart_2096078 baseEnd_2096078 := by
    simpa [prefixWord, tailWord_2096078, baseEnd_2096078] using wordTrace_append hprefix tailTrace_2096078
  have hstable : (prefixWord ++ tailWord_2096078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096078).length < 2 ^ (prefixWord ++ tailWord_2096078).sum := by decide
  have hdescent : baseEnd_2096078 < baseStart_2096078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096085 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2096085 : Nat := 118140960795 + 2096085 * 2 ^ 59
def prefixEnd_2096085 : Nat := 4983230072969 + 3 ^ 40 * 2096085 * 2
def baseEnd_2096085 : Nat := 1076299097679536791497787

theorem tailTrace_2096085 : CollatzResearch.WordTrace tailWord_2096085 prefixEnd_2096085 1076299097679536791497787 := by
  unfold tailWord_2096085
  simp only [CollatzResearch.WordTrace]
  refine ⟨76450500611249502662641709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50967000407499668441761139 76450500611249502662641709)
  ·
    refine ⟨28668937729218563498490641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76450500611249502662641709 28668937729218563498490641)
    ·
      refine ⟨21501703296913922623867981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28668937729218563498490641 21501703296913922623867981)
      ·
        refine ⟨8063138736342720983950493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21501703296913922623867981 8063138736342720983950493)
        ·
          refine ⟨3023677026128520368981435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8063138736342720983950493 3023677026128520368981435)
          ·
            refine ⟨4535515539192780553472153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023677026128520368981435 4535515539192780553472153)
            ·
              refine ⟨3401636654394585415104115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535515539192780553472153 3401636654394585415104115)
              ·
                refine ⟨5102454981591878122656173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401636654394585415104115 5102454981591878122656173)
                ·
                  refine ⟨1913420618096954295996065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5102454981591878122656173 1913420618096954295996065)
                  ·
                    refine ⟨1435065463572715721997049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913420618096954295996065 1435065463572715721997049)
                    ·
                      refine ⟨1076299097679536791497787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435065463572715721997049 1076299097679536791497787)
                      ·
                        rfl

theorem cell23_2096085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2096085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096085 prefixEnd_2096085 := by exact prefixLift 2096085
  have htrace : WordTrace (prefixWord ++ tailWord_2096085) baseStart_2096085 baseEnd_2096085 := by
    simpa [prefixWord, tailWord_2096085, baseEnd_2096085] using wordTrace_append hprefix tailTrace_2096085
  have hstable : (prefixWord ++ tailWord_2096085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096085).length < 2 ^ (prefixWord ++ tailWord_2096085).sum := by decide
  have hdescent : baseEnd_2096085 < baseStart_2096085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096087 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 7]
def baseStart_2096087 : Nat := 118140960795 + 2096087 * 2 ^ 59
def prefixEnd_2096087 : Nat := 4983230072969 + 3 ^ 40 * 2096087 * 2
def baseEnd_2096087 : Nat := 358766708213615261224259

theorem tailTrace_2096087 : CollatzResearch.WordTrace tailWord_2096087 prefixEnd_2096087 358766708213615261224259 := by
  unfold tailWord_2096087
  simp only [CollatzResearch.WordTrace]
  refine ⟨76450573557242257004214515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50967049038161504669476343 76450573557242257004214515)
  ·
    refine ⟨114675860335863385506321773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76450573557242257004214515 114675860335863385506321773)
    ·
      refine ⟨43003447625948769564870665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114675860335863385506321773 43003447625948769564870665)
      ·
        refine ⟨32252585719461577173652999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43003447625948769564870665 32252585719461577173652999)
        ·
          refine ⟨48378878579192365760479499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32252585719461577173652999 48378878579192365760479499)
          ·
            refine ⟨72568317868788548640719249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48378878579192365760479499 72568317868788548640719249)
            ·
              refine ⟨54426238401591411480539437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72568317868788548640719249 54426238401591411480539437)
              ·
                refine ⟨20409839400596779305202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54426238401591411480539437 20409839400596779305202289)
                ·
                  refine ⟨15307379550447584478901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20409839400596779305202289 15307379550447584478901717)
                  ·
                    refine ⟨358766708213615261224259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15307379550447584478901717 358766708213615261224259)
                    ·
                      rfl

theorem cell23_2096087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_2096087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096087 prefixEnd_2096087 := by exact prefixLift 2096087
  have htrace : WordTrace (prefixWord ++ tailWord_2096087) baseStart_2096087 baseEnd_2096087 := by
    simpa [prefixWord, tailWord_2096087, baseEnd_2096087] using wordTrace_append hprefix tailTrace_2096087
  have hstable : (prefixWord ++ tailWord_2096087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096087).length < 2 ^ (prefixWord ++ tailWord_2096087).sum := by decide
  have hdescent : baseEnd_2096087 < baseStart_2096087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096098 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2096098 : Nat := 118140960795 + 2096098 * 2 ^ 59
def prefixEnd_2096098 : Nat := 4983230072969 + 3 ^ 40 * 2096098 * 2
def baseEnd_2096098 : Nat := 1076305772928045240635227

theorem tailTrace_2096098 : CollatzResearch.WordTrace tailWord_2096098 prefixEnd_2096098 1076305772928045240635227 := by
  unfold tailWord_2096098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112743690050601470716237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50967316506801603921909965 19112743690050601470716237)
  ·
    refine ⟨7167278883768975551518589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19112743690050601470716237 7167278883768975551518589)
    ·
      refine ⟨2687729581413365831819471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7167278883768975551518589 2687729581413365831819471)
      ·
        refine ⟨4031594372120048747729207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687729581413365831819471 4031594372120048747729207)
        ·
          refine ⟨6047391558180073121593811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031594372120048747729207 6047391558180073121593811)
          ·
            refine ⟨9071087337270109682390717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047391558180073121593811 9071087337270109682390717)
            ·
              refine ⟨3401657751476291130896519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9071087337270109682390717 3401657751476291130896519)
              ·
                refine ⟨5102486627214436696344779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401657751476291130896519 5102486627214436696344779)
                ·
                  refine ⟨7653729940821655044517169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102486627214436696344779 7653729940821655044517169)
                  ·
                    refine ⟨5740297455616241283387877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653729940821655044517169 5740297455616241283387877)
                    ·
                      refine ⟨1076305772928045240635227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740297455616241283387877 1076305772928045240635227)
                      ·
                        rfl

theorem cell23_2096098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2096098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096098 prefixEnd_2096098 := by exact prefixLift 2096098
  have htrace : WordTrace (prefixWord ++ tailWord_2096098) baseStart_2096098 baseEnd_2096098 := by
    simpa [prefixWord, tailWord_2096098, baseEnd_2096098] using wordTrace_append hprefix tailTrace_2096098
  have hstable : (prefixWord ++ tailWord_2096098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096098).length < 2 ^ (prefixWord ++ tailWord_2096098).sum := by decide
  have hdescent : baseEnd_2096098 < baseStart_2096098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096118 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2096118 : Nat := 118140960795 + 2096118 * 2 ^ 59
def prefixEnd_2096118 : Nat := 4983230072969 + 3 ^ 40 * 2096118 * 2
def baseEnd_2096118 : Nat := 1076316042541135162385135

theorem tailTrace_2096118 : CollatzResearch.WordTrace tailWord_2096118 prefixEnd_2096118 1076316042541135162385135 := by
  unfold tailWord_2096118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778231513758121831162063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50967802813419966199062005 4778231513758121831162063)
  ·
    refine ⟨7167347270637182746743095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778231513758121831162063 7167347270637182746743095)
    ·
      refine ⟨10751020905955774120114643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167347270637182746743095 10751020905955774120114643)
      ·
        refine ⟨16126531358933661180171965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751020905955774120114643 16126531358933661180171965)
        ·
          refine ⟨6047449259600122942564487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16126531358933661180171965 6047449259600122942564487)
          ·
            refine ⟨9071173889400184413846731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047449259600122942564487 9071173889400184413846731)
            ·
              refine ⟨13606760834100276620770097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071173889400184413846731 13606760834100276620770097)
              ·
                refine ⟨10205070625575207465577573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13606760834100276620770097 10205070625575207465577573)
                ·
                  refine ⟨1913450742295351399795795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10205070625575207465577573 1913450742295351399795795)
                  ·
                    refine ⟨2870176113443027099693693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913450742295351399795795 2870176113443027099693693)
                    ·
                      refine ⟨1076316042541135162385135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870176113443027099693693 1076316042541135162385135)
                      ·
                        rfl

theorem cell23_2096118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2096118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096118 prefixEnd_2096118 := by exact prefixLift 2096118
  have htrace : WordTrace (prefixWord ++ tailWord_2096118) baseStart_2096118 baseEnd_2096118 := by
    simpa [prefixWord, tailWord_2096118, baseEnd_2096118] using wordTrace_append hprefix tailTrace_2096118
  have hstable : (prefixWord ++ tailWord_2096118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096118).length < 2 ^ (prefixWord ++ tailWord_2096118).sum := by decide
  have hdescent : baseEnd_2096118 < baseStart_2096118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096146 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2096146 : Nat := 118140960795 + 2096146 * 2 ^ 59
def prefixEnd_2096146 : Nat := 4983230072969 + 3 ^ 40 * 2096146 * 2
def baseEnd_2096146 : Nat := 358776806666487017611669

theorem tailTrace_2096146 : CollatzResearch.WordTrace tailWord_2096146 prefixEnd_2096146 358776806666487017611669 := by
  unfold tailWord_2096146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113181366007127520153073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50968483642685673387074861 19113181366007127520153073)
  ·
    refine ⟨14334886024505345640114805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19113181366007127520153073 14334886024505345640114805)
    ·
      refine ⟨1343895564797376153760763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14334886024505345640114805 1343895564797376153760763)
      ·
        refine ⟨2015843347196064230641145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343895564797376153760763 2015843347196064230641145)
        ·
          refine ⟨1511882510397048172980859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015843347196064230641145 1511882510397048172980859)
          ·
            refine ⟨2267823765595572259471289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511882510397048172980859 2267823765595572259471289)
            ·
              refine ⟨1700867824196679194603467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267823765595572259471289 1700867824196679194603467)
              ·
                refine ⟨2551301736295018791905201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700867824196679194603467 2551301736295018791905201)
                ·
                  refine ⟨1913476302221264093928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551301736295018791905201 1913476302221264093928901)
                  ·
                    refine ⟨358776806666487017611669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913476302221264093928901 358776806666487017611669)
                    ·
                      rfl

theorem cell23_2096146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2096146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096146 prefixEnd_2096146 := by exact prefixLift 2096146
  have htrace : WordTrace (prefixWord ++ tailWord_2096146) baseStart_2096146 baseEnd_2096146 := by
    simpa [prefixWord, tailWord_2096146, baseEnd_2096146] using wordTrace_append hprefix tailTrace_2096146
  have hstable : (prefixWord ++ tailWord_2096146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096146).length < 2 ^ (prefixWord ++ tailWord_2096146).sum := by decide
  have hdescent : baseEnd_2096146 < baseStart_2096146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096154 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2096154 : Nat := 118140960795 + 2096154 * 2 ^ 59
def prefixEnd_2096154 : Nat := 4983230072969 + 3 ^ 40 * 2096154 * 2
def baseEnd_2096154 : Nat := 1076334527844697021534969

theorem tailTrace_2096154 : CollatzResearch.WordTrace tailWord_2096154 prefixEnd_2096154 1076334527844697021534969 := by
  unfold tailWord_2096154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113254311999881861725879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50968678165333018297935677 19113254311999881861725879)
  ·
    refine ⟨28669881467999822792588819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19113254311999881861725879 28669881467999822792588819)
    ·
      refine ⟨43004822201999734188883229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28669881467999822792588819 43004822201999734188883229)
      ·
        refine ⟨16126808325749900320831211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43004822201999734188883229 16126808325749900320831211)
        ·
          refine ⟨24190212488624850481246817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126808325749900320831211 24190212488624850481246817)
          ·
            refine ⟨18142659366468637860935113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24190212488624850481246817 18142659366468637860935113)
            ·
              refine ⟨13606994524851478395701335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18142659366468637860935113 13606994524851478395701335)
              ·
                refine ⟨20410491787277217593552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606994524851478395701335 20410491787277217593552003)
                ·
                  refine ⟨30615737680915826390328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410491787277217593552003 30615737680915826390328005)
                  ·
                    refine ⟨5740450815171717448186501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30615737680915826390328005 5740450815171717448186501)
                    ·
                      refine ⟨1076334527844697021534969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740450815171717448186501 1076334527844697021534969)
                      ·
                        rfl

theorem cell23_2096154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2096154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096154 prefixEnd_2096154 := by exact prefixLift 2096154
  have htrace : WordTrace (prefixWord ++ tailWord_2096154) baseStart_2096154 baseEnd_2096154 := by
    simpa [prefixWord, tailWord_2096154, baseEnd_2096154] using wordTrace_append hprefix tailTrace_2096154
  have hstable : (prefixWord ++ tailWord_2096154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096154).length < 2 ^ (prefixWord ++ tailWord_2096154).sum := by decide
  have hdescent : baseEnd_2096154 < baseStart_2096154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096181 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 5]
def baseStart_2096181 : Nat := 118140960795 + 2096181 * 2 ^ 59
def prefixEnd_2096181 : Nat := 4983230072969 + 3 ^ 40 * 2096181 * 2
def baseEnd_2096181 : Nat := 119594265758040935099705

theorem tailTrace_2096181 : CollatzResearch.WordTrace tailWord_2096181 prefixEnd_2096181 119594265758040935099705 := by
  unfold tailWord_2096181
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454002018901711058136397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50969334679267807372090931 76454002018901711058136397)
  ·
    refine ⟨28670250757088141646801149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76454002018901711058136397 28670250757088141646801149)
    ·
      refine ⟨10751344033908053117550431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28670250757088141646801149 10751344033908053117550431)
      ·
        refine ⟨16127016050862079676325647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751344033908053117550431 16127016050862079676325647)
        ·
          refine ⟨24190524076293119514488471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16127016050862079676325647 24190524076293119514488471)
          ·
            refine ⟨36285786114439679271732707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24190524076293119514488471 36285786114439679271732707)
            ·
              refine ⟨54428679171659518907599061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36285786114439679271732707 54428679171659518907599061)
              ·
                refine ⟨1275672168085769974396853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54428679171659518907599061 1275672168085769974396853)
                ·
                  refine ⟨119594265758040935099705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1275672168085769974396853 119594265758040935099705)
                  ·
                    rfl

theorem cell23_2096181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_2096181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096181 prefixEnd_2096181 := by exact prefixLift 2096181
  have htrace : WordTrace (prefixWord ++ tailWord_2096181) baseStart_2096181 baseEnd_2096181 := by
    simpa [prefixWord, tailWord_2096181, baseEnd_2096181] using wordTrace_append hprefix tailTrace_2096181
  have hstable : (prefixWord ++ tailWord_2096181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096181).length < 2 ^ (prefixWord ++ tailWord_2096181).sum := by decide
  have hdescent : baseEnd_2096181 < baseStart_2096181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096231 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2096231 : Nat := 118140960795 + 2096231 * 2 ^ 59
def prefixEnd_2096231 : Nat := 4983230072969 + 3 ^ 40 * 2096231 * 2
def baseEnd_2096231 : Nat := 1076374065855093220272115

theorem tailTrace_2096231 : CollatzResearch.WordTrace tailWord_2096231 prefixEnd_2096231 1076374065855093220272115 := by
  unfold tailWord_2096231
  simp only [CollatzResearch.WordTrace]
  refine ⟨76455825668720569597456547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50970550445813713064971031 76455825668720569597456547)
  ·
    refine ⟨114683738503080854396184821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76455825668720569597456547 114683738503080854396184821)
    ·
      refine ⟨10751600484663830099642327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114683738503080854396184821 10751600484663830099642327)
      ·
        refine ⟨16127400726995745149463491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751600484663830099642327 16127400726995745149463491)
        ·
          refine ⟨24191101090493617724195237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16127400726995745149463491 24191101090493617724195237)
          ·
            refine ⟨4535831454467553323286607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24191101090493617724195237 4535831454467553323286607)
            ·
              refine ⟨6803747181701329984929911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535831454467553323286607 6803747181701329984929911)
              ·
                refine ⟨10205620772551994977394867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803747181701329984929911 10205620772551994977394867)
                ·
                  refine ⟨15308431158827992466092301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205620772551994977394867 15308431158827992466092301)
                  ·
                    refine ⟨5740661684560497174784613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15308431158827992466092301 5740661684560497174784613)
                    ·
                      refine ⟨1076374065855093220272115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740661684560497174784613 1076374065855093220272115)
                      ·
                        rfl

theorem cell23_2096231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2096231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096231 prefixEnd_2096231 := by exact prefixLift 2096231
  have htrace : WordTrace (prefixWord ++ tailWord_2096231) baseStart_2096231 baseEnd_2096231 := by
    simpa [prefixWord, tailWord_2096231, baseEnd_2096231] using wordTrace_append hprefix tailTrace_2096231
  have hstable : (prefixWord ++ tailWord_2096231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096231).length < 2 ^ (prefixWord ++ tailWord_2096231).sum := by decide
  have hdescent : baseEnd_2096231 < baseStart_2096231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096251 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3]
def baseStart_2096251 : Nat := 118140960795 + 2096251 * 2 ^ 59
def prefixEnd_2096251 : Nat := 4983230072969 + 3 ^ 40 * 2096251 * 2
def baseEnd_2096251 : Nat := 1076384335468183142022023

theorem tailTrace_2096251 : CollatzResearch.WordTrace tailWord_2096251 prefixEnd_2096251 1076384335468183142022023 := by
  unfold tailWord_2096251
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456555128648113013184607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50971036752432075342123071 76456555128648113013184607)
  ·
    refine ⟨114684832692972169519776911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76456555128648113013184607 114684832692972169519776911)
    ·
      refine ⟨172027249039458254279665367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114684832692972169519776911 172027249039458254279665367)
      ·
        refine ⟨258040873559187381419498051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172027249039458254279665367 258040873559187381419498051)
        ·
          refine ⟨387061310338781072129247077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258040873559187381419498051 387061310338781072129247077)
          ·
            refine ⟨72573995688521451024233827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 387061310338781072129247077 72573995688521451024233827)
            ·
              refine ⟨108860993532782176536350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72573995688521451024233827 108860993532782176536350741)
              ·
                refine ⟨5102859071849164525141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108860993532782176536350741 5102859071849164525141441)
                ·
                  refine ⟨3827144303886873393856081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102859071849164525141441 3827144303886873393856081)
                  ·
                    refine ⟨2870358227915155045392061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827144303886873393856081 2870358227915155045392061)
                    ·
                      refine ⟨1076384335468183142022023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870358227915155045392061 1076384335468183142022023)
                      ·
                        rfl

theorem cell23_2096251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].length) (baseStart_2096251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096251 prefixEnd_2096251 := by exact prefixLift 2096251
  have htrace : WordTrace (prefixWord ++ tailWord_2096251) baseStart_2096251 baseEnd_2096251 := by
    simpa [prefixWord, tailWord_2096251, baseEnd_2096251] using wordTrace_append hprefix tailTrace_2096251
  have hstable : (prefixWord ++ tailWord_2096251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096251).length < 2 ^ (prefixWord ++ tailWord_2096251).sum := by decide
  have hdescent : baseEnd_2096251 < baseStart_2096251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096292 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_2096292 : Nat := 118140960795 + 2096292 * 2 ^ 59
def prefixEnd_2096292 : Nat := 4983230072969 + 3 ^ 40 * 2096292 * 2
def baseEnd_2096292 : Nat := 358801796058339160536445

theorem tailTrace_2096292 : CollatzResearch.WordTrace tailWord_2096292 prefixEnd_2096292 358801796058339160536445 := by
  unfold tailWord_2096292
  simp only [CollatzResearch.WordTrace]
  refine ⟨38229025260749788507713565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50972033680999718010284753 38229025260749788507713565)
  ·
    refine ⟨14335884472781170690392587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38229025260749788507713565 14335884472781170690392587)
    ·
      refine ⟨21503826709171756035588881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335884472781170690392587 21503826709171756035588881)
      ·
        refine ⟨16127870031878817026691661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21503826709171756035588881 16127870031878817026691661)
        ·
          refine ⟨6047951261954556385009373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16127870031878817026691661 6047951261954556385009373)
          ·
            refine ⟨2267981723232958644378515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047951261954556385009373 2267981723232958644378515)
            ·
              refine ⟨3401972584849437966567773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267981723232958644378515 3401972584849437966567773)
              ·
                refine ⟨1275739719318539237462915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3401972584849437966567773 1275739719318539237462915)
                ·
                  refine ⟨1913609578977808856194373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275739719318539237462915 1913609578977808856194373)
                  ·
                    refine ⟨358801796058339160536445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913609578977808856194373 358801796058339160536445)
                    ·
                      rfl

theorem cell23_2096292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_2096292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096292 prefixEnd_2096292 := by exact prefixLift 2096292
  have htrace : WordTrace (prefixWord ++ tailWord_2096292) baseStart_2096292 baseEnd_2096292 := by
    simpa [prefixWord, tailWord_2096292, baseEnd_2096292] using wordTrace_append hprefix tailTrace_2096292
  have hstable : (prefixWord ++ tailWord_2096292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096292).length < 2 ^ (prefixWord ++ tailWord_2096292).sum := by decide
  have hdescent : baseEnd_2096292 < baseStart_2096292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096322 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2096322 : Nat := 118140960795 + 2096322 * 2 ^ 59
def prefixEnd_2096322 : Nat := 4983230072969 + 3 ^ 40 * 2096322 * 2
def baseEnd_2096322 : Nat := 119602310288294707137133

theorem tailTrace_2096322 : CollatzResearch.WordTrace tailWord_2096322 prefixEnd_2096322 119602310288294707137133 := by
  unfold tailWord_2096322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114786177847723034754805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50972763140927261426012813 19114786177847723034754805)
  ·
    refine ⟨1792011204173224034508263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19114786177847723034754805 1792011204173224034508263)
    ·
      refine ⟨2688016806259836051762395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792011204173224034508263 2688016806259836051762395)
      ·
        refine ⟨4032025209389754077643593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688016806259836051762395 4032025209389754077643593)
        ·
          refine ⟨3024018907042315558232695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032025209389754077643593 3024018907042315558232695)
          ·
            refine ⟨4536028360563473337349043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024018907042315558232695 4536028360563473337349043)
            ·
              refine ⟨6804042540845210006023565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536028360563473337349043 6804042540845210006023565)
              ·
                refine ⟨2551515952816953752258837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6804042540845210006023565 2551515952816953752258837)
                ·
                  refine ⟨119602310288294707137133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2551515952816953752258837 119602310288294707137133)
                  ·
                    rfl

theorem cell23_2096322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2096322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096322 prefixEnd_2096322 := by exact prefixLift 2096322
  have htrace : WordTrace (prefixWord ++ tailWord_2096322) baseStart_2096322 baseEnd_2096322 := by
    simpa [prefixWord, tailWord_2096322, baseEnd_2096322] using wordTrace_append hprefix tailTrace_2096322
  have hstable : (prefixWord ++ tailWord_2096322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096322).length < 2 ^ (prefixWord ++ tailWord_2096322).sum := by decide
  have hdescent : baseEnd_2096322 < baseStart_2096322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096331 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 6, 4]
def baseStart_2096331 : Nat := 118140960795 + 2096331 * 2 ^ 59
def prefixEnd_2096331 : Nat := 4983230072969 + 3 ^ 40 * 2096331 * 2
def baseEnd_2096331 : Nat := 358808471306847609673885

theorem tailTrace_2096331 : CollatzResearch.WordTrace tailWord_2096331 prefixEnd_2096331 358808471306847609673885 := by
  unfold tailWord_2096331
  simp only [CollatzResearch.WordTrace]
  refine ⟨76459472968358286676096847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50972981978905524450731231 76459472968358286676096847)
  ·
    refine ⟨114689209452537430014145271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76459472968358286676096847 114689209452537430014145271)
    ·
      refine ⟨172033814178806145021217907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114689209452537430014145271 172033814178806145021217907)
      ·
        refine ⟨258050721268209217531826861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172033814178806145021217907 258050721268209217531826861)
        ·
          refine ⟨96769020475578456574435073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258050721268209217531826861 96769020475578456574435073)
          ·
            refine ⟨72576765356683842430826305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96769020475578456574435073 72576765356683842430826305)
            ·
              refine ⟨54432574017512881823119729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72576765356683842430826305 54432574017512881823119729)
              ·
                refine ⟨40824430513134661367339797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54432574017512881823119729 40824430513134661367339797)
                ·
                  refine ⟨1913645180303187251594053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40824430513134661367339797 1913645180303187251594053)
                  ·
                    refine ⟨358808471306847609673885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913645180303187251594053 358808471306847609673885)
                    ·
                      rfl

theorem cell23_2096331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 4].length) (baseStart_2096331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096331 prefixEnd_2096331 := by exact prefixLift 2096331
  have htrace : WordTrace (prefixWord ++ tailWord_2096331) baseStart_2096331 baseEnd_2096331 := by
    simpa [prefixWord, tailWord_2096331, baseEnd_2096331] using wordTrace_append hprefix tailTrace_2096331
  have hstable : (prefixWord ++ tailWord_2096331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096331).length < 2 ^ (prefixWord ++ tailWord_2096331).sum := by decide
  have hdescent : baseEnd_2096331 < baseStart_2096331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096338 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2096338 : Nat := 118140960795 + 2096338 * 2 ^ 59
def prefixEnd_2096338 : Nat := 4983230072969 + 3 ^ 40 * 2096338 * 2
def baseEnd_2096338 : Nat := 1076429008285124301634123

theorem tailTrace_2096338 : CollatzResearch.WordTrace tailWord_2096338 prefixEnd_2096338 1076429008285124301634123 := by
  unfold tailWord_2096338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114932069833231717900417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50973152186221951247734445 19114932069833231717900417)
  ·
    refine ⟨14336199052374923788425313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19114932069833231717900417 14336199052374923788425313)
    ·
      refine ⟨10752149289281192841318985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14336199052374923788425313 10752149289281192841318985)
      ·
        refine ⟨8064111966960894630989239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10752149289281192841318985 8064111966960894630989239)
        ·
          refine ⟨12096167950441341946483859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064111966960894630989239 12096167950441341946483859)
          ·
            refine ⟨18144251925662012919725789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096167950441341946483859 18144251925662012919725789)
            ·
              refine ⟨6804094472123254844897171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18144251925662012919725789 6804094472123254844897171)
              ·
                refine ⟨10206141708184882267345757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804094472123254844897171 10206141708184882267345757)
                ·
                  refine ⟨3827303140569330850254659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10206141708184882267345757 3827303140569330850254659)
                  ·
                    refine ⟨5740954710853996275381989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827303140569330850254659 5740954710853996275381989)
                    ·
                      refine ⟨1076429008285124301634123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740954710853996275381989 1076429008285124301634123)
                      ·
                        rfl

theorem cell23_2096338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2096338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096338 prefixEnd_2096338 := by exact prefixLift 2096338
  have htrace : WordTrace (prefixWord ++ tailWord_2096338) baseStart_2096338 baseEnd_2096338 := by
    simpa [prefixWord, tailWord_2096338, baseEnd_2096338] using wordTrace_append hprefix tailTrace_2096338
  have hstable : (prefixWord ++ tailWord_2096338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096338).length < 2 ^ (prefixWord ++ tailWord_2096338).sum := by decide
  have hdescent : baseEnd_2096338 < baseStart_2096338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096351 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2096351 : Nat := 118140960795 + 2096351 * 2 ^ 59
def prefixEnd_2096351 : Nat := 4983230072969 + 3 ^ 40 * 2096351 * 2
def baseEnd_2096351 : Nat := 1076435683533632750771563

theorem tailTrace_2096351 : CollatzResearch.WordTrace tailWord_2096351 prefixEnd_2096351 1076435683533632750771563 := by
  unfold tailWord_2096351
  simp only [CollatzResearch.WordTrace]
  refine ⟨76460202428285830091824907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50973468285523886727883271 76460202428285830091824907)
  ·
    refine ⟨114690303642428745137737361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76460202428285830091824907 114690303642428745137737361)
    ·
      refine ⟨86017727731821558853303021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114690303642428745137737361 86017727731821558853303021)
      ·
        refine ⟨32256647899433084569988633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86017727731821558853303021 32256647899433084569988633)
        ·
          refine ⟨24192485924574813427491475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32256647899433084569988633 24192485924574813427491475)
          ·
            refine ⟨36288728886862220141237213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24192485924574813427491475 36288728886862220141237213)
            ·
              refine ⟨13608273332573332552963955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36288728886862220141237213 13608273332573332552963955)
              ·
                refine ⟨20412409998859998829445933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608273332573332552963955 20412409998859998829445933)
                ·
                  refine ⟨7654653749572499561042225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20412409998859998829445933 7654653749572499561042225)
                  ·
                    refine ⟨5740990312179374670781669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7654653749572499561042225 5740990312179374670781669)
                    ·
                      refine ⟨1076435683533632750771563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5740990312179374670781669 1076435683533632750771563)
                      ·
                        rfl

theorem cell23_2096351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2096351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096351 prefixEnd_2096351 := by exact prefixLift 2096351
  have htrace : WordTrace (prefixWord ++ tailWord_2096351) baseStart_2096351 baseEnd_2096351 := by
    simpa [prefixWord, tailWord_2096351, baseEnd_2096351] using wordTrace_append hprefix tailTrace_2096351
  have hstable : (prefixWord ++ tailWord_2096351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096351).length < 2 ^ (prefixWord ++ tailWord_2096351).sum := by decide
  have hdescent : baseEnd_2096351 < baseStart_2096351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096365 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2096365 : Nat := 118140960795 + 2096365 * 2 ^ 59
def prefixEnd_2096365 : Nat := 4983230072969 + 3 ^ 40 * 2096365 * 2
def baseEnd_2096365 : Nat := 358814290754265231998833

theorem tailTrace_2096365 : CollatzResearch.WordTrace tailWord_2096365 prefixEnd_2096365 358814290754265231998833 := by
  unfold tailWord_2096365
  simp only [CollatzResearch.WordTrace]
  refine ⟨76460713050235110482834549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50973808700156740321889699 76460713050235110482834549)
  ·
    refine ⟨7168191848459541607765739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76460713050235110482834549 7168191848459541607765739)
    ·
      refine ⟨10752287772689312411648609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168191848459541607765739 10752287772689312411648609)
      ·
        refine ⟨8064215829516984308736457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10752287772689312411648609 8064215829516984308736457)
        ·
          refine ⟨6048161872137738231552343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8064215829516984308736457 6048161872137738231552343)
          ·
            refine ⟨9072242808206607347328515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048161872137738231552343 9072242808206607347328515)
            ·
              refine ⟨13608364212309911020992773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072242808206607347328515 13608364212309911020992773)
              ·
                refine ⟨2551568289808108316436145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13608364212309911020992773 2551568289808108316436145)
                ·
                  refine ⟨1913676217356081237327109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551568289808108316436145 1913676217356081237327109)
                  ·
                    refine ⟨358814290754265231998833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913676217356081237327109 358814290754265231998833)
                    ·
                      rfl

theorem cell23_2096365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2096365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096365 prefixEnd_2096365 := by exact prefixLift 2096365
  have htrace : WordTrace (prefixWord ++ tailWord_2096365) baseStart_2096365 baseEnd_2096365 := by
    simpa [prefixWord, tailWord_2096365, baseEnd_2096365] using wordTrace_append hprefix tailTrace_2096365
  have hstable : (prefixWord ++ tailWord_2096365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096365).length < 2 ^ (prefixWord ++ tailWord_2096365).sum := by decide
  have hdescent : baseEnd_2096365 < baseStart_2096365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096401 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_2096401 : Nat := 118140960795 + 2096401 * 2 ^ 59
def prefixEnd_2096401 : Nat := 4983230072969 + 3 ^ 40 * 2096401 * 2
def baseEnd_2096401 : Nat := 1076461357566357555146333

theorem tailTrace_2096401 : CollatzResearch.WordTrace tailWord_2096401 prefixEnd_2096401 1076461357566357555146333 := by
  unfold tailWord_2096401
  simp only [CollatzResearch.WordTrace]
  refine ⟨76462026078104688631145057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50974684052069792420763371 76462026078104688631145057)
  ·
    refine ⟨57346519558578516473358793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76462026078104688631145057 57346519558578516473358793)
    ·
      refine ⟨43009889668933887355019095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57346519558578516473358793 43009889668933887355019095)
      ·
        refine ⟨64514834503400831032528643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43009889668933887355019095 64514834503400831032528643)
        ·
          refine ⟨96772251755101246548792965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64514834503400831032528643 96772251755101246548792965)
          ·
            refine ⟨18144797204081483727898681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96772251755101246548792965 18144797204081483727898681)
            ·
              refine ⟨13608597903061112795924011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18144797204081483727898681 13608597903061112795924011)
              ·
                refine ⟨20412896854591669193886017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608597903061112795924011 20412896854591669193886017)
                ·
                  refine ⟨15309672640943751895414513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20412896854591669193886017 15309672640943751895414513)
                  ·
                    refine ⟨11482254480707813921560885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309672640943751895414513 11482254480707813921560885)
                    ·
                      refine ⟨1076461357566357555146333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11482254480707813921560885 1076461357566357555146333)
                      ·
                        rfl

theorem cell23_2096401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_2096401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096401 prefixEnd_2096401 := by exact prefixLift 2096401
  have htrace : WordTrace (prefixWord ++ tailWord_2096401) baseStart_2096401 baseEnd_2096401 := by
    simpa [prefixWord, tailWord_2096401, baseEnd_2096401] using wordTrace_append hprefix tailTrace_2096401
  have hstable : (prefixWord ++ tailWord_2096401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096401).length < 2 ^ (prefixWord ++ tailWord_2096401).sum := by decide
  have hdescent : baseEnd_2096401 < baseStart_2096401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096431 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_2096431 : Nat := 118140960795 + 2096431 * 2 ^ 59
def prefixEnd_2096431 : Nat := 4983230072969 + 3 ^ 40 * 2096431 * 2
def baseEnd_2096431 : Nat := 1076476761985992437771195

theorem tailTrace_2096431 : CollatzResearch.WordTrace tailWord_2096431 prefixEnd_2096431 1076476761985992437771195 := by
  unfold tailWord_2096431
  simp only [CollatzResearch.WordTrace]
  refine ⟨76463120267996003754737147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50975413511997335836491431 76463120267996003754737147)
  ·
    refine ⟨114694680401994005632105721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76463120267996003754737147 114694680401994005632105721)
    ·
      refine ⟨86021010301495504224079291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114694680401994005632105721 86021010301495504224079291)
      ·
        refine ⟨129031515452243256336118937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86021010301495504224079291 129031515452243256336118937)
        ·
          refine ⟨96773636589182442252089203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129031515452243256336118937 96773636589182442252089203)
          ·
            refine ⟨145160454883773663378133805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96773636589182442252089203 145160454883773663378133805)
            ·
              refine ⟨54435170581415123766800177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145160454883773663378133805 54435170581415123766800177)
              ·
                refine ⟨40826377936061342825100133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54435170581415123766800177 40826377936061342825100133)
                ·
                  refine ⟨7654945863011501779706275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40826377936061342825100133 7654945863011501779706275)
                  ·
                    refine ⟨11482418794517252669559413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654945863011501779706275 11482418794517252669559413)
                    ·
                      refine ⟨1076476761985992437771195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11482418794517252669559413 1076476761985992437771195)
                      ·
                        rfl

theorem cell23_2096431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_2096431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096431 prefixEnd_2096431 := by exact prefixLift 2096431
  have htrace : WordTrace (prefixWord ++ tailWord_2096431) baseStart_2096431 baseEnd_2096431 := by
    simpa [prefixWord, tailWord_2096431, baseEnd_2096431] using wordTrace_append hprefix tailTrace_2096431
  have hstable : (prefixWord ++ tailWord_2096431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096431).length < 2 ^ (prefixWord ++ tailWord_2096431).sum := by decide
  have hdescent : baseEnd_2096431 < baseStart_2096431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096449 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2096449 : Nat := 118140960795 + 2096449 * 2 ^ 59
def prefixEnd_2096449 : Nat := 4983230072969 + 3 ^ 40 * 2096449 * 2
def baseEnd_2096449 : Nat := 1076486004637773367346113

theorem tailTrace_2096449 : CollatzResearch.WordTrace tailWord_2096449 prefixEnd_2096449 1076486004637773367346113 := by
  unfold tailWord_2096449
  simp only [CollatzResearch.WordTrace]
  refine ⟨76463776781930792828892401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50975851187953861885928267 76463776781930792828892401)
  ·
    refine ⟨57347832586448094621669301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76463776781930792828892401 57347832586448094621669301)
    ·
      refine ⟨5376359304979508870781497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57347832586448094621669301 5376359304979508870781497)
      ·
        refine ⟨4032269478734631653086123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5376359304979508870781497 4032269478734631653086123)
        ·
          refine ⟨6048404218101947479629185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032269478734631653086123 6048404218101947479629185)
          ·
            refine ⟨4536303163576460609721889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6048404218101947479629185 4536303163576460609721889)
            ·
              refine ⟨3402227372682345457291417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536303163576460609721889 3402227372682345457291417)
              ·
                refine ⟨2551670529511759092968563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402227372682345457291417 2551670529511759092968563)
                ·
                  refine ⟨3827505794267638639452845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551670529511759092968563 3827505794267638639452845)
                  ·
                    refine ⟨1435314672850364489794817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827505794267638639452845 1435314672850364489794817)
                    ·
                      refine ⟨1076486004637773367346113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435314672850364489794817 1076486004637773367346113)
                      ·
                        rfl

theorem cell23_2096449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2096449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096449 prefixEnd_2096449 := by exact prefixLift 2096449
  have htrace : WordTrace (prefixWord ++ tailWord_2096449) baseStart_2096449 baseEnd_2096449 := by
    simpa [prefixWord, tailWord_2096449, baseEnd_2096449] using wordTrace_append hprefix tailTrace_2096449
  have hstable : (prefixWord ++ tailWord_2096449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096449).length < 2 ^ (prefixWord ++ tailWord_2096449).sum := by decide
  have hdescent : baseEnd_2096449 < baseStart_2096449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096498 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2096498 : Nat := 118140960795 + 2096498 * 2 ^ 59
def prefixEnd_2096498 : Nat := 4983230072969 + 3 ^ 40 * 2096498 * 2
def baseEnd_2096498 : Nat := 358837055063281225211129

theorem tailTrace_2096498 : CollatzResearch.WordTrace tailWord_2096498 prefixEnd_2096498 358837055063281225211129 := by
  unfold tailWord_2096498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116390989688318549356537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50977042639168849464950765 19116390989688318549356537)
  ·
    refine ⟨14337293242266238912017403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19116390989688318549356537 14337293242266238912017403)
    ·
      refine ⟨21505939863399358368026105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14337293242266238912017403 21505939863399358368026105)
      ·
        refine ⟨16129454897549518776019579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21505939863399358368026105 16129454897549518776019579)
        ·
          refine ⟨24194182346324278164029369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129454897549518776019579 24194182346324278164029369)
          ·
            refine ⟨18145636759743208623022027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24194182346324278164029369 18145636759743208623022027)
            ·
              refine ⟨27218455139614812934533041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18145636759743208623022027 27218455139614812934533041)
              ·
                refine ⟨20413841354711109700899781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27218455139614812934533041 20413841354711109700899781)
                ·
                  refine ⟨3827595254008333068918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20413841354711109700899781 3827595254008333068918709)
                  ·
                    refine ⟨358837055063281225211129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3827595254008333068918709 358837055063281225211129)
                    ·
                      rfl

theorem cell23_2096498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2096498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096498 prefixEnd_2096498 := by exact prefixLift 2096498
  have htrace : WordTrace (prefixWord ++ tailWord_2096498) baseStart_2096498 baseEnd_2096498 := by
    simpa [prefixWord, tailWord_2096498, baseEnd_2096498] using wordTrace_append hprefix tailTrace_2096498
  have hstable : (prefixWord ++ tailWord_2096498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096498).length < 2 ^ (prefixWord ++ tailWord_2096498).sum := by decide
  have hdescent : baseEnd_2096498 < baseStart_2096498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096515 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 2, 5]
def baseStart_2096515 : Nat := 118140960795 + 2096515 * 2 ^ 59
def prefixEnd_2096515 : Nat := 4983230072969 + 3 ^ 40 * 2096515 * 2
def baseEnd_2096515 : Nat := 358839964786990036373603

theorem tailTrace_2096515 : CollatzResearch.WordTrace tailWord_2096515 prefixEnd_2096515 358839964786990036373603 := by
  unfold tailWord_2096515
  simp only [CollatzResearch.WordTrace]
  refine ⟨76466183999691686100794999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50977455999794457400529999 76466183999691686100794999)
  ·
    refine ⟨114699275999537529151192499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76466183999691686100794999 114699275999537529151192499)
    ·
      refine ⟨172048913999306293726788749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114699275999537529151192499 172048913999306293726788749)
      ·
        refine ⟨64518342749739860147545781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172048913999306293726788749 64518342749739860147545781)
        ·
          refine ⟨6048594632788111888832417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64518342749739860147545781 6048594632788111888832417)
          ·
            refine ⟨4536445974591083916624313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6048594632788111888832417 4536445974591083916624313)
            ·
              refine ⟨3402334480943312937468235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536445974591083916624313 3402334480943312937468235)
              ·
                refine ⟨5103501721414969406202353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402334480943312937468235 5103501721414969406202353)
                ·
                  refine ⟨3827626291061227054651765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103501721414969406202353 3827626291061227054651765)
                  ·
                    refine ⟨358839964786990036373603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3827626291061227054651765 358839964786990036373603)
                    ·
                      rfl

theorem cell23_2096515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].length) (baseStart_2096515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096515 prefixEnd_2096515 := by exact prefixLift 2096515
  have htrace : WordTrace (prefixWord ++ tailWord_2096515) baseStart_2096515 baseEnd_2096515 := by
    simpa [prefixWord, tailWord_2096515, baseEnd_2096515] using wordTrace_append hprefix tailTrace_2096515
  have hstable : (prefixWord ++ tailWord_2096515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096515).length < 2 ^ (prefixWord ++ tailWord_2096515).sum := by decide
  have hdescent : baseEnd_2096515 < baseStart_2096515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096535 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_2096535 : Nat := 118140960795 + 2096535 * 2 ^ 59
def prefixEnd_2096535 : Nat := 4983230072969 + 3 ^ 40 * 2096535 * 2
def baseEnd_2096535 : Nat := 1076530163974060030870717

theorem tailTrace_2096535 : CollatzResearch.WordTrace tailWord_2096535 prefixEnd_2096535 1076530163974060030870717 := by
  unfold tailWord_2096535
  simp only [CollatzResearch.WordTrace]
  refine ⟨76466913459619229516523059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50977942306412819677682039 76466913459619229516523059)
  ·
    refine ⟨114700370189428844274784589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76466913459619229516523059 114700370189428844274784589)
    ·
      refine ⟨43012638821035816603044221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114700370189428844274784589 43012638821035816603044221)
      ·
        refine ⟨16129739557888431226141583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43012638821035816603044221 16129739557888431226141583)
        ·
          refine ⟨24194609336832646839212375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129739557888431226141583 24194609336832646839212375)
          ·
            refine ⟨36291914005248970258818563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24194609336832646839212375 36291914005248970258818563)
            ·
              refine ⟨54437871007873455388227845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36291914005248970258818563 54437871007873455388227845)
              ·
                refine ⟨10207100813976272885292721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54437871007873455388227845 10207100813976272885292721)
                ·
                  refine ⟨7655325610482204663969541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10207100813976272885292721 7655325610482204663969541)
                  ·
                    refine ⟨1435373551965413374494289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655325610482204663969541 1435373551965413374494289)
                    ·
                      refine ⟨1076530163974060030870717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435373551965413374494289 1076530163974060030870717)
                      ·
                        rfl

theorem cell23_2096535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_2096535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096535 prefixEnd_2096535 := by exact prefixLift 2096535
  have htrace : WordTrace (prefixWord ++ tailWord_2096535) baseStart_2096535 baseEnd_2096535 := by
    simpa [prefixWord, tailWord_2096535, baseEnd_2096535] using wordTrace_append hprefix tailTrace_2096535
  have hstable : (prefixWord ++ tailWord_2096535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096535).length < 2 ^ (prefixWord ++ tailWord_2096535).sum := by decide
  have hdescent : baseEnd_2096535 < baseStart_2096535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096536 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 5]
def baseStart_2096536 : Nat := 118140960795 + 2096536 * 2 ^ 59
def prefixEnd_2096536 : Nat := 4983230072969 + 3 ^ 40 * 2096536 * 2
def baseEnd_2096536 : Nat := 119614519717190502995357

theorem tailTrace_2096536 : CollatzResearch.WordTrace tailWord_2096536 prefixEnd_2096536 119614519717190502995357 := by
  unfold tailWord_2096536
  simp only [CollatzResearch.WordTrace]
  refine ⟨38233474966307803343654731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50977966621743737791539641 38233474966307803343654731)
  ·
    refine ⟨57350212449461705015482097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38233474966307803343654731 57350212449461705015482097)
    ·
      refine ⟨43012659337096278761611573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57350212449461705015482097 43012659337096278761611573)
      ·
        refine ⟨4032436812852776133901085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43012659337096278761611573 4032436812852776133901085)
        ·
          refine ⟨1512163804819791050212907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4032436812852776133901085 1512163804819791050212907)
          ·
            refine ⟨2268245707229686575319361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512163804819791050212907 2268245707229686575319361)
            ·
              refine ⟨1701184280422264931489521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268245707229686575319361 1701184280422264931489521)
              ·
                refine ⟨1275888210316698698617141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701184280422264931489521 1275888210316698698617141)
                ·
                  refine ⟨119614519717190502995357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1275888210316698698617141 119614519717190502995357)
                  ·
                    rfl

theorem cell23_2096536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 5].length) (baseStart_2096536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096536 prefixEnd_2096536 := by exact prefixLift 2096536
  have htrace : WordTrace (prefixWord ++ tailWord_2096536) baseStart_2096536 baseEnd_2096536 := by
    simpa [prefixWord, tailWord_2096536, baseEnd_2096536] using wordTrace_append hprefix tailTrace_2096536
  have hstable : (prefixWord ++ tailWord_2096536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096536).length < 2 ^ (prefixWord ++ tailWord_2096536).sum := by decide
  have hdescent : baseEnd_2096536 < baseStart_2096536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096538 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2096538 : Nat := 118140960795 + 2096538 * 2 ^ 59
def prefixEnd_2096538 : Nat := 4983230072969 + 3 ^ 40 * 2096538 * 2
def baseEnd_2096538 : Nat := 1076531704416023519133203

theorem tailTrace_2096538 : CollatzResearch.WordTrace tailWord_2096538 prefixEnd_2096538 1076531704416023519133203 := by
  unfold tailWord_2096538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116755719652090257220567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50978015252405574019254845 19116755719652090257220567)
  ·
    refine ⟨28675133579478135385830851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19116755719652090257220567 28675133579478135385830851)
    ·
      refine ⟨43012700369217203078746277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28675133579478135385830851 43012700369217203078746277)
      ·
        refine ⟨8064881319228225577264927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43012700369217203078746277 8064881319228225577264927)
        ·
          refine ⟨12097321978842338365897391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064881319228225577264927 12097321978842338365897391)
          ·
            refine ⟨18145982968263507548846087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097321978842338365897391 18145982968263507548846087)
            ·
              refine ⟨27218974452395261323269131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18145982968263507548846087 27218974452395261323269131)
              ·
                refine ⟨40828461678592891984903697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27218974452395261323269131 40828461678592891984903697)
                ·
                  refine ⟨30621346258944668988677773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40828461678592891984903697 30621346258944668988677773)
                  ·
                    refine ⟨11483004847104250870754165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30621346258944668988677773 11483004847104250870754165)
                    ·
                      refine ⟨1076531704416023519133203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11483004847104250870754165 1076531704416023519133203)
                      ·
                        rfl

theorem cell23_2096538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2096538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096538 prefixEnd_2096538 := by exact prefixLift 2096538
  have htrace : WordTrace (prefixWord ++ tailWord_2096538) baseStart_2096538 baseEnd_2096538 := by
    simpa [prefixWord, tailWord_2096538, baseEnd_2096538] using wordTrace_append hprefix tailTrace_2096538
  have hstable : (prefixWord ++ tailWord_2096538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096538).length < 2 ^ (prefixWord ++ tailWord_2096538).sum := by decide
  have hdescent : baseEnd_2096538 < baseStart_2096538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096548 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2096548 : Nat := 118140960795 + 2096548 * 2 ^ 59
def prefixEnd_2096548 : Nat := 4983230072969 + 3 ^ 40 * 2096548 * 2
def baseEnd_2096548 : Nat := 1076536839222568480008157

theorem tailTrace_2096548 : CollatzResearch.WordTrace tailWord_2096548 prefixEnd_2096548 1076536839222568480008157 := by
  unfold tailWord_2096548
  simp only [CollatzResearch.WordTrace]
  refine ⟨38233693804286066368373149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50978258405714755157830865 38233693804286066368373149)
  ·
    refine ⟨14337635176607274888139931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38233693804286066368373149 14337635176607274888139931)
    ·
      refine ⟨21506452764910912332209897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14337635176607274888139931 21506452764910912332209897)
      ·
        refine ⟨16129839573683184249157423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21506452764910912332209897 16129839573683184249157423)
        ·
          refine ⟨24194759360524776373736135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129839573683184249157423 24194759360524776373736135)
          ·
            refine ⟨36292139040787164560604203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24194759360524776373736135 36292139040787164560604203)
            ·
              refine ⟨54438208561180746840906305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36292139040787164560604203 54438208561180746840906305)
              ·
                refine ⟨40828656420885560130679729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54438208561180746840906305 40828656420885560130679729)
                ·
                  refine ⟨30621492315664170098009797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40828656420885560130679729 30621492315664170098009797)
                  ·
                    refine ⟨5741529809187031893376837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30621492315664170098009797 5741529809187031893376837)
                    ·
                      refine ⟨1076536839222568480008157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5741529809187031893376837 1076536839222568480008157)
                      ·
                        rfl

theorem cell23_2096548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2096548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096548 prefixEnd_2096548 := by exact prefixLift 2096548
  have htrace : WordTrace (prefixWord ++ tailWord_2096548) baseStart_2096548 baseEnd_2096548 := by
    simpa [prefixWord, tailWord_2096548, baseEnd_2096548] using wordTrace_append hprefix tailTrace_2096548
  have hstable : (prefixWord ++ tailWord_2096548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096548).length < 2 ^ (prefixWord ++ tailWord_2096548).sum := by decide
  have hdescent : baseEnd_2096548 < baseStart_2096548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096569 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2096569 : Nat := 118140960795 + 2096569 * 2 ^ 59
def prefixEnd_2096569 : Nat := 4983230072969 + 3 ^ 40 * 2096569 * 2
def baseEnd_2096569 : Nat := 1076547622316312897845561

theorem tailTrace_2096569 : CollatzResearch.WordTrace tailWord_2096569 prefixEnd_2096569 1076547622316312897845561 := by
  unfold tailWord_2096569
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468153541496053323260761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50978769027664035548840507 76468153541496053323260761)
  ·
    refine ⟨57351115156122039992445571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76468153541496053323260761 57351115156122039992445571)
    ·
      refine ⟨86026672734183059988668357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57351115156122039992445571 86026672734183059988668357)
      ·
        refine ⟨16130001137659323747875317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86026672734183059988668357 16130001137659323747875317)
        ·
          refine ⟨1512187606655561601363311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16130001137659323747875317 1512187606655561601363311)
          ·
            refine ⟨2268281409983342402044967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512187606655561601363311 2268281409983342402044967)
            ·
              refine ⟨3402422114975013603067451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268281409983342402044967 3402422114975013603067451)
              ·
                refine ⟨5103633172462520404601177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402422114975013603067451 5103633172462520404601177)
                ·
                  refine ⟨3827724879346890303450883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103633172462520404601177 3827724879346890303450883)
                  ·
                    refine ⟨5741587319020335455176325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827724879346890303450883 5741587319020335455176325)
                    ·
                      refine ⟨1076547622316312897845561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5741587319020335455176325 1076547622316312897845561)
                      ·
                        rfl

theorem cell23_2096569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2096569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096569 prefixEnd_2096569 := by exact prefixLift 2096569
  have htrace : WordTrace (prefixWord ++ tailWord_2096569) baseStart_2096569 baseEnd_2096569 := by
    simpa [prefixWord, tailWord_2096569, baseEnd_2096569] using wordTrace_append hprefix tailTrace_2096569
  have hstable : (prefixWord ++ tailWord_2096569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096569).length < 2 ^ (prefixWord ++ tailWord_2096569).sum := by decide
  have hdescent : baseEnd_2096569 < baseStart_2096569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096572 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2096572 : Nat := 118140960795 + 2096572 * 2 ^ 59
def prefixEnd_2096572 : Nat := 4983230072969 + 3 ^ 40 * 2096572 * 2
def baseEnd_2096572 : Nat := 1076549162758276386108047

theorem tailTrace_2096572 : CollatzResearch.WordTrace tailWord_2096572 prefixEnd_2096572 1076549162758276386108047 := by
  unfold tailWord_2096572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234131480242592417809985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50978841973656789890413313 38234131480242592417809985)
  ·
    refine ⟨28675598610181944313357489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38234131480242592417809985 28675598610181944313357489)
    ·
      refine ⟨21506698957636458235018117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28675598610181944313357489 21506698957636458235018117)
      ·
        refine ⟨4032506054556835919065897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21506698957636458235018117 4032506054556835919065897)
        ·
          refine ⟨3024379540917626939299423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032506054556835919065897 3024379540917626939299423)
          ·
            refine ⟨4536569311376440408949135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024379540917626939299423 4536569311376440408949135)
            ·
              refine ⟨6804853967064660613423703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536569311376440408949135 6804853967064660613423703)
              ·
                refine ⟨10207280950596990920135555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804853967064660613423703 10207280950596990920135555)
                ·
                  refine ⟨15310921425895486380203333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207280950596990920135555 15310921425895486380203333)
                  ·
                    refine ⟨2870797767355403696288125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15310921425895486380203333 2870797767355403696288125)
                    ·
                      refine ⟨1076549162758276386108047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870797767355403696288125 1076549162758276386108047)
                      ·
                        rfl

theorem cell23_2096572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2096572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096572 prefixEnd_2096572 := by exact prefixLift 2096572
  have htrace : WordTrace (prefixWord ++ tailWord_2096572) baseStart_2096572 baseEnd_2096572 := by
    simpa [prefixWord, tailWord_2096572, baseEnd_2096572] using wordTrace_append hprefix tailTrace_2096572
  have hstable : (prefixWord ++ tailWord_2096572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096572).length < 2 ^ (prefixWord ++ tailWord_2096572).sum := by decide
  have hdescent : baseEnd_2096572 < baseStart_2096572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096585 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_2096585 : Nat := 118140960795 + 2096585 * 2 ^ 59
def prefixEnd_2096585 : Nat := 4983230072969 + 3 ^ 40 * 2096585 * 2
def baseEnd_2096585 : Nat := 1076555838006784835245487

theorem tailTrace_2096585 : CollatzResearch.WordTrace tailWord_2096585 prefixEnd_2096585 1076555838006784835245487 := by
  unfold tailWord_2096585
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468737109438088055843209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50979158072958725370562139 76468737109438088055843209)
  ·
    refine ⟨57351552832078566041882407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76468737109438088055843209 57351552832078566041882407)
    ·
      refine ⟨86027329248117849062823611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57351552832078566041882407 86027329248117849062823611)
      ·
        refine ⟨129040993872176773594235417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86027329248117849062823611 129040993872176773594235417)
        ·
          refine ⟨96780745404132580195676563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129040993872176773594235417 96780745404132580195676563)
          ·
            refine ⟨145171118106198870293514845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96780745404132580195676563 145171118106198870293514845)
            ·
              refine ⟨54439169289824576360068067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145171118106198870293514845 54439169289824576360068067)
              ·
                refine ⟨81658753934736864540102101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54439169289824576360068067 81658753934736864540102101)
                ·
                  refine ⟨1913877045345395262658643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81658753934736864540102101 1913877045345395262658643)
                  ·
                    refine ⟨2870815568018092893987965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913877045345395262658643 2870815568018092893987965)
                    ·
                      refine ⟨1076555838006784835245487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870815568018092893987965 1076555838006784835245487)
                      ·
                        rfl

theorem cell23_2096585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_2096585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096585 prefixEnd_2096585 := by exact prefixLift 2096585
  have htrace : WordTrace (prefixWord ++ tailWord_2096585) baseStart_2096585 baseEnd_2096585 := by
    simpa [prefixWord, tailWord_2096585, baseEnd_2096585] using wordTrace_append hprefix tailTrace_2096585
  have hstable : (prefixWord ++ tailWord_2096585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096585).length < 2 ^ (prefixWord ++ tailWord_2096585).sum := by decide
  have hdescent : baseEnd_2096585 < baseStart_2096585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096602 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_2096602 : Nat := 118140960795 + 2096602 * 2 ^ 59
def prefixEnd_2096602 : Nat := 4983230072969 + 3 ^ 40 * 2096602 * 2
def baseEnd_2096602 : Nat := 1076564567177911268732909

theorem tailTrace_2096602 : CollatzResearch.WordTrace tailWord_2096602 prefixEnd_2096602 1076564567177911268732909 := by
  unfold tailWord_2096602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117339287594124989803015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50979571433584333306141373 19117339287594124989803015)
  ·
    refine ⟨28676008931391187484704523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19117339287594124989803015 28676008931391187484704523)
    ·
      refine ⟨43014013397086781227056785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28676008931391187484704523 43014013397086781227056785)
      ·
        refine ⟨32260510047815085920292589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43014013397086781227056785 32260510047815085920292589)
        ·
          refine ⟨12097691267930657220109721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32260510047815085920292589 12097691267930657220109721)
          ·
            refine ⟨9073268450947992915082291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12097691267930657220109721 9073268450947992915082291)
            ·
              refine ⟨13609902676421989372623437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073268450947992915082291 13609902676421989372623437)
              ·
                refine ⟨5103713503658246014733789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13609902676421989372623437 5103713503658246014733789)
                ·
                  refine ⟨1913892563871842255525171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5103713503658246014733789 1913892563871842255525171)
                  ·
                    refine ⟨2870838845807763383287757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913892563871842255525171 2870838845807763383287757)
                    ·
                      refine ⟨1076564567177911268732909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870838845807763383287757 1076564567177911268732909)
                      ·
                        rfl

theorem cell23_2096602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_2096602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096602 prefixEnd_2096602 := by exact prefixLift 2096602
  have htrace : WordTrace (prefixWord ++ tailWord_2096602) baseStart_2096602 baseEnd_2096602 := by
    simpa [prefixWord, tailWord_2096602, baseEnd_2096602] using wordTrace_append hprefix tailTrace_2096602
  have hstable : (prefixWord ++ tailWord_2096602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096602).length < 2 ^ (prefixWord ++ tailWord_2096602).sum := by decide
  have hdescent : baseEnd_2096602 < baseStart_2096602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096608 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2096608 : Nat := 118140960795 + 2096608 * 2 ^ 59
def prefixEnd_2096608 : Nat := 4983230072969 + 3 ^ 40 * 2096608 * 2
def baseEnd_2096608 : Nat := 1076567648061838245257881

theorem tailTrace_2096608 : CollatzResearch.WordTrace tailWord_2096608 prefixEnd_2096608 1076567648061838245257881 := by
  unfold tailWord_2096608
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234787994177381491965239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50979717325569841989286985 38234787994177381491965239)
  ·
    refine ⟨57352181991266072237947859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38234787994177381491965239 57352181991266072237947859)
    ·
      refine ⟨86028272986899108356921789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57352181991266072237947859 86028272986899108356921789)
      ·
        refine ⟨32260602370087165633845671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86028272986899108356921789 32260602370087165633845671)
        ·
          refine ⟨48390903555130748450768507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32260602370087165633845671 48390903555130748450768507)
          ·
            refine ⟨72586355332696122676152761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48390903555130748450768507 72586355332696122676152761)
            ·
              refine ⟨54439766499522092007114571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72586355332696122676152761 54439766499522092007114571)
              ·
                refine ⟨81659649749283138010671857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54439766499522092007114571 81659649749283138010671857)
                ·
                  refine ⟨61244737311962353508003893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81659649749283138010671857 61244737311962353508003893)
                  ·
                    refine ⟨5741694122996470641375365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61244737311962353508003893 5741694122996470641375365)
                    ·
                      refine ⟨1076567648061838245257881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5741694122996470641375365 1076567648061838245257881)
                      ·
                        rfl

theorem cell23_2096608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2096608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096608 prefixEnd_2096608 := by exact prefixLift 2096608
  have htrace : WordTrace (prefixWord ++ tailWord_2096608) baseStart_2096608 baseEnd_2096608 := by
    simpa [prefixWord, tailWord_2096608, baseEnd_2096608] using wordTrace_append hprefix tailTrace_2096608
  have hstable : (prefixWord ++ tailWord_2096608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096608).length < 2 ^ (prefixWord ++ tailWord_2096608).sum := by decide
  have hdescent : baseEnd_2096608 < baseStart_2096608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096622 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2096622 : Nat := 118140960795 + 2096622 * 2 ^ 59
def prefixEnd_2096622 : Nat := 4983230072969 + 3 ^ 40 * 2096622 * 2
def baseEnd_2096622 : Nat := 358858278930333730160939

theorem tailTrace_2096622 : CollatzResearch.WordTrace tailWord_2096622 prefixEnd_2096622 358858278930333730160939 := by
  unfold tailWord_2096622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558760826288005421867515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50980057740202695583293413 9558760826288005421867515)
  ·
    refine ⟨14338141239432008132801273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9558760826288005421867515 14338141239432008132801273)
    ·
      refine ⟨10753605929574006099600955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14338141239432008132801273 10753605929574006099600955)
      ·
        refine ⟨16130408894361009149401433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753605929574006099600955 16130408894361009149401433)
        ·
          refine ⟨12097806670770756862051075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130408894361009149401433 12097806670770756862051075)
          ·
            refine ⟨18146710006156135293076613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097806670770756862051075 18146710006156135293076613)
            ·
              refine ⟨3402508126154275367451865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18146710006156135293076613 3402508126154275367451865)
              ·
                refine ⟨2551881094615706525588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402508126154275367451865 2551881094615706525588899)
                ·
                  refine ⟨3827821641923559788383349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551881094615706525588899 3827821641923559788383349)
                  ·
                    refine ⟨358858278930333730160939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3827821641923559788383349 358858278930333730160939)
                    ·
                      rfl

theorem cell23_2096622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2096622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096622 prefixEnd_2096622 := by exact prefixLift 2096622
  have htrace : WordTrace (prefixWord ++ tailWord_2096622) baseStart_2096622 baseEnd_2096622 := by
    simpa [prefixWord, tailWord_2096622, baseEnd_2096622] using wordTrace_append hprefix tailTrace_2096622
  have hstable : (prefixWord ++ tailWord_2096622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096622).length < 2 ^ (prefixWord ++ tailWord_2096622).sum := by decide
  have hdescent : baseEnd_2096622 < baseStart_2096622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096629 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2096629 : Nat := 118140960795 + 2096629 * 2 ^ 59
def prefixEnd_2096629 : Nat := 4983230072969 + 3 ^ 40 * 2096629 * 2
def baseEnd_2096629 : Nat := 1076578431155582663095285

theorem tailTrace_2096629 : CollatzResearch.WordTrace tailWord_2096629 prefixEnd_2096629 1076578431155582663095285 := by
  unfold tailWord_2096629
  simp only [CollatzResearch.WordTrace]
  refine ⟨76470341921278683570444941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50980227947519122380296627 76470341921278683570444941)
  ·
    refine ⟨28676378220479506338916853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76470341921278683570444941 28676378220479506338916853)
    ·
      refine ⟨2688410458169953719273455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28676378220479506338916853 2688410458169953719273455)
      ·
        refine ⟨4032615687254930578910183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688410458169953719273455 4032615687254930578910183)
        ·
          refine ⟨6048923530882395868365275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032615687254930578910183 6048923530882395868365275)
          ·
            refine ⟨9073385296323593802547913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048923530882395868365275 9073385296323593802547913)
            ·
              refine ⟨6805038972242695351910935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9073385296323593802547913 6805038972242695351910935)
              ·
                refine ⟨10207558458364043027866403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805038972242695351910935 10207558458364043027866403)
                ·
                  refine ⟨15311337687546064541799605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207558458364043027866403 15311337687546064541799605)
                  ·
                    refine ⟨1435437908207443550793713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15311337687546064541799605 1435437908207443550793713)
                    ·
                      refine ⟨1076578431155582663095285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435437908207443550793713 1076578431155582663095285)
                      ·
                        rfl

theorem cell23_2096629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2096629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096629 prefixEnd_2096629 := by exact prefixLift 2096629
  have htrace : WordTrace (prefixWord ++ tailWord_2096629) baseStart_2096629 baseEnd_2096629 := by
    simpa [prefixWord, tailWord_2096629, baseEnd_2096629] using wordTrace_append hprefix tailTrace_2096629
  have hstable : (prefixWord ++ tailWord_2096629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096629).length < 2 ^ (prefixWord ++ tailWord_2096629).sum := by decide
  have hdescent : baseEnd_2096629 < baseStart_2096629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096645 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_2096645 : Nat := 118140960795 + 2096645 * 2 ^ 59
def prefixEnd_2096645 : Nat := 4983230072969 + 3 ^ 40 * 2096645 * 2
def baseEnd_2096645 : Nat := 1076586646846054600495211

theorem tailTrace_2096645 : CollatzResearch.WordTrace tailWord_2096645 prefixEnd_2096645 1076586646846054600495211 := by
  unfold tailWord_2096645
  simp only [CollatzResearch.WordTrace]
  refine ⟨76470925489220718303027389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50980616992813812202018259 76470925489220718303027389)
  ·
    refine ⟨28676597058457769363635271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76470925489220718303027389 28676597058457769363635271)
    ·
      refine ⟨43014895587686654045452907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28676597058457769363635271 43014895587686654045452907)
      ·
        refine ⟨64522343381529981068179361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43014895587686654045452907 64522343381529981068179361)
        ·
          refine ⟨48391757536147485801134521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64522343381529981068179361 48391757536147485801134521)
          ·
            refine ⟨36293818152110614350850891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48391757536147485801134521 36293818152110614350850891)
            ·
              refine ⟨54440727228165921526276337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36293818152110614350850891 54440727228165921526276337)
              ·
                refine ⟨40830545421124441144707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54440727228165921526276337 40830545421124441144707253)
                ·
                  refine ⟨3827863633230416357316305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40830545421124441144707253 3827863633230416357316305)
                  ·
                    refine ⟨2870897724922812267987229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827863633230416357316305 2870897724922812267987229)
                    ·
                      refine ⟨1076586646846054600495211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870897724922812267987229 1076586646846054600495211)
                      ·
                        rfl

theorem cell23_2096645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_2096645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096645 prefixEnd_2096645 := by exact prefixLift 2096645
  have htrace : WordTrace (prefixWord ++ tailWord_2096645) baseStart_2096645 baseEnd_2096645 := by
    simpa [prefixWord, tailWord_2096645, baseEnd_2096645] using wordTrace_append hprefix tailTrace_2096645
  have hstable : (prefixWord ++ tailWord_2096645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096645).length < 2 ^ (prefixWord ++ tailWord_2096645).sum := by decide
  have hdescent : baseEnd_2096645 < baseStart_2096645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096648 : List Nat := [2, 1, 3, 2, 1, 1, 13]
def baseStart_2096648 : Nat := 118140960795 + 2096648 * 2 ^ 59
def prefixEnd_2096648 : Nat := 4983230072969 + 3 ^ 40 * 2096648 * 2
def baseEnd_2096648 : Nat := 13291212188740964058737

theorem tailTrace_2096648 : CollatzResearch.WordTrace tailWord_2096648 prefixEnd_2096648 13291212188740964058737 := by
  unfold tailWord_2096648
  simp only [CollatzResearch.WordTrace]
  refine ⟨38235517454104924907693299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50980689938806566543591065 38235517454104924907693299)
  ·
    refine ⟨57353276181157387361539949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38235517454104924907693299 57353276181157387361539949)
    ·
      refine ⟨21507478567934020260577481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57353276181157387361539949 21507478567934020260577481)
      ·
        refine ⟨16130608925950515195433111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507478567934020260577481 16130608925950515195433111)
        ·
          refine ⟨24195913388925772793149667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130608925950515195433111 24195913388925772793149667)
          ·
            refine ⟨36293870083388659189724501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24195913388925772793149667 36293870083388659189724501)
            ·
              refine ⟨13291212188740964058737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 36293870083388659189724501 13291212188740964058737)
              ·
                rfl

theorem cell23_2096648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 13].length) (baseStart_2096648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096648 prefixEnd_2096648 := by exact prefixLift 2096648
  have htrace : WordTrace (prefixWord ++ tailWord_2096648) baseStart_2096648 baseEnd_2096648 := by
    simpa [prefixWord, tailWord_2096648, baseEnd_2096648] using wordTrace_append hprefix tailTrace_2096648
  have hstable : (prefixWord ++ tailWord_2096648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096648).length < 2 ^ (prefixWord ++ tailWord_2096648).sum := by decide
  have hdescent : baseEnd_2096648 < baseStart_2096648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096659 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 3, 2, 2]
def baseStart_2096659 : Nat := 118140960795 + 2096659 * 2 ^ 59
def prefixEnd_2096659 : Nat := 4983230072969 + 3 ^ 40 * 2096659 * 2
def baseEnd_2096659 : Nat := 1076593835575217545720147

theorem tailTrace_2096659 : CollatzResearch.WordTrace tailWord_2096659 prefixEnd_2096659 1076593835575217545720147 := by
  unfold tailWord_2096659
  simp only [CollatzResearch.WordTrace]
  refine ⟨76471436111169998694037031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50980957407446665796024687 76471436111169998694037031)
  ·
    refine ⟨114707154166754998041055547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76471436111169998694037031 114707154166754998041055547)
    ·
      refine ⟨172060731250132497061583321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114707154166754998041055547 172060731250132497061583321)
      ·
        refine ⟨129045548437599372796187491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172060731250132497061583321 129045548437599372796187491)
        ·
          refine ⟨193568322656399059194281237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129045548437599372796187491 193568322656399059194281237)
          ·
            refine ⟨9073515124518705899731933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193568322656399059194281237 9073515124518705899731933)
            ·
              refine ⟨3402568171694514712399475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9073515124518705899731933 3402568171694514712399475)
              ·
                refine ⟨5103852257541772068599213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402568171694514712399475 5103852257541772068599213)
                ·
                  refine ⟨1913944596578164525724705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5103852257541772068599213 1913944596578164525724705)
                  ·
                    refine ⟨1435458447433623394293529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913944596578164525724705 1435458447433623394293529)
                    ·
                      refine ⟨1076593835575217545720147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435458447433623394293529 1076593835575217545720147)
                      ·
                        rfl

theorem cell23_2096659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2, 2].length) (baseStart_2096659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096659 prefixEnd_2096659 := by exact prefixLift 2096659
  have htrace : WordTrace (prefixWord ++ tailWord_2096659) baseStart_2096659 baseEnd_2096659 := by
    simpa [prefixWord, tailWord_2096659, baseEnd_2096659] using wordTrace_append hprefix tailTrace_2096659
  have hstable : (prefixWord ++ tailWord_2096659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096659).length < 2 ^ (prefixWord ++ tailWord_2096659).sum := by decide
  have hdescent : baseEnd_2096659 < baseStart_2096659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096709 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_2096709 : Nat := 118140960795 + 2096709 * 2 ^ 59
def prefixEnd_2096709 : Nat := 4983230072969 + 3 ^ 40 * 2096709 * 2
def baseEnd_2096709 : Nat := 1076619509607942350094917

theorem tailTrace_2096709 : CollatzResearch.WordTrace tailWord_2096709 prefixEnd_2096709 1076619509607942350094917 := by
  unfold tailWord_2096709
  simp only [CollatzResearch.WordTrace]
  refine ⟨76473259760988857233357181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50982173173992571488904787 76473259760988857233357181)
  ·
    refine ⟨28677472410370821462508943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76473259760988857233357181 28677472410370821462508943)
    ·
      refine ⟨43016208615556232193763415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28677472410370821462508943 43016208615556232193763415)
      ·
        refine ⟨64524312923334348290645123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43016208615556232193763415 64524312923334348290645123)
        ·
          refine ⟨96786469385001522435967685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64524312923334348290645123 96786469385001522435967685)
          ·
            refine ⟨18147463009687785456743941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96786469385001522435967685 18147463009687785456743941)
            ·
              refine ⟨3402649314316459773139489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18147463009687785456743941 3402649314316459773139489)
              ·
                refine ⟨2551986985737344829854617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402649314316459773139489 2551986985737344829854617)
                ·
                  refine ⟨1913990239303008622390963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551986985737344829854617 1913990239303008622390963)
                  ·
                    refine ⟨2870985358954512933586445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913990239303008622390963 2870985358954512933586445)
                    ·
                      refine ⟨1076619509607942350094917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2870985358954512933586445 1076619509607942350094917)
                      ·
                        rfl

theorem cell23_2096709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_2096709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096709 prefixEnd_2096709 := by exact prefixLift 2096709
  have htrace : WordTrace (prefixWord ++ tailWord_2096709) baseStart_2096709 baseEnd_2096709 := by
    simpa [prefixWord, tailWord_2096709, baseEnd_2096709] using wordTrace_append hprefix tailTrace_2096709
  have hstable : (prefixWord ++ tailWord_2096709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096709).length < 2 ^ (prefixWord ++ tailWord_2096709).sum := by decide
  have hdescent : baseEnd_2096709 < baseStart_2096709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096785 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2096785 : Nat := 118140960795 + 2096785 * 2 ^ 59
def prefixEnd_2096785 : Nat := 4983230072969 + 3 ^ 40 * 2096785 * 2
def baseEnd_2096785 : Nat := 358886178045894684248189

theorem tailTrace_2096785 : CollatzResearch.WordTrace tailWord_2096785 prefixEnd_2096785 358886178045894684248189 := by
  unfold tailWord_2096785
  simp only [CollatzResearch.WordTrace]
  refine ⟨76476031708713522213123809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50984021139142348142082539 76476031708713522213123809)
  ·
    refine ⟨57357023781535141659842857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76476031708713522213123809 57357023781535141659842857)
    ·
      refine ⟨43017767836151356244882143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57357023781535141659842857 43017767836151356244882143)
      ·
        refine ⟨64526651754227034367323215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43017767836151356244882143 64526651754227034367323215)
        ·
          refine ⟨96789977631340551550984823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64526651754227034367323215 96789977631340551550984823)
          ·
            refine ⟨145184966447010827326477235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96789977631340551550984823 145184966447010827326477235)
            ·
              refine ⟨217777449670516240989715853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145184966447010827326477235 217777449670516240989715853)
              ·
                refine ⟨81666543626443590371143445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217777449670516240989715853 81666543626443590371143445)
                ·
                  refine ⟨3828119232489543298647349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81666543626443590371143445 3828119232489543298647349)
                  ·
                    refine ⟨358886178045894684248189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3828119232489543298647349 358886178045894684248189)
                    ·
                      rfl

theorem cell23_2096785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2096785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096785 prefixEnd_2096785 := by exact prefixLift 2096785
  have htrace : WordTrace (prefixWord ++ tailWord_2096785) baseStart_2096785 baseEnd_2096785 := by
    simpa [prefixWord, tailWord_2096785, baseEnd_2096785] using wordTrace_append hprefix tailTrace_2096785
  have hstable : (prefixWord ++ tailWord_2096785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096785).length < 2 ^ (prefixWord ++ tailWord_2096785).sum := by decide
  have hdescent : baseEnd_2096785 < baseStart_2096785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096882 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2096882 : Nat := 118140960795 + 2096882 * 2 ^ 59
def prefixEnd_2096882 : Nat := 4983230072969 + 3 ^ 40 * 2096882 * 2
def baseEnd_2096882 : Nat := 1076708341761170173231621

theorem tailTrace_2096882 : CollatzResearch.WordTrace tailWord_2096882 prefixEnd_2096882 1076708341761170173231621 := by
  unfold tailWord_2096882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119892397340526944851225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50986379726241405186269933 19119892397340526944851225)
  ·
    refine ⟨14339919298005395208638419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19119892397340526944851225 14339919298005395208638419)
    ·
      refine ⟨21509878947008092812957629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14339919298005395208638419 21509878947008092812957629)
      ·
        refine ⟨8066204605128034804859111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21509878947008092812957629 8066204605128034804859111)
        ·
          refine ⟨12099306907692052207288667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066204605128034804859111 12099306907692052207288667)
          ·
            refine ⟨18148960361538078310933001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099306907692052207288667 18148960361538078310933001)
            ·
              refine ⟨13611720271153558733199751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18148960361538078310933001 13611720271153558733199751)
              ·
                refine ⟨20417580406730338099799627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13611720271153558733199751 20417580406730338099799627)
                ·
                  refine ⟨30626370610095507149699441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20417580406730338099799627 30626370610095507149699441)
                  ·
                    refine ⟨22969777957571630362274581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30626370610095507149699441 22969777957571630362274581)
                    ·
                      refine ⟨1076708341761170173231621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22969777957571630362274581 1076708341761170173231621)
                      ·
                        rfl

theorem cell23_2096882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2096882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096882 prefixEnd_2096882 := by exact prefixLift 2096882
  have htrace : WordTrace (prefixWord ++ tailWord_2096882) baseStart_2096882 baseEnd_2096882 := by
    simpa [prefixWord, tailWord_2096882, baseEnd_2096882] using wordTrace_append hprefix tailTrace_2096882
  have hstable : (prefixWord ++ tailWord_2096882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096882).length < 2 ^ (prefixWord ++ tailWord_2096882).sum := by decide
  have hdescent : baseEnd_2096882 < baseStart_2096882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096892 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_2096892 : Nat := 118140960795 + 2096892 * 2 ^ 59
def prefixEnd_2096892 : Nat := 4983230072969 + 3 ^ 40 * 2096892 * 2
def baseEnd_2096892 : Nat := 358904492189238378035525

theorem tailTrace_2096892 : CollatzResearch.WordTrace tailWord_2096892 prefixEnd_2096892 358904492189238378035525 := by
  unfold tailWord_2096892
  simp only [CollatzResearch.WordTrace]
  refine ⟨38239967159662939743634465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50986622879550586324845953 38239967159662939743634465)
  ·
    refine ⟨28679975369747204807725849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38239967159662939743634465 28679975369747204807725849)
    ·
      refine ⟨21509981527310403605794387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28679975369747204807725849 21509981527310403605794387)
      ·
        refine ⟨32264972290965605408691581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21509981527310403605794387 32264972290965605408691581)
        ·
          refine ⟨12099364609112102028259343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32264972290965605408691581 12099364609112102028259343)
          ·
            refine ⟨18149046913668153042389015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099364609112102028259343 18149046913668153042389015)
            ·
              refine ⟨27223570370502229563583523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149046913668153042389015 27223570370502229563583523)
              ·
                refine ⟨40835355555753344345375285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27223570370502229563583523 40835355555753344345375285)
                ·
                  refine ⟨3828314583351876032378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40835355555753344345375285 3828314583351876032378933)
                  ·
                    refine ⟨358904492189238378035525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3828314583351876032378933 358904492189238378035525)
                    ·
                      rfl

theorem cell23_2096892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_2096892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096892 prefixEnd_2096892 := by exact prefixLift 2096892
  have htrace : WordTrace (prefixWord ++ tailWord_2096892) baseStart_2096892 baseEnd_2096892 := by
    simpa [prefixWord, tailWord_2096892, baseEnd_2096892] using wordTrace_append hprefix tailTrace_2096892
  have hstable : (prefixWord ++ tailWord_2096892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096892).length < 2 ^ (prefixWord ++ tailWord_2096892).sum := by decide
  have hdescent : baseEnd_2096892 < baseStart_2096892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096899 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 4, 3, 2]
def baseStart_2096899 : Nat := 118140960795 + 2096899 * 2 ^ 59
def prefixEnd_2096899 : Nat := 4983230072969 + 3 ^ 40 * 2096899 * 2
def baseEnd_2096899 : Nat := 1076717070932296606719043

theorem tailTrace_2096899 : CollatzResearch.WordTrace tailWord_2096899 prefixEnd_2096899 1076717070932296606719043 := by
  unfold tailWord_2096899
  simp only [CollatzResearch.WordTrace]
  refine ⟨76480189630300519682773751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50986793086867013121849167 76480189630300519682773751)
  ·
    refine ⟨114720284445450779524160627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76480189630300519682773751 114720284445450779524160627)
    ·
      refine ⟨172080426668176169286240941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114720284445450779524160627 172080426668176169286240941)
      ·
        refine ⟨64530160000566063482340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172080426668176169286240941 64530160000566063482340353)
        ·
          refine ⟨48397620000424547611755265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64530160000566063482340353 48397620000424547611755265)
          ·
            refine ⟨36298215000318410708816449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48397620000424547611755265 36298215000318410708816449)
            ·
              refine ⟨27223661250238808031612337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36298215000318410708816449 27223661250238808031612337)
              ·
                refine ⟨20417745937679106023709253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27223661250238808031612337 20417745937679106023709253)
                ·
                  refine ⟨3828327363314832379445485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20417745937679106023709253 3828327363314832379445485)
                  ·
                    refine ⟨1435622761243062142292057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828327363314832379445485 1435622761243062142292057)
                    ·
                      refine ⟨1076717070932296606719043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435622761243062142292057 1076717070932296606719043)
                      ·
                        rfl

theorem cell23_2096899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_2096899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096899 prefixEnd_2096899 := by exact prefixLift 2096899
  have htrace : WordTrace (prefixWord ++ tailWord_2096899) baseStart_2096899 baseEnd_2096899 := by
    simpa [prefixWord, tailWord_2096899, baseEnd_2096899] using wordTrace_append hprefix tailTrace_2096899
  have hstable : (prefixWord ++ tailWord_2096899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096899).length < 2 ^ (prefixWord ++ tailWord_2096899).sum := by decide
  have hdescent : baseEnd_2096899 < baseStart_2096899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096906 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2096906 : Nat := 118140960795 + 2096906 * 2 ^ 59
def prefixEnd_2096906 : Nat := 4983230072969 + 3 ^ 40 * 2096906 * 2
def baseEnd_2096906 : Nat := 1076720665296878079331511

theorem tailTrace_2096906 : CollatzResearch.WordTrace tailWord_2096906 prefixEnd_2096906 1076720665296878079331511 := by
  unfold tailWord_2096906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120111235318789969569643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50986963294183439918852381 19120111235318789969569643)
  ·
    refine ⟨28680166852978184954354465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19120111235318789969569643 28680166852978184954354465)
    ·
      refine ⟨21510125139733638715765849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28680166852978184954354465 21510125139733638715765849)
      ·
        refine ⟨16132593854800229036824387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21510125139733638715765849 16132593854800229036824387)
        ·
          refine ⟨24198890782200343555236581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16132593854800229036824387 24198890782200343555236581)
          ·
            refine ⟨4537292021662564416606859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24198890782200343555236581 4537292021662564416606859)
            ·
              refine ⟨6805938032493846624910289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537292021662564416606859 6805938032493846624910289)
              ·
                refine ⟨5104453524370384968682717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805938032493846624910289 5104453524370384968682717)
                ·
                  refine ⟨1914170071638894363256019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5104453524370384968682717 1914170071638894363256019)
                  ·
                    refine ⟨2871255107458341544884029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914170071638894363256019 2871255107458341544884029)
                    ·
                      refine ⟨1076720665296878079331511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2871255107458341544884029 1076720665296878079331511)
                      ·
                        rfl

theorem cell23_2096906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2096906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096906 prefixEnd_2096906 := by exact prefixLift 2096906
  have htrace : WordTrace (prefixWord ++ tailWord_2096906) baseStart_2096906 baseEnd_2096906 := by
    simpa [prefixWord, tailWord_2096906, baseEnd_2096906] using wordTrace_append hprefix tailTrace_2096906
  have hstable : (prefixWord ++ tailWord_2096906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096906).length < 2 ^ (prefixWord ++ tailWord_2096906).sum := by decide
  have hdescent : baseEnd_2096906 < baseStart_2096906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096959 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_2096959 : Nat := 118140960795 + 2096959 * 2 ^ 59
def prefixEnd_2096959 : Nat := 4983230072969 + 3 ^ 40 * 2096959 * 2
def baseEnd_2096959 : Nat := 1076747879771566371968767

theorem tailTrace_2096959 : CollatzResearch.WordTrace tailWord_2096959 prefixEnd_2096959 1076747879771566371968767 := by
  unfold tailWord_2096959
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482378010083149929957931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50988252006722099953305287 76482378010083149929957931)
  ·
    refine ⟨114723567015124724894936897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482378010083149929957931 114723567015124724894936897)
    ·
      refine ⟨86042675261343543671202673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114723567015124724894936897 86042675261343543671202673)
      ·
        refine ⟨64532006446007657753402005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86042675261343543671202673 64532006446007657753402005)
        ·
          refine ⟨3024937802156608957190719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64532006446007657753402005 3024937802156608957190719)
          ·
            refine ⟨4537406703234913435786079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024937802156608957190719 4537406703234913435786079)
            ·
              refine ⟨6806110054852370153679119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537406703234913435786079 6806110054852370153679119)
              ·
                refine ⟨10209165082278555230518679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806110054852370153679119 10209165082278555230518679)
                ·
                  refine ⟨15313747623417832845778019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209165082278555230518679 15313747623417832845778019)
                  ·
                    refine ⟨22970621435126749268667029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15313747623417832845778019 22970621435126749268667029)
                    ·
                      refine ⟨1076747879771566371968767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22970621435126749268667029 1076747879771566371968767)
                      ·
                        rfl

theorem cell23_2096959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_2096959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2096959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2096959 prefixEnd_2096959 := by exact prefixLift 2096959
  have htrace : WordTrace (prefixWord ++ tailWord_2096959) baseStart_2096959 baseEnd_2096959 := by
    simpa [prefixWord, tailWord_2096959, baseEnd_2096959] using wordTrace_append hprefix tailTrace_2096959
  have hstable : (prefixWord ++ tailWord_2096959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096959).length < 2 ^ (prefixWord ++ tailWord_2096959).sum := by decide
  have hdescent : baseEnd_2096959 < baseStart_2096959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097013 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2097013 : Nat := 118140960795 + 2097013 * 2 ^ 59
def prefixEnd_2097013 : Nat := 4983230072969 + 3 ^ 40 * 2097013 * 2
def baseEnd_2097013 : Nat := 1076775607726909160693519

theorem tailTrace_2097013 : CollatzResearch.WordTrace tailWord_2097013 prefixEnd_2097013 1076775607726909160693519 := by
  unfold tailWord_2097013
  simp only [CollatzResearch.WordTrace]
  refine ⟨76484347551887517152423693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50989565034591678101615795 76484347551887517152423693)
  ·
    refine ⟨28681630331957818932158885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76484347551887517152423693 28681630331957818932158885)
    ·
      refine ⟨5377805687242091049779791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28681630331957818932158885 5377805687242091049779791)
      ·
        refine ⟨8066708530863136574669687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377805687242091049779791 8066708530863136574669687)
        ·
          refine ⟨12100062796294704862004531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066708530863136574669687 12100062796294704862004531)
          ·
            refine ⟨18150094194442057293006797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100062796294704862004531 18150094194442057293006797)
            ·
              refine ⟨6806285322915771484877549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18150094194442057293006797 6806285322915771484877549)
              ·
                refine ⟨2552356996093414306829081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6806285322915771484877549 2552356996093414306829081)
                ·
                  refine ⟨1914267747070060730121811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2552356996093414306829081 1914267747070060730121811)
                  ·
                    refine ⟨2871401620605091095182717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914267747070060730121811 2871401620605091095182717)
                    ·
                      refine ⟨1076775607726909160693519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2871401620605091095182717 1076775607726909160693519)
                      ·
                        rfl

theorem cell23_2097013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2097013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097013 prefixEnd_2097013 := by exact prefixLift 2097013
  have htrace : WordTrace (prefixWord ++ tailWord_2097013) baseStart_2097013 baseEnd_2097013 := by
    simpa [prefixWord, tailWord_2097013, baseEnd_2097013] using wordTrace_append hprefix tailTrace_2097013
  have hstable : (prefixWord ++ tailWord_2097013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097013).length < 2 ^ (prefixWord ++ tailWord_2097013).sum := by decide
  have hdescent : baseEnd_2097013 < baseStart_2097013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097136 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_2097136 : Nat := 118140960795 + 2097136 * 2 ^ 59
def prefixEnd_2097136 : Nat := 4983230072969 + 3 ^ 40 * 2097136 * 2
def baseEnd_2097136 : Nat := 358946255282470726485151

theorem tailTrace_2097136 : CollatzResearch.WordTrace tailWord_2097136 prefixEnd_2097136 358946255282470726485151 := by
  unfold tailWord_2097136
  simp only [CollatzResearch.WordTrace]
  refine ⟨38244416865220954579575631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50992555820294606106100841 38244416865220954579575631)
  ·
    refine ⟨57366625297831431869363447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38244416865220954579575631 57366625297831431869363447)
    ·
      refine ⟨86049937946747147804045171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57366625297831431869363447 86049937946747147804045171)
      ·
        refine ⟨129074906920120721706067757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86049937946747147804045171 129074906920120721706067757)
        ·
          refine ⟨48403090095045270639775409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129074906920120721706067757 48403090095045270639775409)
          ·
            refine ⟨36302317571283952979831557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48403090095045270639775409 36302317571283952979831557)
            ·
              refine ⟨6806684544615741183718417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36302317571283952979831557 6806684544615741183718417)
              ·
                refine ⟨5105013408461805887788813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806684544615741183718417 5105013408461805887788813)
                ·
                  refine ⟨1914380028173177207920805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5105013408461805887788813 1914380028173177207920805)
                  ·
                    refine ⟨358946255282470726485151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914380028173177207920805 358946255282470726485151)
                    ·
                      rfl

theorem cell23_2097136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_2097136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097136 prefixEnd_2097136 := by exact prefixLift 2097136
  have htrace : WordTrace (prefixWord ++ tailWord_2097136) baseStart_2097136 baseEnd_2097136 := by
    simpa [prefixWord, tailWord_2097136, baseEnd_2097136] using wordTrace_append hprefix tailTrace_2097136
  have hstable : (prefixWord ++ tailWord_2097136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097136).length < 2 ^ (prefixWord ++ tailWord_2097136).sum := by decide
  have hdescent : baseEnd_2097136 < baseStart_2097136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097149 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 8]
def baseStart_2097149 : Nat := 118140960795 + 2097149 * 2 ^ 59
def prefixEnd_2097149 : Nat := 4983230072969 + 3 ^ 40 * 2097149 * 2
def baseEnd_2097149 : Nat := 119649493455102292065877

theorem tailTrace_2097149 : CollatzResearch.WordTrace tailWord_2097149 prefixEnd_2097149 119649493455102292065877 := by
  unfold tailWord_2097149
  simp only [CollatzResearch.WordTrace]
  refine ⟨76489307879394812379374501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50992871919596541586249667 76489307879394812379374501)
  ·
    refine ⟨14341745227386527321132719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76489307879394812379374501 14341745227386527321132719)
    ·
      refine ⟨21512617841079790981699079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14341745227386527321132719 21512617841079790981699079)
      ·
        refine ⟨32268926761619686472548619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21512617841079790981699079 32268926761619686472548619)
        ·
          refine ⟨48403390142429529708822929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32268926761619686472548619 48403390142429529708822929)
          ·
            refine ⟨36302542606822147281617197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48403390142429529708822929 36302542606822147281617197)
            ·
              refine ⟨13613453477558305230606449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36302542606822147281617197 13613453477558305230606449)
              ·
                refine ⟨10210090108168728922954837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13613453477558305230606449 10210090108168728922954837)
                ·
                  refine ⟨119649493455102292065877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10210090108168728922954837 119649493455102292065877)
                  ·
                    rfl

theorem cell23_2097149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_2097149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097149 prefixEnd_2097149 := by exact prefixLift 2097149
  have htrace : WordTrace (prefixWord ++ tailWord_2097149) baseStart_2097149 baseEnd_2097149 := by
    simpa [prefixWord, tailWord_2097149, baseEnd_2097149] using wordTrace_append hprefix tailTrace_2097149
  have hstable : (prefixWord ++ tailWord_2097149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097149).length < 2 ^ (prefixWord ++ tailWord_2097149).sum := by decide
  have hdescent : baseEnd_2097149 < baseStart_2097149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097166 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_2097166 : Nat := 118140960795 + 2097166 * 2 ^ 59
def prefixEnd_2097166 : Nat := 4983230072969 + 3 ^ 40 * 2097166 * 2
def baseEnd_2097166 : Nat := 119650463363005229120035

theorem tailTrace_2097166 : CollatzResearch.WordTrace tailWord_2097166 prefixEnd_2097166 119650463363005229120035 := by
  unfold tailWord_2097166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9561240990041653035342919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50993285280222149521828901 9561240990041653035342919)
  ·
    refine ⟨14341861485062479553014379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9561240990041653035342919 14341861485062479553014379)
    ·
      refine ⟨21512792227593719329521569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14341861485062479553014379 21512792227593719329521569)
      ·
        refine ⟨16134594170695289497141177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21512792227593719329521569 16134594170695289497141177)
        ·
          refine ⟨12100945628021467122855883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16134594170695289497141177 12100945628021467122855883)
          ·
            refine ⟨18151418442032200684283825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100945628021467122855883 18151418442032200684283825)
            ·
              refine ⟨13613563831524150513212869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18151418442032200684283825 13613563831524150513212869)
              ·
                refine ⟨2552543218410778221227413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13613563831524150513212869 2552543218410778221227413)
                ·
                  refine ⟨119650463363005229120035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2552543218410778221227413 119650463363005229120035)
                  ·
                    rfl

theorem cell23_2097166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_2097166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097166 prefixEnd_2097166 := by exact prefixLift 2097166
  have htrace : WordTrace (prefixWord ++ tailWord_2097166) baseStart_2097166 baseEnd_2097166 := by
    simpa [prefixWord, tailWord_2097166, baseEnd_2097166] using wordTrace_append hprefix tailTrace_2097166
  have hstable : (prefixWord ++ tailWord_2097166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097166).length < 2 ^ (prefixWord ++ tailWord_2097166).sum := by decide
  have hdescent : baseEnd_2097166 < baseStart_2097166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097196 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_2097196 : Nat := 118140960795 + 2097196 * 2 ^ 59
def prefixEnd_2097196 : Nat := 4983230072969 + 3 ^ 40 * 2097196 * 2
def baseEnd_2097196 : Nat := 358956524895560648235059

theorem tailTrace_2097196 : CollatzResearch.WordTrace tailWord_2097196 prefixEnd_2097196 358956524895560648235059 := by
  unfold tailWord_2097196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38245511055112269703167721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50994014740149692937556961 38245511055112269703167721)
  ·
    refine ⟨28684133291334202277375791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38245511055112269703167721 28684133291334202277375791)
    ·
      refine ⟨43026199937001303416063687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28684133291334202277375791 43026199937001303416063687)
      ·
        refine ⟨64539299905501955124095531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43026199937001303416063687 64539299905501955124095531)
        ·
          refine ⟨96808949858252932686143297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64539299905501955124095531 96808949858252932686143297)
          ·
            refine ⟨72606712393689699514607473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96808949858252932686143297 72606712393689699514607473)
            ·
              refine ⟨54455034295267274635955605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72606712393689699514607473 54455034295267274635955605)
              ·
                refine ⟨2552579732590653498560419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54455034295267274635955605 2552579732590653498560419)
                ·
                  refine ⟨3828869598885980247840629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552579732590653498560419 3828869598885980247840629)
                  ·
                    refine ⟨358956524895560648235059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3828869598885980247840629 358956524895560648235059)
                    ·
                      rfl

theorem cell23_2097196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_2097196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097196 prefixEnd_2097196 := by exact prefixLift 2097196
  have htrace : WordTrace (prefixWord ++ tailWord_2097196) baseStart_2097196 baseEnd_2097196 := by
    simpa [prefixWord, tailWord_2097196, baseEnd_2097196] using wordTrace_append hprefix tailTrace_2097196
  have hstable : (prefixWord ++ tailWord_2097196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097196).length < 2 ^ (prefixWord ++ tailWord_2097196).sum := by decide
  have hdescent : baseEnd_2097196 < baseStart_2097196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097203 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 2, 3, 2]
def baseStart_2097203 : Nat := 118140960795 + 2097203 * 2 ^ 59
def prefixEnd_2097203 : Nat := 4983230072969 + 3 ^ 40 * 2097203 * 2
def baseEnd_2097203 : Nat := 1076873169051263417317645

theorem tailTrace_2097203 : CollatzResearch.WordTrace tailWord_2097203 prefixEnd_2097203 1076873169051263417317645 := by
  unfold tailWord_2097203
  simp only [CollatzResearch.WordTrace]
  refine ⟨76491277421199179601840263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50994184947466119734560175 76491277421199179601840263)
  ·
    refine ⟨114736916131798769402760395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76491277421199179601840263 114736916131798769402760395)
    ·
      refine ⟨172105374197698154104140593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114736916131798769402760395 172105374197698154104140593)
      ·
        refine ⟨129079030648273615578105445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172105374197698154104140593 129079030648273615578105445)
        ·
          refine ⟨24202318246551302920894771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129079030648273615578105445 24202318246551302920894771)
          ·
            refine ⟨36303477369826954381342157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24202318246551302920894771 36303477369826954381342157)
            ·
              refine ⟨13613804013685107893003309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36303477369826954381342157 13613804013685107893003309)
              ·
                refine ⟨5105176505131915459876241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13613804013685107893003309 5105176505131915459876241)
                ·
                  refine ⟨3828882378848936594907181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105176505131915459876241 3828882378848936594907181)
                  ·
                    refine ⟨1435830892068351223090193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828882378848936594907181 1435830892068351223090193)
                    ·
                      refine ⟨1076873169051263417317645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1435830892068351223090193 1076873169051263417317645)
                      ·
                        rfl

theorem cell23_2097203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3, 2].length) (baseStart_2097203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097203 prefixEnd_2097203 := by exact prefixLift 2097203
  have htrace : WordTrace (prefixWord ++ tailWord_2097203) baseStart_2097203 baseEnd_2097203 := by
    simpa [prefixWord, tailWord_2097203, baseEnd_2097203] using wordTrace_append hprefix tailTrace_2097203
  have hstable : (prefixWord ++ tailWord_2097203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097203).length < 2 ^ (prefixWord ++ tailWord_2097203).sum := by decide
  have hdescent : baseEnd_2097203 < baseStart_2097203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097210 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_2097210 : Nat := 118140960795 + 2097210 * 2 ^ 59
def prefixEnd_2097210 : Nat := 4983230072969 + 3 ^ 40 * 2097210 * 2
def baseEnd_2097210 : Nat := 1076876763415844889930113

theorem tailTrace_2097210 : CollatzResearch.WordTrace tailWord_2097210 prefixEnd_2097210 1076876763415844889930113 := by
  unfold tailWord_2097210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19122883183043454949336271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50994355154782546531563389 19122883183043454949336271)
  ·
    refine ⟨28684324774565182424004407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19122883183043454949336271 28684324774565182424004407)
    ·
      refine ⟨43026487161847773636006611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28684324774565182424004407 43026487161847773636006611)
      ·
        refine ⟨64539730742771660454009917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43026487161847773636006611 64539730742771660454009917)
        ·
          refine ⟨24202399028539372670253719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64539730742771660454009917 24202399028539372670253719)
          ·
            refine ⟨36303598542809059005380579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24202399028539372670253719 36303598542809059005380579)
            ·
              refine ⟨54455397814213588508070869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36303598542809059005380579 54455397814213588508070869)
              ·
                refine ⟨1276298386270630980657911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54455397814213588508070869 1276298386270630980657911)
                ·
                  refine ⟨1914447579405946470986867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276298386270630980657911 1914447579405946470986867)
                  ·
                    refine ⟨2871671369108919706480301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914447579405946470986867 2871671369108919706480301)
                    ·
                      refine ⟨1076876763415844889930113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2871671369108919706480301 1076876763415844889930113)
                      ·
                        rfl

theorem cell23_2097210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_2097210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097210 prefixEnd_2097210 := by exact prefixLift 2097210
  have htrace : WordTrace (prefixWord ++ tailWord_2097210) baseStart_2097210 baseEnd_2097210 := by
    simpa [prefixWord, tailWord_2097210, baseEnd_2097210] using wordTrace_append hprefix tailTrace_2097210
  have hstable : (prefixWord ++ tailWord_2097210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097210).length < 2 ^ (prefixWord ++ tailWord_2097210).sum := by decide
  have hdescent : baseEnd_2097210 < baseStart_2097210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2097236 : Nat := 118140960795 + 2097236 * 2 ^ 59
def prefixEnd_2097236 : Nat := 4983230072969 + 3 ^ 40 * 2097236 * 2
def baseEnd_2097236 : Nat := 1076890113912861788204993

theorem tailTrace_2097236 : CollatzResearch.WordTrace tailWord_2097236 prefixEnd_2097236 1076890113912861788204993 := by
  unfold tailWord_2097236
  simp only [CollatzResearch.WordTrace]
  refine ⟨38246240515039813118895781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50994987353386417491861041 38246240515039813118895781)
  ·
    refine ⟨7171170096569964959792959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38246240515039813118895781 7171170096569964959792959)
    ·
      refine ⟨10756755144854947439689439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171170096569964959792959 10756755144854947439689439)
      ·
        refine ⟨16135132717282421159534159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10756755144854947439689439 16135132717282421159534159)
        ·
          refine ⟨24202699075923631739301239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16135132717282421159534159 24202699075923631739301239)
          ·
            refine ⟨36304048613885447608951859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24202699075923631739301239 36304048613885447608951859)
            ·
              refine ⟨54456072920828171413427789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36304048613885447608951859 54456072920828171413427789)
              ·
                refine ⟨20421027345310564280035421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54456072920828171413427789 20421027345310564280035421)
                ·
                  refine ⟨7657885254491461605013283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20421027345310564280035421 7657885254491461605013283)
                  ·
                    refine ⟨11486827881737192407519925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657885254491461605013283 11486827881737192407519925)
                    ·
                      refine ⟨1076890113912861788204993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11486827881737192407519925 1076890113912861788204993)
                      ·
                        rfl

theorem cell23_2097236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2097236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097236 prefixEnd_2097236 := by exact prefixLift 2097236
  have htrace : WordTrace (prefixWord ++ tailWord_2097236) baseStart_2097236 baseEnd_2097236 := by
    simpa [prefixWord, tailWord_2097236, baseEnd_2097236] using wordTrace_append hprefix tailTrace_2097236
  have hstable : (prefixWord ++ tailWord_2097236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097236).length < 2 ^ (prefixWord ++ tailWord_2097236).sum := by decide
  have hdescent : baseEnd_2097236 < baseStart_2097236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097253 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2097253 : Nat := 118140960795 + 2097253 * 2 ^ 59
def prefixEnd_2097253 : Nat := 4983230072969 + 3 ^ 40 * 2097253 * 2
def baseEnd_2097253 : Nat := 1076898843083988221692415

theorem tailTrace_2097253 : CollatzResearch.WordTrace tailWord_2097253 prefixEnd_2097253 1076898843083988221692415 := by
  unfold tailWord_2097253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76493101071018038141160413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50995400714012025427440275 76493101071018038141160413)
  ·
    refine ⟨28684912901631764302935155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76493101071018038141160413 28684912901631764302935155)
    ·
      refine ⟨43027369352447646454402733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28684912901631764302935155 43027369352447646454402733)
      ·
        refine ⟨16135263507167867420401025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43027369352447646454402733 16135263507167867420401025)
        ·
          refine ⟨12101447630375900565300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16135263507167867420401025 12101447630375900565300769)
          ·
            refine ⟨9076085722781925423975577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12101447630375900565300769 9076085722781925423975577)
            ·
              refine ⟨6807064292086444067981683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9076085722781925423975577 6807064292086444067981683)
              ·
                refine ⟨10210596438129666101972525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6807064292086444067981683 10210596438129666101972525)
                ·
                  refine ⟨3828973664298624788239697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10210596438129666101972525 3828973664298624788239697)
                  ·
                    refine ⟨2871730248223968591179773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3828973664298624788239697 2871730248223968591179773)
                    ·
                      refine ⟨1076898843083988221692415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2871730248223968591179773 1076898843083988221692415)
                      ·
                        rfl

theorem cell23_2097253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2097253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097253 prefixEnd_2097253 := by exact prefixLift 2097253
  have htrace : WordTrace (prefixWord ++ tailWord_2097253) baseStart_2097253 baseEnd_2097253 := by
    simpa [prefixWord, tailWord_2097253, baseEnd_2097253] using wordTrace_append hprefix tailTrace_2097253
  have hstable : (prefixWord ++ tailWord_2097253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097253).length < 2 ^ (prefixWord ++ tailWord_2097253).sum := by decide
  have hdescent : baseEnd_2097253 < baseStart_2097253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097393 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2097393 : Nat := 118140960795 + 2097393 * 2 ^ 59
def prefixEnd_2097393 : Nat := 4983230072969 + 3 ^ 40 * 2097393 * 2
def baseEnd_2097393 : Nat := 358990243458539224647257

theorem tailTrace_2097393 : CollatzResearch.WordTrace tailWord_2097393 prefixEnd_2097393 358990243458539224647257 := by
  unfold tailWord_2097393
  simp only [CollatzResearch.WordTrace]
  refine ⟨76498207290510842051256833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50998804860340561367504555 76498207290510842051256833)
  ·
    refine ⟨57373655467883131538442625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76498207290510842051256833 57373655467883131538442625)
    ·
      refine ⟨43030241600912348653831969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57373655467883131538442625 43030241600912348653831969)
      ·
        refine ⟨32272681200684261490373977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43030241600912348653831969 32272681200684261490373977)
        ·
          refine ⟨24204510900513196117780483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32272681200684261490373977 24204510900513196117780483)
          ·
            refine ⟨36306766350769794176670725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24204510900513196117780483 36306766350769794176670725)
            ·
              refine ⟨6807518690769336408125761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36306766350769794176670725 6807518690769336408125761)
              ·
                refine ⟨5105639018077002306094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6807518690769336408125761 5105639018077002306094321)
                ·
                  refine ⟨3829229263557751729570741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105639018077002306094321 3829229263557751729570741)
                  ·
                    refine ⟨358990243458539224647257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3829229263557751729570741 358990243458539224647257)
                    ·
                      rfl

theorem cell23_2097393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2097393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097393 prefixEnd_2097393 := by exact prefixLift 2097393
  have htrace : WordTrace (prefixWord ++ tailWord_2097393) baseStart_2097393 baseEnd_2097393 := by
    simpa [prefixWord, tailWord_2097393, baseEnd_2097393] using wordTrace_append hprefix tailTrace_2097393
  have hstable : (prefixWord ++ tailWord_2097393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097393).length < 2 ^ (prefixWord ++ tailWord_2097393).sum := by decide
  have hdescent : baseEnd_2097393 < baseStart_2097393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097457 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2097457 : Nat := 118140960795 + 2097457 * 2 ^ 59
def prefixEnd_2097457 : Nat := 4983230072969 + 3 ^ 40 * 2097457 * 2
def baseEnd_2097457 : Nat := 359001197712501807847159

theorem tailTrace_2097457 : CollatzResearch.WordTrace tailWord_2097457 prefixEnd_2097457 359001197712501807847159 := by
  unfold tailWord_2097457
  simp only [CollatzResearch.WordTrace]
  refine ⟨76500541562278980981586625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51000361041519320654391083 76500541562278980981586625)
  ·
    refine ⟨57375406171709235736189969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76500541562278980981586625 57375406171709235736189969)
    ·
      refine ⟨43031554628781926802142477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57375406171709235736189969 43031554628781926802142477)
      ·
        refine ⟨16136832985793222550803429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43031554628781926802142477 16136832985793222550803429)
        ·
          refine ⟨3025656184836229228275643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16136832985793222550803429 3025656184836229228275643)
          ·
            refine ⟨4538484277254343842413465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025656184836229228275643 4538484277254343842413465)
            ·
              refine ⟨3403863207940757881810099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538484277254343842413465 3403863207940757881810099)
              ·
                refine ⟨5105794811911136822715149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403863207940757881810099 5105794811911136822715149)
                ·
                  refine ⟨1914673054466676308518181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5105794811911136822715149 1914673054466676308518181)
                  ·
                    refine ⟨359001197712501807847159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914673054466676308518181 359001197712501807847159)
                    ·
                      rfl

theorem cell23_2097457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2097457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097457 prefixEnd_2097457 := by exact prefixLift 2097457
  have htrace : WordTrace (prefixWord ++ tailWord_2097457) baseStart_2097457 baseEnd_2097457 := by
    simpa [prefixWord, tailWord_2097457, baseEnd_2097457] using wordTrace_append hprefix tailTrace_2097457
  have hstable : (prefixWord ++ tailWord_2097457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097457).length < 2 ^ (prefixWord ++ tailWord_2097457).sum := by decide
  have hdescent : baseEnd_2097457 < baseStart_2097457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097507 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 2, 3, 2]
def baseStart_2097507 : Nat := 118140960795 + 2097507 * 2 ^ 59
def prefixEnd_2097507 : Nat := 4983230072969 + 3 ^ 40 * 2097507 * 2
def baseEnd_2097507 : Nat := 1077029267170230227916247

theorem tailTrace_2097507 : CollatzResearch.WordTrace tailWord_2097507 prefixEnd_2097507 1077029267170230227916247 := by
  unfold tailWord_2097507
  simp only [CollatzResearch.WordTrace]
  refine ⟨76502365212097839520906775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51001576808065226347271183 76502365212097839520906775)
  ·
    refine ⟨114753547818146759281360163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76502365212097839520906775 114753547818146759281360163)
    ·
      refine ⟨172130321727220138922040245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114753547818146759281360163 172130321727220138922040245)
      ·
        refine ⟨16137217661926888023941273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172130321727220138922040245 16137217661926888023941273)
        ·
          refine ⟨12102913246445166017955955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16137217661926888023941273 12102913246445166017955955)
          ·
            refine ⟨18154369869667749026933933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12102913246445166017955955 18154369869667749026933933)
            ·
              refine ⟨6807888701125405885100225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18154369869667749026933933 6807888701125405885100225)
              ·
                refine ⟨5105916525844054413825169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6807888701125405885100225 5105916525844054413825169)
                ·
                  refine ⟨3829437394383040810368877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105916525844054413825169 3829437394383040810368877)
                  ·
                    refine ⟨1436039022893640303888329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3829437394383040810368877 1436039022893640303888329)
                    ·
                      refine ⟨1077029267170230227916247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436039022893640303888329 1077029267170230227916247)
                      ·
                        rfl

theorem cell23_2097507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_2097507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097507 prefixEnd_2097507 := by exact prefixLift 2097507
  have htrace : WordTrace (prefixWord ++ tailWord_2097507) baseStart_2097507 baseEnd_2097507 := by
    simpa [prefixWord, tailWord_2097507, baseEnd_2097507] using wordTrace_append hprefix tailTrace_2097507
  have hstable : (prefixWord ++ tailWord_2097507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097507).length < 2 ^ (prefixWord ++ tailWord_2097507).sum := by decide
  have hdescent : baseEnd_2097507 < baseStart_2097507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097514 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2097514 : Nat := 118140960795 + 2097514 * 2 ^ 59
def prefixEnd_2097514 : Nat := 4983230072969 + 3 ^ 40 * 2097514 * 2
def baseEnd_2097514 : Nat := 1077032861534811700528715

theorem tailTrace_2097514 : CollatzResearch.WordTrace tailWord_2097514 prefixEnd_2097514 1077032861534811700528715 := by
  unfold tailWord_2097514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19125655130768119929102899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51001747015381653144274397 19125655130768119929102899)
  ·
    refine ⟨28688482696152179893654349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19125655130768119929102899 28688482696152179893654349)
    ·
      refine ⟨10758181011057067460120381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28688482696152179893654349 10758181011057067460120381)
      ·
        refine ⟨4034317879146400297545143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10758181011057067460120381 4034317879146400297545143)
        ·
          refine ⟨6051476818719600446317715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034317879146400297545143 6051476818719600446317715)
          ·
            refine ⟨9077215228079400669476573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051476818719600446317715 9077215228079400669476573)
            ·
              refine ⟨3403955710529775251053715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9077215228079400669476573 3403955710529775251053715)
              ·
                refine ⟨5105933565794662876580573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403955710529775251053715 5105933565794662876580573)
                ·
                  refine ⟨1914725087172998578717715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5105933565794662876580573 1914725087172998578717715)
                  ·
                    refine ⟨2872087630759497868076573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914725087172998578717715 2872087630759497868076573)
                    ·
                      refine ⟨1077032861534811700528715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872087630759497868076573 1077032861534811700528715)
                      ·
                        rfl

theorem cell23_2097514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2097514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097514 prefixEnd_2097514 := by exact prefixLift 2097514
  have htrace : WordTrace (prefixWord ++ tailWord_2097514) baseStart_2097514 baseEnd_2097514 := by
    simpa [prefixWord, tailWord_2097514, baseEnd_2097514] using wordTrace_append hprefix tailTrace_2097514
  have hstable : (prefixWord ++ tailWord_2097514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097514).length < 2 ^ (prefixWord ++ tailWord_2097514).sum := by decide
  have hdescent : baseEnd_2097514 < baseStart_2097514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097537 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2097537 : Nat := 118140960795 + 2097537 * 2 ^ 59
def prefixEnd_2097537 : Nat := 4983230072969 + 3 ^ 40 * 2097537 * 2
def baseEnd_2097537 : Nat := 1077044671589865110541109

theorem tailTrace_2097537 : CollatzResearch.WordTrace tailWord_2097537 prefixEnd_2097537 1077044671589865110541109 := by
  unfold tailWord_2097537
  simp only [CollatzResearch.WordTrace]
  refine ⟨76503459401989154644498865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51002306267992769762999243 76503459401989154644498865)
  ·
    refine ⟨57377594551491865983374149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76503459401989154644498865 57377594551491865983374149)
    ·
      refine ⟨10758298978404724871882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57377594551491865983374149 10758298978404724871882653)
      ·
        refine ⟨4034362116901771826955995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10758298978404724871882653 4034362116901771826955995)
        ·
          refine ⟨6051543175352657740433993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034362116901771826955995 6051543175352657740433993)
          ·
            refine ⟨4538657381514493305325495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6051543175352657740433993 4538657381514493305325495)
            ·
              refine ⟨6807986072271739957988243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538657381514493305325495 6807986072271739957988243)
              ·
                refine ⟨10211979108407609936982365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6807986072271739957988243 10211979108407609936982365)
                ·
                  refine ⟨3829492165652853726368387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10211979108407609936982365 3829492165652853726368387)
                  ·
                    refine ⟨5744238248479280589552581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3829492165652853726368387 5744238248479280589552581)
                    ·
                      refine ⟨1077044671589865110541109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5744238248479280589552581 1077044671589865110541109)
                      ·
                        rfl

theorem cell23_2097537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2097537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097537 prefixEnd_2097537 := by exact prefixLift 2097537
  have htrace : WordTrace (prefixWord ++ tailWord_2097537) baseStart_2097537 baseEnd_2097537 := by
    simpa [prefixWord, tailWord_2097537, baseEnd_2097537] using wordTrace_append hprefix tailTrace_2097537
  have hstable : (prefixWord ++ tailWord_2097537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097537).length < 2 ^ (prefixWord ++ tailWord_2097537).sum := by decide
  have hdescent : baseEnd_2097537 < baseStart_2097537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097543 : List Nat := [1, 1, 4, 2, 2, 1, 1, 11]
def baseStart_2097543 : Nat := 118140960795 + 2097543 * 2 ^ 59
def prefixEnd_2097543 : Nat := 4983230072969 + 3 ^ 40 * 2097543 * 2
def baseEnd_2097543 : Nat := 39890657499029336558003

theorem tailTrace_2097543 : CollatzResearch.WordTrace tailWord_2097543 prefixEnd_2097543 39890657499029336558003 := by
  unfold tailWord_2097543
  simp only [CollatzResearch.WordTrace]
  refine ⟨76503678239967417669217283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51002452159978278446144855 76503678239967417669217283)
  ·
    refine ⟨114755517359951126503825925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76503678239967417669217283 114755517359951126503825925)
    ·
      refine ⟨21516659504990836219467361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114755517359951126503825925 21516659504990836219467361)
      ·
        refine ⟨16137494628743127164600521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21516659504990836219467361 16137494628743127164600521)
        ·
          refine ⟨12103120971557345373450391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16137494628743127164600521 12103120971557345373450391)
          ·
            refine ⟨18154681457336018060175587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12103120971557345373450391 18154681457336018060175587)
            ·
              refine ⟨27232022186004027090263381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18154681457336018060175587 27232022186004027090263381)
              ·
                refine ⟨39890657499029336558003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27232022186004027090263381 39890657499029336558003)
                ·
                  rfl

theorem cell23_2097543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 11].length) (baseStart_2097543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097543 prefixEnd_2097543 := by exact prefixLift 2097543
  have htrace : WordTrace (prefixWord ++ tailWord_2097543) baseStart_2097543 baseEnd_2097543 := by
    simpa [prefixWord, tailWord_2097543, baseEnd_2097543] using wordTrace_append hprefix tailTrace_2097543
  have hstable : (prefixWord ++ tailWord_2097543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097543).length < 2 ^ (prefixWord ++ tailWord_2097543).sum := by decide
  have hdescent : baseEnd_2097543 < baseStart_2097543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097565 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2097565 : Nat := 118140960795 + 2097565 * 2 ^ 59
def prefixEnd_2097565 : Nat := 4983230072969 + 3 ^ 40 * 2097565 * 2
def baseEnd_2097565 : Nat := 1077059049048191000990981

theorem tailTrace_2097565 : CollatzResearch.WordTrace tailWord_2097565 prefixEnd_2097565 1077059049048191000990981 := by
  unfold tailWord_2097565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76504480645887715426518149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51002987097258476951012099 76504480645887715426518149)
  ·
    refine ⟨14344590121103946642472153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76504480645887715426518149 14344590121103946642472153)
    ·
      refine ⟨10758442590827959981854115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14344590121103946642472153 10758442590827959981854115)
      ·
        refine ⟨16137663886241939972781173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758442590827959981854115 16137663886241939972781173)
        ·
          refine ⟨1512905989335181872448235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16137663886241939972781173 1512905989335181872448235)
          ·
            refine ⟨2269358984002772808672353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512905989335181872448235 2269358984002772808672353)
            ·
              refine ⟨1702019238002079606504265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269358984002772808672353 1702019238002079606504265)
              ·
                refine ⟨1276514428501559704878199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702019238002079606504265 1276514428501559704878199)
                ·
                  refine ⟨1914771642752339557317299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276514428501559704878199 1914771642752339557317299)
                  ·
                    refine ⟨2872157464128509335975949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914771642752339557317299 2872157464128509335975949)
                    ·
                      refine ⟨1077059049048191000990981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872157464128509335975949 1077059049048191000990981)
                      ·
                        rfl

theorem cell23_2097565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2097565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097565 prefixEnd_2097565 := by exact prefixLift 2097565
  have htrace : WordTrace (prefixWord ++ tailWord_2097565) baseStart_2097565 baseEnd_2097565 := by
    simpa [prefixWord, tailWord_2097565, baseEnd_2097565] using wordTrace_append hprefix tailTrace_2097565
  have hstable : (prefixWord ++ tailWord_2097565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097565).length < 2 ^ (prefixWord ++ tailWord_2097565).sum := by decide
  have hdescent : baseEnd_2097565 < baseStart_2097565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097571 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 1, 2, 2]
def baseStart_2097571 : Nat := 118140960795 + 2097571 * 2 ^ 59
def prefixEnd_2097571 : Nat := 4983230072969 + 3 ^ 40 * 2097571 * 2
def baseEnd_2097571 : Nat := 1077062129932117977515953

theorem tailTrace_2097571 : CollatzResearch.WordTrace tailWord_2097571 prefixEnd_2097571 1077062129932117977515953 := by
  unfold tailWord_2097571
  simp only [CollatzResearch.WordTrace]
  refine ⟨76504699483865978451236567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51003132989243985634157711 76504699483865978451236567)
  ·
    refine ⟨114757049225798967676854851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76504699483865978451236567 114757049225798967676854851)
    ·
      refine ⟨172135573838698451515282277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114757049225798967676854851 172135573838698451515282277)
      ·
        refine ⟨32275420094755959659115427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172135573838698451515282277 32275420094755959659115427)
        ·
          refine ⟨48413130142133939488673141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32275420094755959659115427 48413130142133939488673141)
          ·
            refine ⟨4538730950825056827063107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48413130142133939488673141 4538730950825056827063107)
            ·
              refine ⟨6808096426237585240594661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538730950825056827063107 6808096426237585240594661)
              ·
                refine ⟨1276518079919547232611499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6808096426237585240594661 1276518079919547232611499)
                ·
                  refine ⟨1914777119879320848917249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276518079919547232611499 1914777119879320848917249)
                  ·
                    refine ⟨1436082839909490636687937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1914777119879320848917249 1436082839909490636687937)
                    ·
                      refine ⟨1077062129932117977515953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436082839909490636687937 1077062129932117977515953)
                      ·
                        rfl

theorem cell23_2097571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_2097571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097571 prefixEnd_2097571 := by exact prefixLift 2097571
  have htrace : WordTrace (prefixWord ++ tailWord_2097571) baseStart_2097571 baseEnd_2097571 := by
    simpa [prefixWord, tailWord_2097571, baseEnd_2097571] using wordTrace_append hprefix tailTrace_2097571
  have hstable : (prefixWord ++ tailWord_2097571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097571).length < 2 ^ (prefixWord ++ tailWord_2097571).sum := by decide
  have hdescent : baseEnd_2097571 < baseStart_2097571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097573 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_2097573 : Nat := 118140960795 + 2097573 * 2 ^ 59
def prefixEnd_2097573 : Nat := 4983230072969 + 3 ^ 40 * 2097573 * 2
def baseEnd_2097573 : Nat := 359021052297808989896981

theorem tailTrace_2097573 : CollatzResearch.WordTrace tailWord_2097573 prefixEnd_2097573 359021052297808989896981 := by
  unfold tailWord_2097573
  simp only [CollatzResearch.WordTrace]
  refine ⟨76504772429858732792809373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51003181619905821861872915 76504772429858732792809373)
  ·
    refine ⟨28689289661197024797303515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76504772429858732792809373 28689289661197024797303515)
    ·
      refine ⟨43033934491795537195955273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28689289661197024797303515 43033934491795537195955273)
      ·
        refine ⟨32275450868846652896966455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43033934491795537195955273 32275450868846652896966455)
        ·
          refine ⟨48413176303269979345449683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32275450868846652896966455 48413176303269979345449683)
          ·
            refine ⟨72619764454904969018174525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48413176303269979345449683 72619764454904969018174525)
            ·
              refine ⟨27232411670589363381815447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72619764454904969018174525 27232411670589363381815447)
              ·
                refine ⟨40848617505884045072723171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27232411670589363381815447 40848617505884045072723171)
                ·
                  refine ⟨61272926258826067609084757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40848617505884045072723171 61272926258826067609084757)
                  ·
                    refine ⟨359021052297808989896981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61272926258826067609084757 359021052297808989896981)
                    ·
                      rfl

theorem cell23_2097573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_2097573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097573 prefixEnd_2097573 := by exact prefixLift 2097573
  have htrace : WordTrace (prefixWord ++ tailWord_2097573) baseStart_2097573 baseEnd_2097573 := by
    simpa [prefixWord, tailWord_2097573, baseEnd_2097573] using wordTrace_append hprefix tailTrace_2097573
  have hstable : (prefixWord ++ tailWord_2097573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097573).length < 2 ^ (prefixWord ++ tailWord_2097573).sum := by decide
  have hdescent : baseEnd_2097573 < baseStart_2097573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097583 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_2097583 : Nat := 118140960795 + 2097583 * 2 ^ 59
def prefixEnd_2097583 : Nat := 4983230072969 + 3 ^ 40 * 2097583 * 2
def baseEnd_2097583 : Nat := 1077068291699971930565897

theorem tailTrace_2097583 : CollatzResearch.WordTrace tailWord_2097583 prefixEnd_2097583 1077068291699971930565897 := by
  unfold tailWord_2097583
  simp only [CollatzResearch.WordTrace]
  refine ⟨76505137159822504500673403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51003424773215003000448935 76505137159822504500673403)
  ·
    refine ⟨114757705739733756751010105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76505137159822504500673403 114757705739733756751010105)
    ·
      refine ⟨86068279304800317563257579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114757705739733756751010105 86068279304800317563257579)
      ·
        refine ⟨129102418957200476344886369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86068279304800317563257579 129102418957200476344886369)
        ·
          refine ⟨96826814217900357258664777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129102418957200476344886369 96826814217900357258664777)
          ·
            refine ⟨72620110663425267943998583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96826814217900357258664777 72620110663425267943998583)
            ·
              refine ⟨108930165995137901915997875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72620110663425267943998583 108930165995137901915997875)
              ·
                refine ⟨163395248992706852873996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108930165995137901915997875 163395248992706852873996813)
                ·
                  refine ⟨61273218372265069827748805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163395248992706852873996813 61273218372265069827748805)
                  ·
                    refine ⟨11488728444799700592702901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61273218372265069827748805 11488728444799700592702901)
                    ·
                      refine ⟨1077068291699971930565897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11488728444799700592702901 1077068291699971930565897)
                      ·
                        rfl

theorem cell23_2097583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_2097583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097583 prefixEnd_2097583 := by exact prefixLift 2097583
  have htrace : WordTrace (prefixWord ++ tailWord_2097583) baseStart_2097583 baseEnd_2097583 := by
    simpa [prefixWord, tailWord_2097583, baseEnd_2097583] using wordTrace_append hprefix tailTrace_2097583
  have hstable : (prefixWord ++ tailWord_2097583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097583).length < 2 ^ (prefixWord ++ tailWord_2097583).sum := by decide
  have hdescent : baseEnd_2097583 < baseStart_2097583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097603 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 8]
def baseStart_2097603 : Nat := 118140960795 + 2097603 * 2 ^ 59
def prefixEnd_2097603 : Nat := 4983230072969 + 3 ^ 40 * 2097603 * 2
def baseEnd_2097603 : Nat := 359026187104353950771935

theorem tailTrace_2097603 : CollatzResearch.WordTrace tailWord_2097603 prefixEnd_2097603 359026187104353950771935 := by
  unfold tailWord_2097603
  simp only [CollatzResearch.WordTrace]
  refine ⟨76505866619750047916401463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51003911079833365277600975 76505866619750047916401463)
  ·
    refine ⟨114758799929625071874602195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76505866619750047916401463 114758799929625071874602195)
    ·
      refine ⟨172138199894437607811903293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114758799929625071874602195 172138199894437607811903293)
      ·
        refine ⟨64551824960414102929463735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172138199894437607811903293 64551824960414102929463735)
        ·
          refine ⟨96827737440621154394195603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64551824960414102929463735 96827737440621154394195603)
          ·
            refine ⟨145241606160931731591293405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96827737440621154394195603 145241606160931731591293405)
            ·
              refine ⟨54465602310349399346735027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145241606160931731591293405 54465602310349399346735027)
              ·
                refine ⟨81698403465524099020102541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54465602310349399346735027 81698403465524099020102541)
                ·
                  refine ⟨30636901299571537132538453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81698403465524099020102541 30636901299571537132538453)
                  ·
                    refine ⟨359026187104353950771935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30636901299571537132538453 359026187104353950771935)
                    ·
                      rfl

theorem cell23_2097603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_2097603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097603 prefixEnd_2097603 := by exact prefixLift 2097603
  have htrace : WordTrace (prefixWord ++ tailWord_2097603) baseStart_2097603 baseEnd_2097603 := by
    simpa [prefixWord, tailWord_2097603, baseEnd_2097603] using wordTrace_append hprefix tailTrace_2097603
  have hstable : (prefixWord ++ tailWord_2097603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097603).length < 2 ^ (prefixWord ++ tailWord_2097603).sum := by decide
  have hdescent : baseEnd_2097603 < baseStart_2097603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097621 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2097621 : Nat := 118140960795 + 2097621 * 2 ^ 59
def prefixEnd_2097621 : Nat := 4983230072969 + 3 ^ 40 * 2097621 * 2
def baseEnd_2097621 : Nat := 1077087803964842781890723

theorem tailTrace_2097621 : CollatzResearch.WordTrace tailWord_2097621 prefixEnd_2097621 1077087803964842781890723 := by
  unfold tailWord_2097621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76506523133684836990556717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51004348755789891327037811 76506523133684836990556717)
  ·
    refine ⟨28689946175131813871458769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76506523133684836990556717 28689946175131813871458769)
    ·
      refine ⟨21517459631348860403594077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28689946175131813871458769 21517459631348860403594077)
      ·
        refine ⟨8069047361755822651347779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21517459631348860403594077 8069047361755822651347779)
        ·
          refine ⟨12103571042633733977021669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8069047361755822651347779 12103571042633733977021669)
          ·
            refine ⟨2269419570493825120691563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12103571042633733977021669 2269419570493825120691563)
            ·
              refine ⟨3404129355740737681037345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269419570493825120691563 3404129355740737681037345)
              ·
                refine ⟨2553097016805553260778009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404129355740737681037345 2553097016805553260778009)
                ·
                  refine ⟨1914822762604164945583507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553097016805553260778009 1914822762604164945583507)
                  ·
                    refine ⟨2872234143906247418375261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914822762604164945583507 2872234143906247418375261)
                    ·
                      refine ⟨1077087803964842781890723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872234143906247418375261 1077087803964842781890723)
                      ·
                        rfl

theorem cell23_2097621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2097621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097621 prefixEnd_2097621 := by exact prefixLift 2097621
  have htrace : WordTrace (prefixWord ++ tailWord_2097621) baseStart_2097621 baseEnd_2097621 := by
    simpa [prefixWord, tailWord_2097621, baseEnd_2097621] using wordTrace_append hprefix tailTrace_2097621
  have hstable : (prefixWord ++ tailWord_2097621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097621).length < 2 ^ (prefixWord ++ tailWord_2097621).sum := by decide
  have hdescent : baseEnd_2097621 < baseStart_2097621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097684 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 7]
def baseStart_2097684 : Nat := 118140960795 + 2097684 * 2 ^ 59
def prefixEnd_2097684 : Nat := 4983230072969 + 3 ^ 40 * 2097684 * 2
def baseEnd_2097684 : Nat := 119680017027341781711437

theorem tailTrace_2097684 : CollatzResearch.WordTrace tailWord_2097684 prefixEnd_2097684 119680017027341781711437 := by
  unfold tailWord_2097684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38254410466228299375050053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51005880621637732500066737 38254410466228299375050053)
  ·
    refine ⟨7172701962417806132821885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38254410466228299375050053 7172701962417806132821885)
    ·
      refine ⟨2689763235906677299808207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7172701962417806132821885 2689763235906677299808207)
      ·
        refine ⟨4034644853860015949712311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689763235906677299808207 4034644853860015949712311)
        ·
          refine ⟨6051967280790023924568467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034644853860015949712311 6051967280790023924568467)
          ·
            refine ⟨9077950921185035886852701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051967280790023924568467 9077950921185035886852701)
            ·
              refine ⟨3404231595444388457569763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9077950921185035886852701 3404231595444388457569763)
              ·
                refine ⟨5106347393166582686354645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404231595444388457569763 5106347393166582686354645)
                ·
                  refine ⟨119680017027341781711437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5106347393166582686354645 119680017027341781711437)
                  ·
                    rfl

theorem cell23_2097684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_2097684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097684 prefixEnd_2097684 := by exact prefixLift 2097684
  have htrace : WordTrace (prefixWord ++ tailWord_2097684) baseStart_2097684 baseEnd_2097684 := by
    simpa [prefixWord, tailWord_2097684, baseEnd_2097684] using wordTrace_append hprefix tailTrace_2097684
  have hstable : (prefixWord ++ tailWord_2097684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097684).length < 2 ^ (prefixWord ++ tailWord_2097684).sum := by decide
  have hdescent : baseEnd_2097684 < baseStart_2097684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097690 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2097690 : Nat := 118140960795 + 2097690 * 2 ^ 59
def prefixEnd_2097690 : Nat := 4983230072969 + 3 ^ 40 * 2097690 * 2
def baseEnd_2097690 : Nat := 1077123234130003011927905

theorem tailTrace_2097690 : CollatzResearch.WordTrace tailWord_2097690 prefixEnd_2097690 1077123234130003011927905 := by
  unfold tailWord_2097690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19127259942608715443704631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51006026513623241183212349 19127259942608715443704631)
  ·
    refine ⟨28690889913913073165556947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19127259942608715443704631 28690889913913073165556947)
    ·
      refine ⟨43036334870869609748335421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28690889913913073165556947 43036334870869609748335421)
      ·
        refine ⟨16138625576576103655625783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43036334870869609748335421 16138625576576103655625783)
        ·
          refine ⟨24207938364864155483438675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16138625576576103655625783 24207938364864155483438675)
          ·
            refine ⟨36311907547296233225158013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24207938364864155483438675 36311907547296233225158013)
            ·
              refine ⟨13616965330236087459434255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36311907547296233225158013 13616965330236087459434255)
              ·
                refine ⟨20425447995354131189151383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13616965330236087459434255 20425447995354131189151383)
                ·
                  refine ⟨30638171993031196783727075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20425447995354131189151383 30638171993031196783727075)
                  ·
                    refine ⟨45957257989546795175590613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30638171993031196783727075 45957257989546795175590613)
                    ·
                      refine ⟨1077123234130003011927905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45957257989546795175590613 1077123234130003011927905)
                      ·
                        rfl

theorem cell23_2097690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2097690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097690 prefixEnd_2097690 := by exact prefixLift 2097690
  have htrace : WordTrace (prefixWord ++ tailWord_2097690) baseStart_2097690 baseEnd_2097690 := by
    simpa [prefixWord, tailWord_2097690, baseEnd_2097690] using wordTrace_append hprefix tailTrace_2097690
  have hstable : (prefixWord ++ tailWord_2097690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097690).length < 2 ^ (prefixWord ++ tailWord_2097690).sum := by decide
  have hdescent : baseEnd_2097690 < baseStart_2097690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097768 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2097768 : Nat := 118140960795 + 2097768 * 2 ^ 59
def prefixEnd_2097768 : Nat := 4983230072969 + 3 ^ 40 * 2097768 * 2
def baseEnd_2097768 : Nat := 1077163285621053706752547

theorem tailTrace_2097768 : CollatzResearch.WordTrace tailWord_2097768 prefixEnd_2097768 1077163285621053706752547 := by
  unfold tailWord_2097768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38255942332076140548078979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51007923109434854064105305 38255942332076140548078979)
  ·
    refine ⟨57383913498114210822118469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38255942332076140548078979 57383913498114210822118469)
    ·
      refine ⟨10759483780896414529147213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57383913498114210822118469 10759483780896414529147213)
      ·
        refine ⟨4034806417836155448430205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10759483780896414529147213 4034806417836155448430205)
        ·
          refine ⟨1513052406688558293161327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4034806417836155448430205 1513052406688558293161327)
          ·
            refine ⟨2269578610032837439741991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513052406688558293161327 2269578610032837439741991)
            ·
              refine ⟨3404367915049256159612987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269578610032837439741991 3404367915049256159612987)
              ·
                refine ⟨5106551872573884239419481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404367915049256159612987 5106551872573884239419481)
                ·
                  refine ⟨3829913904430413179564611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5106551872573884239419481 3829913904430413179564611)
                  ·
                    refine ⟨5744870856645619769346917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3829913904430413179564611 5744870856645619769346917)
                    ·
                      refine ⟨1077163285621053706752547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5744870856645619769346917 1077163285621053706752547)
                      ·
                        rfl

theorem cell23_2097768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2097768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097768 prefixEnd_2097768 := by exact prefixLift 2097768
  have htrace : WordTrace (prefixWord ++ tailWord_2097768) baseStart_2097768 baseEnd_2097768 := by
    simpa [prefixWord, tailWord_2097768, baseEnd_2097768] using wordTrace_append hprefix tailTrace_2097768
  have hstable : (prefixWord ++ tailWord_2097768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097768).length < 2 ^ (prefixWord ++ tailWord_2097768).sum := by decide
  have hdescent : baseEnd_2097768 < baseStart_2097768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097778 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_2097778 : Nat := 118140960795 + 2097778 * 2 ^ 59
def prefixEnd_2097778 : Nat := 4983230072969 + 3 ^ 40 * 2097778 * 2
def baseEnd_2097778 : Nat := 359056140142532889209167

theorem tailTrace_2097778 : CollatzResearch.WordTrace tailWord_2097778 prefixEnd_2097778 359056140142532889209167 := by
  unfold tailWord_2097778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128062348529013201005497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51008166262744035202681325 19128062348529013201005497)
  ·
    refine ⟨14346046761396759900754123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19128062348529013201005497 14346046761396759900754123)
    ·
      refine ⟨21519070142095139851131185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14346046761396759900754123 21519070142095139851131185)
      ·
        refine ⟨16139302606571354888348389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21519070142095139851131185 16139302606571354888348389)
        ·
          refine ⟨3026119238732129041565323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16139302606571354888348389 3026119238732129041565323)
          ·
            refine ⟨4539178858098193562347985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026119238732129041565323 4539178858098193562347985)
            ·
              refine ⟨3404384143573645171760989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539178858098193562347985 3404384143573645171760989)
              ·
                refine ⟨1276644053840116939410371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3404384143573645171760989 1276644053840116939410371)
                ·
                  refine ⟨1914966080760175409115557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276644053840116939410371 1914966080760175409115557)
                  ·
                    refine ⟨359056140142532889209167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914966080760175409115557 359056140142532889209167)
                    ·
                      rfl

theorem cell23_2097778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_2097778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097778 prefixEnd_2097778 := by exact prefixLift 2097778
  have htrace : WordTrace (prefixWord ++ tailWord_2097778) baseStart_2097778 baseEnd_2097778 := by
    simpa [prefixWord, tailWord_2097778, baseEnd_2097778] using wordTrace_append hprefix tailTrace_2097778
  have hstable : (prefixWord ++ tailWord_2097778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097778).length < 2 ^ (prefixWord ++ tailWord_2097778).sum := by decide
  have hdescent : baseEnd_2097778 < baseStart_2097778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097868 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_2097868 : Nat := 118140960795 + 2097868 * 2 ^ 59
def prefixEnd_2097868 : Nat := 4983230072969 + 3 ^ 40 * 2097868 * 2
def baseEnd_2097868 : Nat := 359071544562167771834029

theorem tailTrace_2097868 : CollatzResearch.WordTrace tailWord_2097868 prefixEnd_2097868 359071544562167771834029 := by
  unfold tailWord_2097868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38257765981894999087399129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51010354642526665449865505 38257765981894999087399129)
  ·
    refine ⟨28693324486421249315549347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38257765981894999087399129 28693324486421249315549347)
    ·
      refine ⟨43039986729631873973324021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28693324486421249315549347 43039986729631873973324021)
      ·
        refine ⟨4034998755902988184999127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43039986729631873973324021 4034998755902988184999127)
        ·
          refine ⟨6052498133854482277498691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034998755902988184999127 6052498133854482277498691)
          ·
            refine ⟨9078747200781723416248037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052498133854482277498691 9078747200781723416248037)
            ·
              refine ⟨1702265100146573140546507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9078747200781723416248037 1702265100146573140546507)
              ·
                refine ⟨2553397650219859710819761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702265100146573140546507 2553397650219859710819761)
                ·
                  refine ⟨1915048237664894783114821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553397650219859710819761 1915048237664894783114821)
                  ·
                    refine ⟨359071544562167771834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915048237664894783114821 359071544562167771834029)
                    ·
                      rfl

theorem cell23_2097868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_2097868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097868 prefixEnd_2097868 := by exact prefixLift 2097868
  have htrace : WordTrace (prefixWord ++ tailWord_2097868) baseStart_2097868 baseEnd_2097868 := by
    simpa [prefixWord, tailWord_2097868, baseEnd_2097868] using wordTrace_append hprefix tailTrace_2097868
  have hstable : (prefixWord ++ tailWord_2097868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097868).length < 2 ^ (prefixWord ++ tailWord_2097868).sum := by decide
  have hdescent : baseEnd_2097868 < baseStart_2097868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097891 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2097891 : Nat := 118140960795 + 2097891 * 2 ^ 59
def prefixEnd_2097891 : Nat := 4983230072969 + 3 ^ 40 * 2097891 * 2
def baseEnd_2097891 : Nat := 1077226443741556725514481

theorem tailTrace_2097891 : CollatzResearch.WordTrace tailWord_2097891 prefixEnd_2097891 1077226443741556725514481 := by
  unfold tailWord_2097891
  simp only [CollatzResearch.WordTrace]
  refine ⟨76516370842706673102885527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51010913895137782068590351 76516370842706673102885527)
  ·
    refine ⟨114774556264060009654328291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76516370842706673102885527 114774556264060009654328291)
    ·
      refine ⟨172161834396090014481492437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114774556264060009654328291 172161834396090014481492437)
      ·
        refine ⟨4035042993658359714409979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 172161834396090014481492437 4035042993658359714409979)
        ·
          refine ⟨6052564490487539571614969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035042993658359714409979 6052564490487539571614969)
          ·
            refine ⟨4539423367865654678711227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6052564490487539571614969 4539423367865654678711227)
            ·
              refine ⟨6809135051798482018066841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539423367865654678711227 6809135051798482018066841)
              ·
                refine ⟨5106851288848861513550131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6809135051798482018066841 5106851288848861513550131)
                ·
                  refine ⟨7660276933273292270325197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106851288848861513550131 7660276933273292270325197)
                  ·
                    refine ⟨2872603849977484601371949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7660276933273292270325197 2872603849977484601371949)
                    ·
                      refine ⟨1077226443741556725514481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872603849977484601371949 1077226443741556725514481)
                      ·
                        rfl

theorem cell23_2097891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2097891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097891 prefixEnd_2097891 := by exact prefixLift 2097891
  have htrace : WordTrace (prefixWord ++ tailWord_2097891) baseStart_2097891 baseEnd_2097891 := by
    simpa [prefixWord, tailWord_2097891, baseEnd_2097891] using wordTrace_append hprefix tailTrace_2097891
  have hstable : (prefixWord ++ tailWord_2097891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097891).length < 2 ^ (prefixWord ++ tailWord_2097891).sum := by decide
  have hdescent : baseEnd_2097891 < baseStart_2097891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097907 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 6]
def baseStart_2097907 : Nat := 118140960795 + 2097907 * 2 ^ 59
def prefixEnd_2097907 : Nat := 4983230072969 + 3 ^ 40 * 2097907 * 2
def baseEnd_2097907 : Nat := 359078219810676220971469

theorem tailTrace_2097907 : CollatzResearch.WordTrace tailWord_2097907 prefixEnd_2097907 359078219810676220971469 := by
  unfold tailWord_2097907
  simp only [CollatzResearch.WordTrace]
  refine ⟨76516954410648707835467975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51011302940432471890311983 76516954410648707835467975)
  ·
    refine ⟨114775431615973061753201963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76516954410648707835467975 114775431615973061753201963)
    ·
      refine ⟨172163147423959592629802945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114775431615973061753201963 172163147423959592629802945)
      ·
        refine ⟨129122360567969694472352209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172163147423959592629802945 129122360567969694472352209)
        ·
          refine ⟨96841770425977270854264157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129122360567969694472352209 96841770425977270854264157)
          ·
            refine ⟨36315663909741476570349059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96841770425977270854264157 36315663909741476570349059)
            ·
              refine ⟨54473495864612214855523589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36315663909741476570349059 54473495864612214855523589)
              ·
                refine ⟨10213780474614790285410673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54473495864612214855523589 10213780474614790285410673)
                ·
                  refine ⟨7660335355961092714058005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10213780474614790285410673 7660335355961092714058005)
                  ·
                    refine ⟨359078219810676220971469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7660335355961092714058005 359078219810676220971469)
                    ·
                      rfl

theorem cell23_2097907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_2097907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097907 prefixEnd_2097907 := by exact prefixLift 2097907
  have htrace : WordTrace (prefixWord ++ tailWord_2097907) baseStart_2097907 baseEnd_2097907 := by
    simpa [prefixWord, tailWord_2097907, baseEnd_2097907] using wordTrace_append hprefix tailTrace_2097907
  have hstable : (prefixWord ++ tailWord_2097907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097907).length < 2 ^ (prefixWord ++ tailWord_2097907).sum := by decide
  have hdescent : baseEnd_2097907 < baseStart_2097907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097918 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_2097918 : Nat := 118140960795 + 2097918 * 2 ^ 59
def prefixEnd_2097918 : Nat := 4983230072969 + 3 ^ 40 * 2097918 * 2
def baseEnd_2097918 : Nat := 1077240307719228119876857

theorem tailTrace_2097918 : CollatzResearch.WordTrace tailWord_2097918 prefixEnd_2097918 1077240307719228119876857 := by
  unfold tailWord_2097918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564669451701107089264801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51011570409072571142745605 9564669451701107089264801)
  ·
    refine ⟨7173502088775830316948601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9564669451701107089264801 7173502088775830316948601)
    ·
      refine ⟨5380126566581872737711451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7173502088775830316948601 5380126566581872737711451)
      ·
        refine ⟨8070189849872809106567177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380126566581872737711451 8070189849872809106567177)
        ·
          refine ⟨6052642387404606829925383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8070189849872809106567177 6052642387404606829925383)
          ·
            refine ⟨9078963581106910244888075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052642387404606829925383 9078963581106910244888075)
            ·
              refine ⟨13618445371660365367332113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9078963581106910244888075 13618445371660365367332113)
              ·
                refine ⟨10213834028745274025499085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13618445371660365367332113 10213834028745274025499085)
                ·
                  refine ⟨3830187760779477759562157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10213834028745274025499085 3830187760779477759562157)
                  ·
                    refine ⟨1436320410292304159835809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3830187760779477759562157 1436320410292304159835809)
                    ·
                      refine ⟨1077240307719228119876857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436320410292304159835809 1077240307719228119876857)
                      ·
                        rfl

theorem cell23_2097918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_2097918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097918 prefixEnd_2097918 := by exact prefixLift 2097918
  have htrace : WordTrace (prefixWord ++ tailWord_2097918) baseStart_2097918 baseEnd_2097918 := by
    simpa [prefixWord, tailWord_2097918, baseEnd_2097918] using wordTrace_append hprefix tailTrace_2097918
  have hstable : (prefixWord ++ tailWord_2097918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097918).length < 2 ^ (prefixWord ++ tailWord_2097918).sum := by decide
  have hdescent : baseEnd_2097918 < baseStart_2097918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097924 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_2097924 : Nat := 118140960795 + 2097924 * 2 ^ 59
def prefixEnd_2097924 : Nat := 4983230072969 + 3 ^ 40 * 2097924 * 2
def baseEnd_2097924 : Nat := 359081129534385032133943

theorem tailTrace_2097924 : CollatzResearch.WordTrace tailWord_2097924 prefixEnd_2097924 359081129534385032133943 := by
  unfold tailWord_2097924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38258787225793559869418413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51011716301058079825891217 38258787225793559869418413)
  ·
    refine ⟨14347045209672584951031905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38258787225793559869418413 14347045209672584951031905)
    ·
      refine ⟨10760283907254438713273929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14347045209672584951031905 10760283907254438713273929)
      ·
        refine ⟨8070212930440829034955447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760283907254438713273929 8070212930440829034955447)
        ·
          refine ⟨12105319395661243552433171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070212930440829034955447 12105319395661243552433171)
          ·
            refine ⟨18157979093491865328649757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12105319395661243552433171 18157979093491865328649757)
            ·
              refine ⟨6809242160059449498243659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18157979093491865328649757 6809242160059449498243659)
              ·
                refine ⟨10213863240089174247365489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6809242160059449498243659 10213863240089174247365489)
                ·
                  refine ⟨7660397430066880685524117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10213863240089174247365489 7660397430066880685524117)
                  ·
                    refine ⟨359081129534385032133943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7660397430066880685524117 359081129534385032133943)
                    ·
                      rfl

theorem cell23_2097924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_2097924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097924 prefixEnd_2097924 := by exact prefixLift 2097924
  have htrace : WordTrace (prefixWord ++ tailWord_2097924) baseStart_2097924 baseEnd_2097924 := by
    simpa [prefixWord, tailWord_2097924, baseEnd_2097924] using wordTrace_append hprefix tailTrace_2097924
  have hstable : (prefixWord ++ tailWord_2097924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097924).length < 2 ^ (prefixWord ++ tailWord_2097924).sum := by decide
  have hdescent : baseEnd_2097924 < baseStart_2097924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097931 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 6, 2, 2]
def baseStart_2097931 : Nat := 118140960795 + 2097931 * 2 ^ 59
def prefixEnd_2097931 : Nat := 4983230072969 + 3 ^ 40 * 2097931 * 2
def baseEnd_2097931 : Nat := 1077246982967736569014297

theorem tailTrace_2097931 : CollatzResearch.WordTrace tailWord_2097931 prefixEnd_2097931 1077246982967736569014297 := by
  unfold tailWord_2097931
  simp only [CollatzResearch.WordTrace]
  refine ⟨76517829762561759934341647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51011886508374506622894431 76517829762561759934341647)
  ·
    refine ⟨114776744643842639901512471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76517829762561759934341647 114776744643842639901512471)
    ·
      refine ⟨172165116965763959852268707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114776744643842639901512471 172165116965763959852268707)
      ·
        refine ⟨258247675448645939778403061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172165116965763959852268707 258247675448645939778403061)
        ·
          refine ⟨24210719573310556854225287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258247675448645939778403061 24210719573310556854225287)
          ·
            refine ⟨36316079359965835281337931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24210719573310556854225287 36316079359965835281337931)
            ·
              refine ⟨54474119039948752922006897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36316079359965835281337931 54474119039948752922006897)
              ·
                refine ⟨40855589279961564691505173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54474119039948752922006897 40855589279961564691505173)
                ·
                  refine ⟨1915105747498198344914305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40855589279961564691505173 1915105747498198344914305)
                  ·
                    refine ⟨1436329310623648758685729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915105747498198344914305 1436329310623648758685729)
                    ·
                      refine ⟨1077246982967736569014297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436329310623648758685729 1077246982967736569014297)
                      ·
                        rfl

theorem cell23_2097931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2, 2].length) (baseStart_2097931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097931 prefixEnd_2097931 := by exact prefixLift 2097931
  have htrace : WordTrace (prefixWord ++ tailWord_2097931) baseStart_2097931 baseEnd_2097931 := by
    simpa [prefixWord, tailWord_2097931, baseEnd_2097931] using wordTrace_append hprefix tailTrace_2097931
  have hstable : (prefixWord ++ tailWord_2097931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097931).length < 2 ^ (prefixWord ++ tailWord_2097931).sum := by decide
  have hdescent : baseEnd_2097931 < baseStart_2097931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097934 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2097934 : Nat := 118140960795 + 2097934 * 2 ^ 59
def prefixEnd_2097934 : Nat := 4983230072969 + 3 ^ 40 * 2097934 * 2
def baseEnd_2097934 : Nat := 1077248523409700057276783

theorem tailTrace_2097934 : CollatzResearch.WordTrace tailWord_2097934 prefixEnd_2097934 1077248523409700057276783 := by
  unfold tailWord_2097934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564742397693861430837607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51011959454367260964467237 9564742397693861430837607)
  ·
    refine ⟨14347113596540792146256411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564742397693861430837607 14347113596540792146256411)
    ·
      refine ⟨21520670394811188219384617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14347113596540792146256411 21520670394811188219384617)
      ·
        refine ⟨16140502796108391164538463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21520670394811188219384617 16140502796108391164538463)
        ·
          refine ⟨24210754194162586746807695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16140502796108391164538463 24210754194162586746807695)
          ·
            refine ⟨36316131291243880120211543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24210754194162586746807695 36316131291243880120211543)
            ·
              refine ⟨54474196936865820180317315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36316131291243880120211543 54474196936865820180317315)
              ·
                refine ⟨81711295405298730270475973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54474196936865820180317315 81711295405298730270475973)
                ·
                  refine ⟨15320867888493511925714245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81711295405298730270475973 15320867888493511925714245)
                  ·
                    refine ⟨2872662729092533486071421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15320867888493511925714245 2872662729092533486071421)
                    ·
                      refine ⟨1077248523409700057276783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872662729092533486071421 1077248523409700057276783)
                      ·
                        rfl

theorem cell23_2097934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2097934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097934 prefixEnd_2097934 := by exact prefixLift 2097934
  have htrace : WordTrace (prefixWord ++ tailWord_2097934) baseStart_2097934 baseEnd_2097934 := by
    simpa [prefixWord, tailWord_2097934, baseEnd_2097934] using wordTrace_append hprefix tailTrace_2097934
  have hstable : (prefixWord ++ tailWord_2097934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097934).length < 2 ^ (prefixWord ++ tailWord_2097934).sum := by decide
  have hdescent : baseEnd_2097934 < baseStart_2097934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097937 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 9]
def baseStart_2097937 : Nat := 118140960795 + 2097937 * 2 ^ 59
def prefixEnd_2097937 : Nat := 4983230072969 + 3 ^ 40 * 2097937 * 2
def baseEnd_2097937 : Nat := 119694451539073727282141

theorem tailTrace_2097937 : CollatzResearch.WordTrace tailWord_2097937 prefixEnd_2097937 119694451539073727282141 := by
  unfold tailWord_2097937
  simp only [CollatzResearch.WordTrace]
  refine ⟨76518048600540022959060065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51012032400360015306040043 76518048600540022959060065)
  ·
    refine ⟨57388536450405017219295049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76518048600540022959060065 57388536450405017219295049)
    ·
      refine ⟨43041402337803762914471287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57388536450405017219295049 43041402337803762914471287)
      ·
        refine ⟨64562103506705644371706931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43041402337803762914471287 64562103506705644371706931)
        ·
          refine ⟨96843155260058466557560397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64562103506705644371706931 96843155260058466557560397)
          ·
            refine ⟨36316183222521924959085149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96843155260058466557560397 36316183222521924959085149)
            ·
              refine ⟨13618568708445721859656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36316183222521924959085149 13618568708445721859656931)
              ·
                refine ⟨20427853062668582789485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13618568708445721859656931 20427853062668582789485397)
                ·
                  refine ⟨119694451539073727282141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20427853062668582789485397 119694451539073727282141)
                  ·
                    rfl

theorem cell23_2097937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_2097937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097937 prefixEnd_2097937 := by exact prefixLift 2097937
  have htrace : WordTrace (prefixWord ++ tailWord_2097937) baseStart_2097937 baseEnd_2097937 := by
    simpa [prefixWord, tailWord_2097937, baseEnd_2097937] using wordTrace_append hprefix tailTrace_2097937
  have hstable : (prefixWord ++ tailWord_2097937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097937).length < 2 ^ (prefixWord ++ tailWord_2097937).sum := by decide
  have hdescent : baseEnd_2097937 < baseStart_2097937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097964 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_2097964 : Nat := 118140960795 + 2097964 * 2 ^ 59
def prefixEnd_2097964 : Nat := 4983230072969 + 3 ^ 40 * 2097964 * 2
def baseEnd_2097964 : Nat := 1077263927829334939901645

theorem tailTrace_2097964 : CollatzResearch.WordTrace tailWord_2097964 prefixEnd_2097964 1077263927829334939901645 := by
  unfold tailWord_2097964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38259516685721103285146473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51012688914294804380195297 38259516685721103285146473)
  ·
    refine ⟨28694637514290827463859855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38259516685721103285146473 28694637514290827463859855)
    ·
      refine ⟨43041956271436241195789783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28694637514290827463859855 43041956271436241195789783)
      ·
        refine ⟨64562934407154361793684675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43041956271436241195789783 64562934407154361793684675)
        ·
          refine ⟨96844401610731542690527013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64562934407154361793684675 96844401610731542690527013)
          ·
            refine ⟨18158325302012164254473815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96844401610731542690527013 18158325302012164254473815)
            ·
              refine ⟨27237487953018246381710723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18158325302012164254473815 27237487953018246381710723)
              ·
                refine ⟨40856231929527369572566085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27237487953018246381710723 40856231929527369572566085)
                ·
                  refine ⟨7660543486786381794856141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40856231929527369572566085 7660543486786381794856141)
                  ·
                    refine ⟨2872703807544893173071053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7660543486786381794856141 2872703807544893173071053)
                    ·
                      refine ⟨1077263927829334939901645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872703807544893173071053 1077263927829334939901645)
                      ·
                        rfl

theorem cell23_2097964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_2097964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097964 prefixEnd_2097964 := by exact prefixLift 2097964
  have htrace : WordTrace (prefixWord ++ tailWord_2097964) baseStart_2097964 baseEnd_2097964 := by
    simpa [prefixWord, tailWord_2097964, baseEnd_2097964] using wordTrace_append hprefix tailTrace_2097964
  have hstable : (prefixWord ++ tailWord_2097964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097964).length < 2 ^ (prefixWord ++ tailWord_2097964).sum := by decide
  have hdescent : baseEnd_2097964 < baseStart_2097964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097967 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 7]
def baseStart_2097967 : Nat := 118140960795 + 2097967 * 2 ^ 59
def prefixEnd_2097967 : Nat := 4983230072969 + 3 ^ 40 * 2097967 * 2
def baseEnd_2097967 : Nat := 359088489423766142721377

theorem tailTrace_2097967 : CollatzResearch.WordTrace tailWord_2097967 prefixEnd_2097967 359088489423766142721377 := by
  unfold tailWord_2097967
  simp only [CollatzResearch.WordTrace]
  refine ⟨76519142790431338082652155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51012761860287558721768103 76519142790431338082652155)
  ·
    refine ⟨114778714185647007123978233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76519142790431338082652155 114778714185647007123978233)
    ·
      refine ⟨86084035639235255342983675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114778714185647007123978233 86084035639235255342983675)
      ·
        refine ⟨129126053458852883014475513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86084035639235255342983675 129126053458852883014475513)
        ·
          refine ⟨96844540094139662260856635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129126053458852883014475513 96844540094139662260856635)
          ·
            refine ⟨145266810141209493391284953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96844540094139662260856635 145266810141209493391284953)
            ·
              refine ⟨108950107605907120043463715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145266810141209493391284953 108950107605907120043463715)
              ·
                refine ⟨163425161408860680065195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108950107605907120043463715 163425161408860680065195573)
                ·
                  refine ⟨15321108882080688756112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163425161408860680065195573 15321108882080688756112085)
                  ·
                    refine ⟨359088489423766142721377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15321108882080688756112085 359088489423766142721377)
                    ·
                      rfl

theorem cell23_2097967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_2097967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097967 prefixEnd_2097967 := by exact prefixLift 2097967
  have htrace : WordTrace (prefixWord ++ tailWord_2097967) baseStart_2097967 baseEnd_2097967 := by
    simpa [prefixWord, tailWord_2097967, baseEnd_2097967] using wordTrace_append hprefix tailTrace_2097967
  have hstable : (prefixWord ++ tailWord_2097967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097967).length < 2 ^ (prefixWord ++ tailWord_2097967).sum := by decide
  have hdescent : baseEnd_2097967 < baseStart_2097967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097971 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 5]
def baseStart_2097971 : Nat := 118140960795 + 2097971 * 2 ^ 59
def prefixEnd_2097971 : Nat := 4983230072969 + 3 ^ 40 * 2097971 * 2
def baseEnd_2097971 : Nat := 119696391354879601390457

theorem tailTrace_2097971 : CollatzResearch.WordTrace tailWord_2097971 prefixEnd_2097971 119696391354879601390457 := by
  unfold tailWord_2097971
  simp only [CollatzResearch.WordTrace]
  refine ⟨76519288682416846765797767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51012859121611231177198511 76519288682416846765797767)
  ·
    refine ⟨114778933023625270148696651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76519288682416846765797767 114778933023625270148696651)
    ·
      refine ⟨172168399535437905223044977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114778933023625270148696651 172168399535437905223044977)
      ·
        refine ⟨129126299651578428917283733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172168399535437905223044977 129126299651578428917283733)
        ·
          refine ⟨6052795296167738855497675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129126299651578428917283733 6052795296167738855497675)
          ·
            refine ⟨9079192944251608283246513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052795296167738855497675 9079192944251608283246513)
            ·
              refine ⟨6809394708188706212434885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9079192944251608283246513 6809394708188706212434885)
              ·
                refine ⟨1276761507785382414831541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6809394708188706212434885 1276761507785382414831541)
                ·
                  refine ⟨119696391354879601390457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276761507785382414831541 119696391354879601390457)
                  ·
                    rfl

theorem cell23_2097971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 5].length) (baseStart_2097971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097971 prefixEnd_2097971 := by exact prefixLift 2097971
  have htrace : WordTrace (prefixWord ++ tailWord_2097971) baseStart_2097971 baseEnd_2097971 := by
    simpa [prefixWord, tailWord_2097971, baseEnd_2097971] using wordTrace_append hprefix tailTrace_2097971
  have hstable : (prefixWord ++ tailWord_2097971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097971).length < 2 ^ (prefixWord ++ tailWord_2097971).sum := by decide
  have hdescent : baseEnd_2097971 < baseStart_2097971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097982 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2097982 : Nat := 118140960795 + 2097982 * 2 ^ 59
def prefixEnd_2097982 : Nat := 4983230072969 + 3 ^ 40 * 2097982 * 2
def baseEnd_2097982 : Nat := 1077273170481115869476563

theorem tailTrace_2097982 : CollatzResearch.WordTrace tailWord_2097982 prefixEnd_2097982 1077273170481115869476563 := by
  unfold tailWord_2097982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564961235672124455556025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51013126590251330429632133 9564961235672124455556025)
  ·
    refine ⟨7173720926754093341667019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9564961235672124455556025 7173720926754093341667019)
    ·
      refine ⟨10760581390131140012500529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7173720926754093341667019 10760581390131140012500529)
      ·
        refine ⟨8070436042598355009375397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760581390131140012500529 8070436042598355009375397)
        ·
          refine ⟨1513206757987191564257887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8070436042598355009375397 1513206757987191564257887)
          ·
            refine ⟨2269810136980787346386831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513206757987191564257887 2269810136980787346386831)
            ·
              refine ⟨3404715205471181019580247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269810136980787346386831 3404715205471181019580247)
              ·
                refine ⟨5107072808206771529370371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404715205471181019580247 5107072808206771529370371)
                ·
                  refine ⟨7660609212310157294055557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5107072808206771529370371 7660609212310157294055557)
                  ·
                    refine ⟨1436364227308154492635417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7660609212310157294055557 1436364227308154492635417)
                    ·
                      refine ⟨1077273170481115869476563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436364227308154492635417 1077273170481115869476563)
                      ·
                        rfl

theorem cell23_2097982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2097982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2097982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2097982 prefixEnd_2097982 := by exact prefixLift 2097982
  have htrace : WordTrace (prefixWord ++ tailWord_2097982) baseStart_2097982 baseEnd_2097982 := by
    simpa [prefixWord, tailWord_2097982, baseEnd_2097982] using wordTrace_append hprefix tailTrace_2097982
  have hstable : (prefixWord ++ tailWord_2097982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097982).length < 2 ^ (prefixWord ++ tailWord_2097982).sum := by decide
  have hdescent : baseEnd_2097982 < baseStart_2097982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098018 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2098018 : Nat := 118140960795 + 2098018 * 2 ^ 59
def prefixEnd_2098018 : Nat := 4983230072969 + 3 ^ 40 * 2098018 * 2
def baseEnd_2098018 : Nat := 359097218594892576208799

theorem tailTrace_2098018 : CollatzResearch.WordTrace tailWord_2098018 prefixEnd_2098018 359097218594892576208799 := by
  unfold tailWord_2098018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130250728311643448189677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51014001942164382528505805 19130250728311643448189677)
  ·
    refine ⟨7173844023116866293071129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19130250728311643448189677 7173844023116866293071129)
    ·
      refine ⟨5380383017337649719803347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7173844023116866293071129 5380383017337649719803347)
      ·
        refine ⟨8070574526006474579705021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380383017337649719803347 8070574526006474579705021)
        ·
          refine ⟨3026465447252427967389383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8070574526006474579705021 3026465447252427967389383)
          ·
            refine ⟨4539698170878641951084075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026465447252427967389383 4539698170878641951084075)
            ·
              refine ⟨6809547256317962926626113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539698170878641951084075 6809547256317962926626113)
              ·
                refine ⟨5107160442238472194969585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6809547256317962926626113 5107160442238472194969585)
                ·
                  refine ⟨3830370331678854146227189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107160442238472194969585 3830370331678854146227189)
                  ·
                    refine ⟨359097218594892576208799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3830370331678854146227189 359097218594892576208799)
                    ·
                      rfl

theorem cell23_2098018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2098018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098018 prefixEnd_2098018 := by exact prefixLift 2098018
  have htrace : WordTrace (prefixWord ++ tailWord_2098018) baseStart_2098018 baseEnd_2098018 := by
    simpa [prefixWord, tailWord_2098018, baseEnd_2098018] using wordTrace_append hprefix tailTrace_2098018
  have hstable : (prefixWord ++ tailWord_2098018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098018).length < 2 ^ (prefixWord ++ tailWord_2098018).sum := by decide
  have hdescent : baseEnd_2098018 < baseStart_2098018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098021 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_2098021 : Nat := 118140960795 + 2098021 * 2 ^ 59
def prefixEnd_2098021 : Nat := 4983230072969 + 3 ^ 40 * 2098021 * 2
def baseEnd_2098021 : Nat := 1077293196226641216888883

theorem tailTrace_2098021 : CollatzResearch.WordTrace tailWord_2098021 prefixEnd_2098021 1077293196226641216888883 := by
  unfold tailWord_2098021
  simp only [CollatzResearch.WordTrace]
  refine ⟨76521112332235705305117917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51014074888157136870078611 76521112332235705305117917)
  ·
    refine ⟨28695417124588389489419219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76521112332235705305117917 28695417124588389489419219)
    ·
      refine ⟨43043125686882584234128829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28695417124588389489419219 43043125686882584234128829)
      ·
        refine ⟨16141172132580969087798311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43043125686882584234128829 16141172132580969087798311)
        ·
          refine ⟨24211758198871453631697467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16141172132580969087798311 24211758198871453631697467)
          ·
            refine ⟨36317637298307180447546201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24211758198871453631697467 36317637298307180447546201)
            ·
              refine ⟨27238227973730385335659651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36317637298307180447546201 27238227973730385335659651)
              ·
                refine ⟨40857341960595578003489477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27238227973730385335659651 40857341960595578003489477)
                ·
                  refine ⟨7660751617611670875654277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40857341960595578003489477 7660751617611670875654277)
                  ·
                    refine ⟨1436390928302188289185177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7660751617611670875654277 1436390928302188289185177)
                    ·
                      refine ⟨1077293196226641216888883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436390928302188289185177 1077293196226641216888883)
                      ·
                        rfl

theorem cell23_2098021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_2098021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098021 prefixEnd_2098021 := by exact prefixLift 2098021
  have htrace : WordTrace (prefixWord ++ tailWord_2098021) baseStart_2098021 baseEnd_2098021 := by
    simpa [prefixWord, tailWord_2098021, baseEnd_2098021] using wordTrace_append hprefix tailTrace_2098021
  have hstable : (prefixWord ++ tailWord_2098021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098021).length < 2 ^ (prefixWord ++ tailWord_2098021).sum := by decide
  have hdescent : baseEnd_2098021 < baseStart_2098021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098034 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2098034 : Nat := 118140960795 + 2098034 * 2 ^ 59
def prefixEnd_2098034 : Nat := 4983230072969 + 3 ^ 40 * 2098034 * 2
def baseEnd_2098034 : Nat := 1077299871475149666026323

theorem tailTrace_2098034 : CollatzResearch.WordTrace tailWord_2098034 prefixEnd_2098034 1077299871475149666026323 := by
  unfold tailWord_2098034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130396620297152131335289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51014390987459072350227437 19130396620297152131335289)
  ·
    refine ⟨14347797465222864098501467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19130396620297152131335289 14347797465222864098501467)
    ·
      refine ⟨21521696197834296147752201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14347797465222864098501467 21521696197834296147752201)
      ·
        refine ⟨16141272148375722110814151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21521696197834296147752201 16141272148375722110814151)
        ·
          refine ⟨24211908222563583166221227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16141272148375722110814151 24211908222563583166221227)
          ·
            refine ⟨36317862333845374749331841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24211908222563583166221227 36317862333845374749331841)
            ·
              refine ⟨27238396750384031061998881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36317862333845374749331841 27238396750384031061998881)
              ·
                refine ⟨20428797562788023296499161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27238396750384031061998881 20428797562788023296499161)
                ·
                  refine ⟨15321598172091017472374371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20428797562788023296499161 15321598172091017472374371)
                  ·
                    refine ⟨22982397258136526208561557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15321598172091017472374371 22982397258136526208561557)
                    ·
                      refine ⟨1077299871475149666026323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22982397258136526208561557 1077299871475149666026323)
                      ·
                        rfl

theorem cell23_2098034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2098034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098034 prefixEnd_2098034 := by exact prefixLift 2098034
  have htrace : WordTrace (prefixWord ++ tailWord_2098034) baseStart_2098034 baseEnd_2098034 := by
    simpa [prefixWord, tailWord_2098034, baseEnd_2098034] using wordTrace_append hprefix tailTrace_2098034
  have hstable : (prefixWord ++ tailWord_2098034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098034).length < 2 ^ (prefixWord ++ tailWord_2098034).sum := by decide
  have hdescent : baseEnd_2098034 < baseStart_2098034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098058 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2098058 : Nat := 118140960795 + 2098058 * 2 ^ 59
def prefixEnd_2098058 : Nat := 4983230072969 + 3 ^ 40 * 2098058 * 2
def baseEnd_2098058 : Nat := 1077312195010857572126213

theorem tailTrace_2098058 : CollatzResearch.WordTrace tailWord_2098058 prefixEnd_2098058 1077312195010857572126213 := by
  unfold tailWord_2098058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130615458275415156053707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51014974555401107082809885 19130615458275415156053707)
  ·
    refine ⟨28695923187413122734080561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19130615458275415156053707 28695923187413122734080561)
    ·
      refine ⟨21521942390559842050560421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28695923187413122734080561 21521942390559842050560421)
      ·
        refine ⟨4035364198229970384480079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21521942390559842050560421 4035364198229970384480079)
        ·
          refine ⟨6053046297344955576720119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035364198229970384480079 6053046297344955576720119)
          ·
            refine ⟨9079569446017433365080179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053046297344955576720119 9079569446017433365080179)
            ·
              refine ⟨13619354169026150047620269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9079569446017433365080179 13619354169026150047620269)
              ·
                refine ⟨5107257813384806267857601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13619354169026150047620269 5107257813384806267857601)
                ·
                  refine ⟨3830443360038604700893201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107257813384806267857601 3830443360038604700893201)
                  ·
                    refine ⟨2872832520028953525669901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3830443360038604700893201 2872832520028953525669901)
                    ·
                      refine ⟨1077312195010857572126213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2872832520028953525669901 1077312195010857572126213)
                      ·
                        rfl

theorem cell23_2098058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2098058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098058 prefixEnd_2098058 := by exact prefixLift 2098058
  have htrace : WordTrace (prefixWord ++ tailWord_2098058) baseStart_2098058 baseEnd_2098058 := by
    simpa [prefixWord, tailWord_2098058, baseEnd_2098058] using wordTrace_append hprefix tailTrace_2098058
  have hstable : (prefixWord ++ tailWord_2098058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098058).length < 2 ^ (prefixWord ++ tailWord_2098058).sum := by decide
  have hdescent : baseEnd_2098058 < baseStart_2098058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098082 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2098082 : Nat := 118140960795 + 2098082 * 2 ^ 59
def prefixEnd_2098082 : Nat := 4983230072969 + 3 ^ 40 * 2098082 * 2
def baseEnd_2098082 : Nat := 359108172848855159408701

theorem tailTrace_2098082 : CollatzResearch.WordTrace tailWord_2098082 prefixEnd_2098082 359108172848855159408701 := by
  unfold tailWord_2098082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130834296253678180772125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51015558123343141815392333 19130834296253678180772125)
  ·
    refine ⟨7174062861095129317789547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19130834296253678180772125 7174062861095129317789547)
    ·
      refine ⟨10761094291642693976684321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7174062861095129317789547 10761094291642693976684321)
      ·
        refine ⟨8070820718732020482513241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10761094291642693976684321 8070820718732020482513241)
        ·
          refine ⟨6053115539049015361884931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8070820718732020482513241 6053115539049015361884931)
          ·
            refine ⟨9079673308573523042827397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053115539049015361884931 9079673308573523042827397)
            ·
              refine ⟨1702438745357535570530137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9079673308573523042827397 1702438745357535570530137)
              ·
                refine ⟨1276829059018151677897603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702438745357535570530137 1276829059018151677897603)
                ·
                  refine ⟨1915243588527227516846405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276829059018151677897603 1915243588527227516846405)
                  ·
                    refine ⟨359108172848855159408701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915243588527227516846405 359108172848855159408701)
                    ·
                      rfl

theorem cell23_2098082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2098082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098082 prefixEnd_2098082 := by exact prefixLift 2098082
  have htrace : WordTrace (prefixWord ++ tailWord_2098082) baseStart_2098082 baseEnd_2098082 := by
    simpa [prefixWord, tailWord_2098082, baseEnd_2098082] using wordTrace_append hprefix tailTrace_2098082
  have hstable : (prefixWord ++ tailWord_2098082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098082).length < 2 ^ (prefixWord ++ tailWord_2098082).sum := by decide
  have hdescent : baseEnd_2098082 < baseStart_2098082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098111 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 8, 2]
def baseStart_2098111 : Nat := 118140960795 + 2098111 * 2 ^ 59
def prefixEnd_2098111 : Nat := 4983230072969 + 3 ^ 40 * 2098111 * 2
def baseEnd_2098111 : Nat := 1077339409485545864763469

theorem tailTrace_2098111 : CollatzResearch.WordTrace tailWord_2098111 prefixEnd_2098111 1077339409485545864763469 := by
  unfold tailWord_2098111
  simp only [CollatzResearch.WordTrace]
  refine ⟨76524394901909650675894187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51016263267939767117262791 76524394901909650675894187)
  ·
    refine ⟨114786592352864476013841281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76524394901909650675894187 114786592352864476013841281)
    ·
      refine ⟨86089944264648357010380961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114786592352864476013841281 86089944264648357010380961)
      ·
        refine ⟨64567458198486267757785721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86089944264648357010380961 64567458198486267757785721)
        ·
          refine ⟨48425593648864700818339291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64567458198486267757785721 48425593648864700818339291)
          ·
            refine ⟨72638390473297051227508937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48425593648864700818339291 72638390473297051227508937)
            ·
              refine ⟨54478792854972788420631703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72638390473297051227508937 54478792854972788420631703)
              ·
                refine ⟨81718189282459182630947555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54478792854972788420631703 81718189282459182630947555)
                ·
                  refine ⟨122577283923688773946421333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81718189282459182630947555 122577283923688773946421333)
                  ·
                    refine ⟨1436452545980727819684625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122577283923688773946421333 1436452545980727819684625)
                    ·
                      refine ⟨1077339409485545864763469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436452545980727819684625 1077339409485545864763469)
                      ·
                        rfl

theorem cell23_2098111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_2098111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098111 prefixEnd_2098111 := by exact prefixLift 2098111
  have htrace : WordTrace (prefixWord ++ tailWord_2098111) baseStart_2098111 baseEnd_2098111 := by
    simpa [prefixWord, tailWord_2098111, baseEnd_2098111] using wordTrace_append hprefix tailTrace_2098111
  have hstable : (prefixWord ++ tailWord_2098111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098111).length < 2 ^ (prefixWord ++ tailWord_2098111).sum := by decide
  have hdescent : baseEnd_2098111 < baseStart_2098111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098128 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2]
def baseStart_2098128 : Nat := 118140960795 + 2098128 * 2 ^ 59
def prefixEnd_2098128 : Nat := 4983230072969 + 3 ^ 40 * 2098128 * 2
def baseEnd_2098128 : Nat := 1077348138656672298250891

theorem tailTrace_2098128 : CollatzResearch.WordTrace tailWord_2098128 prefixEnd_2098128 1077348138656672298250891 := by
  unfold tailWord_2098128
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262507471424031289631519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51016676628565375052842025 38262507471424031289631519)
  ·
    refine ⟨57393761207136046934447279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38262507471424031289631519 57393761207136046934447279)
    ·
      refine ⟨86090641810704070401670919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57393761207136046934447279 86090641810704070401670919)
      ·
        refine ⟨129135962716056105602506379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86090641810704070401670919 129135962716056105602506379)
        ·
          refine ⟨193703944074084158403759569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129135962716056105602506379 193703944074084158403759569)
          ·
            refine ⟨145277958055563118802819677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193703944074084158403759569 145277958055563118802819677)
            ·
              refine ⟨54479234270836169551057379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145277958055563118802819677 54479234270836169551057379)
              ·
                refine ⟨81718851406254254326586069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54479234270836169551057379 81718851406254254326586069)
                ·
                  refine ⟨1915285579834084085779361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81718851406254254326586069 1915285579834084085779361)
                  ·
                    refine ⟨1436464184875563064334521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915285579834084085779361 1436464184875563064334521)
                    ·
                      refine ⟨1077348138656672298250891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436464184875563064334521 1077348138656672298250891)
                      ·
                        rfl

theorem cell23_2098128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2].length) (baseStart_2098128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098128 prefixEnd_2098128 := by exact prefixLift 2098128
  have htrace : WordTrace (prefixWord ++ tailWord_2098128) baseStart_2098128 baseEnd_2098128 := by
    simpa [prefixWord, tailWord_2098128, baseEnd_2098128] using wordTrace_append hprefix tailTrace_2098128
  have hstable : (prefixWord ++ tailWord_2098128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098128).length < 2 ^ (prefixWord ++ tailWord_2098128).sum := by decide
  have hdescent : baseEnd_2098128 < baseStart_2098128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098138 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_2098138 : Nat := 118140960795 + 2098138 * 2 ^ 59
def prefixEnd_2098138 : Nat := 4983230072969 + 3 ^ 40 * 2098138 * 2
def baseEnd_2098138 : Nat := 359117757821072419708615

theorem tailTrace_2098138 : CollatzResearch.WordTrace tailWord_2098138 prefixEnd_2098138 359117757821072419708615 := by
  unfold tailWord_2098138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131344918202958571781767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51016919781874556191418045 19131344918202958571781767)
  ·
    refine ⟨28697017377304437857672651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19131344918202958571781767 28697017377304437857672651)
    ·
      refine ⟨43045526065956656786508977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28697017377304437857672651 43045526065956656786508977)
      ·
        refine ⟨32284144549467492589881733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43045526065956656786508977 32284144549467492589881733)
        ·
          refine ⟨6053277103025154860602825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32284144549467492589881733 6053277103025154860602825)
          ·
            refine ⟨4539957827268866145452119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053277103025154860602825 4539957827268866145452119)
            ·
              refine ⟨6809936740903299218178179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539957827268866145452119 6809936740903299218178179)
              ·
                refine ⟨10214905111354948827267269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6809936740903299218178179 10214905111354948827267269)
                ·
                  refine ⟨1915294708379052905112613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10214905111354948827267269 1915294708379052905112613)
                  ·
                    refine ⟨359117757821072419708615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915294708379052905112613 359117757821072419708615)
                    ·
                      rfl

theorem cell23_2098138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_2098138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098138 prefixEnd_2098138 := by exact prefixLift 2098138
  have htrace : WordTrace (prefixWord ++ tailWord_2098138) baseStart_2098138 baseEnd_2098138 := by
    simpa [prefixWord, tailWord_2098138, baseEnd_2098138] using wordTrace_append hprefix tailTrace_2098138
  have hstable : (prefixWord ++ tailWord_2098138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098138).length < 2 ^ (prefixWord ++ tailWord_2098138).sum := by decide
  have hdescent : baseEnd_2098138 < baseStart_2098138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098144 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2098144 : Nat := 118140960795 + 2098144 * 2 ^ 59
def prefixEnd_2098144 : Nat := 4983230072969 + 3 ^ 40 * 2098144 * 2
def baseEnd_2098144 : Nat := 1077356354347144235650817

theorem tailTrace_2098144 : CollatzResearch.WordTrace tailWord_2098144 prefixEnd_2098144 1077356354347144235650817 := by
  unfold tailWord_2098144
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262799255395048655922743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51017065673860064874563657 38262799255395048655922743)
  ·
    refine ⟨57394198883092572983884115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38262799255395048655922743 57394198883092572983884115)
    ·
      refine ⟨86091298324638859475826173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57394198883092572983884115 86091298324638859475826173)
      ·
        refine ⟨32284236871739572303434815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86091298324638859475826173 32284236871739572303434815)
        ·
          refine ⟨48426355307609358455152223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32284236871739572303434815 48426355307609358455152223)
          ·
            refine ⟨72639532961414037682728335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48426355307609358455152223 72639532961414037682728335)
            ·
              refine ⟨108959299442121056524092503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72639532961414037682728335 108959299442121056524092503)
              ·
                refine ⟨163438949163181584786138755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108959299442121056524092503 163438949163181584786138755)
                ·
                  refine ⟨245158423744772377179208133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163438949163181584786138755 245158423744772377179208133)
                  ·
                    refine ⟨45967204452144820721101525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245158423744772377179208133 45967204452144820721101525)
                    ·
                      refine ⟨1077356354347144235650817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45967204452144820721101525 1077356354347144235650817)
                      ·
                        rfl

theorem cell23_2098144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2098144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098144 prefixEnd_2098144 := by exact prefixLift 2098144
  have htrace : WordTrace (prefixWord ++ tailWord_2098144) baseStart_2098144 baseEnd_2098144 := by
    simpa [prefixWord, tailWord_2098144, baseEnd_2098144] using wordTrace_append hprefix tailTrace_2098144
  have hstable : (prefixWord ++ tailWord_2098144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098144).length < 2 ^ (prefixWord ++ tailWord_2098144).sum := by decide
  have hdescent : baseEnd_2098144 < baseStart_2098144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098158 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2098158 : Nat := 118140960795 + 2098158 * 2 ^ 59
def prefixEnd_2098158 : Nat := 4983230072969 + 3 ^ 40 * 2098158 * 2
def baseEnd_2098158 : Nat := 1077363543076307180875753

theorem tailTrace_2098158 : CollatzResearch.WordTrace tailWord_2098158 prefixEnd_2098158 1077363543076307180875753 := by
  unfold tailWord_2098158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9565763641592422212856891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51017406088492918468570085 9565763641592422212856891)
  ·
    refine ⟨14348645462388633319285337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9565763641592422212856891 14348645462388633319285337)
    ·
      refine ⟨10761484096791474989464003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14348645462388633319285337 10761484096791474989464003)
      ·
        refine ⟨16142226145187212484196005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10761484096791474989464003 16142226145187212484196005)
        ·
          refine ⟨3026667402222602340786751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16142226145187212484196005 3026667402222602340786751)
          ·
            refine ⟨4540001103333903511180127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026667402222602340786751 4540001103333903511180127)
            ·
              refine ⟨6810001655000855266770191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540001103333903511180127 6810001655000855266770191)
              ·
                refine ⟨10215002482501282900155287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6810001655000855266770191 10215002482501282900155287)
                ·
                  refine ⟨15322503723751924350232931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10215002482501282900155287 15322503723751924350232931)
                  ·
                    refine ⟨22983755585627886525349397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15322503723751924350232931 22983755585627886525349397)
                    ·
                      refine ⟨1077363543076307180875753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22983755585627886525349397 1077363543076307180875753)
                      ·
                        rfl

theorem cell23_2098158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2098158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098158 prefixEnd_2098158 := by exact prefixLift 2098158
  have htrace : WordTrace (prefixWord ++ tailWord_2098158) baseStart_2098158 baseEnd_2098158 := by
    simpa [prefixWord, tailWord_2098158, baseEnd_2098158] using wordTrace_append hprefix tailTrace_2098158
  have hstable : (prefixWord ++ tailWord_2098158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098158).length < 2 ^ (prefixWord ++ tailWord_2098158).sum := by decide
  have hdescent : baseEnd_2098158 < baseStart_2098158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098162 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2098162 : Nat := 118140960795 + 2098162 * 2 ^ 59
def prefixEnd_2098162 : Nat := 4983230072969 + 3 ^ 40 * 2098162 * 2
def baseEnd_2098162 : Nat := 1077365596998925165225735

theorem tailTrace_2098162 : CollatzResearch.WordTrace tailWord_2098162 prefixEnd_2098162 1077365596998925165225735 := by
  unfold tailWord_2098162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131563756181221596500185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51017503349816590924000493 19131563756181221596500185)
  ·
    refine ⟨14348672817135916197375139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19131563756181221596500185 14348672817135916197375139)
    ·
      refine ⟨21523009225703874296062709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14348672817135916197375139 21523009225703874296062709)
      ·
        refine ⟨2017782114909738215255879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21523009225703874296062709 2017782114909738215255879)
        ·
          refine ⟨3026673172364607322883819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017782114909738215255879 3026673172364607322883819)
          ·
            refine ⟨4540009758546910984325729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026673172364607322883819 4540009758546910984325729)
            ·
              refine ⟨3405007318910183238244297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540009758546910984325729 3405007318910183238244297)
              ·
                refine ⟨2553755489182637428683223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405007318910183238244297 2553755489182637428683223)
                ·
                  refine ⟨3830633233773956143024835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553755489182637428683223 3830633233773956143024835)
                  ·
                    refine ⟨5745949850660934214537253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3830633233773956143024835 5745949850660934214537253)
                    ·
                      refine ⟨1077365596998925165225735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5745949850660934214537253 1077365596998925165225735)
                      ·
                        rfl

theorem cell23_2098162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2098162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098162 prefixEnd_2098162 := by exact prefixLift 2098162
  have htrace : WordTrace (prefixWord ++ tailWord_2098162) baseStart_2098162 baseEnd_2098162 := by
    simpa [prefixWord, tailWord_2098162, baseEnd_2098162] using wordTrace_append hprefix tailTrace_2098162
  have hstable : (prefixWord ++ tailWord_2098162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098162).length < 2 ^ (prefixWord ++ tailWord_2098162).sum := by decide
  have hdescent : baseEnd_2098162 < baseStart_2098162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098212 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2098212 : Nat := 118140960795 + 2098212 * 2 ^ 59
def prefixEnd_2098212 : Nat := 4983230072969 + 3 ^ 40 * 2098212 * 2
def baseEnd_2098212 : Nat := 1077391271031649969600505

theorem tailTrace_2098212 : CollatzResearch.WordTrace tailWord_2098212 prefixEnd_2098212 1077391271031649969600505 := by
  unfold tailWord_2098212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38264039337271872462660445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51018719116362496616880593 38264039337271872462660445)
  ·
    refine ⟨14349014751476952173497667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38264039337271872462660445 14349014751476952173497667)
    ·
      refine ⟨21523522127215428260246501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14349014751476952173497667 21523522127215428260246501)
      ·
        refine ⟨4035660398852892798796219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21523522127215428260246501 4035660398852892798796219)
        ·
          refine ⟨6053490598279339198194329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035660398852892798796219 6053490598279339198194329)
          ·
            refine ⟨4540117948709504398645747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053490598279339198194329 4540117948709504398645747)
            ·
              refine ⟨6810176923064256597968621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540117948709504398645747 6810176923064256597968621)
              ·
                refine ⟨2553816346149096224238233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6810176923064256597968621 2553816346149096224238233)
                ·
                  refine ⟨1915362259611822168178675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553816346149096224238233 1915362259611822168178675)
                  ·
                    refine ⟨2873043389417733252268013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1915362259611822168178675 2873043389417733252268013)
                    ·
                      refine ⟨1077391271031649969600505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873043389417733252268013 1077391271031649969600505)
                      ·
                        rfl

theorem cell23_2098212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2098212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098212 prefixEnd_2098212 := by exact prefixLift 2098212
  have htrace : WordTrace (prefixWord ++ tailWord_2098212) baseStart_2098212 baseEnd_2098212 := by
    simpa [prefixWord, tailWord_2098212, baseEnd_2098212] using wordTrace_append hprefix tailTrace_2098212
  have hstable : (prefixWord ++ tailWord_2098212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098212).length < 2 ^ (prefixWord ++ tailWord_2098212).sum := by decide
  have hdescent : baseEnd_2098212 < baseStart_2098212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098231 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2098231 : Nat := 118140960795 + 2098231 * 2 ^ 59
def prefixEnd_2098231 : Nat := 4983230072969 + 3 ^ 40 * 2098231 * 2
def baseEnd_2098231 : Nat := 1077401027164085395262917

theorem tailTrace_2098231 : CollatzResearch.WordTrace tailWord_2098231 prefixEnd_2098231 1077401027164085395262917 := by
  unfold tailWord_2098231
  simp only [CollatzResearch.WordTrace]
  refine ⟨76528771661474911170262547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51019181107649940780175031 76528771661474911170262547)
  ·
    refine ⟨114793157492212366755393821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76528771661474911170262547 114793157492212366755393821)
    ·
      refine ⟨43047434059579637533272683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114793157492212366755393821 43047434059579637533272683)
      ·
        refine ⟨64571151089369456299909025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43047434059579637533272683 64571151089369456299909025)
        ·
          refine ⟨48428363317027092224931769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64571151089369456299909025 48428363317027092224931769)
          ·
            refine ⟨36321272487770319168698827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48428363317027092224931769 36321272487770319168698827)
            ·
              refine ⟨54481908731655478753048241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36321272487770319168698827 54481908731655478753048241)
              ·
                refine ⟨40861431548741609064786181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54481908731655478753048241 40861431548741609064786181)
                ·
                  refine ⟨7661518415389051699647409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40861431548741609064786181 7661518415389051699647409)
                  ·
                    refine ⟨5746138811541788774735557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7661518415389051699647409 5746138811541788774735557)
                    ·
                      refine ⟨1077401027164085395262917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5746138811541788774735557 1077401027164085395262917)
                      ·
                        rfl

theorem cell23_2098231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2098231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098231 prefixEnd_2098231 := by exact prefixLift 2098231
  have htrace : WordTrace (prefixWord ++ tailWord_2098231) baseStart_2098231 baseEnd_2098231 := by
    simpa [prefixWord, tailWord_2098231, baseEnd_2098231] using wordTrace_append hprefix tailTrace_2098231
  have hstable : (prefixWord ++ tailWord_2098231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098231).length < 2 ^ (prefixWord ++ tailWord_2098231).sum := by decide
  have hdescent : baseEnd_2098231 < baseStart_2098231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098262 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2098262 : Nat := 118140960795 + 2098262 * 2 ^ 59
def prefixEnd_2098262 : Nat := 4983230072969 + 3 ^ 40 * 2098262 * 2
def baseEnd_2098262 : Nat := 359138981688124924658425

theorem tailTrace_2098262 : CollatzResearch.WordTrace tailWord_2098262 prefixEnd_2098262 359138981688124924658425 := by
  unfold tailWord_2098262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783118895272662716540065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51019934882908402309760693 4783118895272662716540065)
  ·
    refine ⟨3587339171454497037405049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4783118895272662716540065 3587339171454497037405049)
    ·
      refine ⟨2690504378590872778053787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3587339171454497037405049 2690504378590872778053787)
      ·
        refine ⟨4035756567886309167080681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690504378590872778053787 4035756567886309167080681)
        ·
          refine ⟨3026817425914731875310511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4035756567886309167080681 3026817425914731875310511)
          ·
            refine ⟨4540226138872097812965767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026817425914731875310511 4540226138872097812965767)
            ·
              refine ⟨6810339208308146719448651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540226138872097812965767 6810339208308146719448651)
              ·
                refine ⟨10215508812462220079172977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6810339208308146719448651 10215508812462220079172977)
                ·
                  refine ⟨7661631609346665059379733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10215508812462220079172977 7661631609346665059379733)
                  ·
                    refine ⟨359138981688124924658425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7661631609346665059379733 359138981688124924658425)
                    ·
                      rfl

theorem cell23_2098262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2098262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098262 prefixEnd_2098262 := by exact prefixLift 2098262
  have htrace : WordTrace (prefixWord ++ tailWord_2098262) baseStart_2098262 baseEnd_2098262 := by
    simpa [prefixWord, tailWord_2098262, baseEnd_2098262] using wordTrace_append hprefix tailTrace_2098262
  have hstable : (prefixWord ++ tailWord_2098262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098262).length < 2 ^ (prefixWord ++ tailWord_2098262).sum := by decide
  have hdescent : baseEnd_2098262 < baseStart_2098262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098269 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2098269 : Nat := 118140960795 + 2098269 * 2 ^ 59
def prefixEnd_2098269 : Nat := 4983230072969 + 3 ^ 40 * 2098269 * 2
def baseEnd_2098269 : Nat := 1077420539428956246587743

theorem tailTrace_2098269 : CollatzResearch.WordTrace tailWord_2098269 prefixEnd_2098269 1077420539428956246587743 := by
  unfold tailWord_2098269
  simp only [CollatzResearch.WordTrace]
  refine ⟨76530157635337243660145861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51020105090224829106763907 76530157635337243660145861)
  ·
    refine ⟨14349404556625733186277349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76530157635337243660145861 14349404556625733186277349)
    ·
      refine ⟨2690513354367324972427003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14349404556625733186277349 2690513354367324972427003)
      ·
        refine ⟨4035770031550987458640505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690513354367324972427003 4035770031550987458640505)
        ·
          refine ⟨3026827523663240593980379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4035770031550987458640505 3026827523663240593980379)
          ·
            refine ⟨4540241285494860890970569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026827523663240593980379 4540241285494860890970569)
            ·
              refine ⟨3405180964121145668227927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540241285494860890970569 3405180964121145668227927)
              ·
                refine ⟨5107771446181718502341891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405180964121145668227927 5107771446181718502341891)
                ·
                  refine ⟨7661657169272577753512837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5107771446181718502341891 7661657169272577753512837)
                  ·
                    refine ⟨1436560719238608328783657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7661657169272577753512837 1436560719238608328783657)
                    ·
                      refine ⟨1077420539428956246587743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436560719238608328783657 1077420539428956246587743)
                      ·
                        rfl

theorem cell23_2098269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2098269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098269 prefixEnd_2098269 := by exact prefixLift 2098269
  have htrace : WordTrace (prefixWord ++ tailWord_2098269) baseStart_2098269 baseEnd_2098269 := by
    simpa [prefixWord, tailWord_2098269, baseEnd_2098269] using wordTrace_append hprefix tailTrace_2098269
  have hstable : (prefixWord ++ tailWord_2098269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098269).length < 2 ^ (prefixWord ++ tailWord_2098269).sum := by decide
  have hdescent : baseEnd_2098269 < baseStart_2098269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098271 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 7]
def baseStart_2098271 : Nat := 118140960795 + 2098271 * 2 ^ 59
def prefixEnd_2098271 : Nat := 4983230072969 + 3 ^ 40 * 2098271 * 2
def baseEnd_2098271 : Nat := 359140522130088412920911

theorem tailTrace_2098271 : CollatzResearch.WordTrace tailWord_2098271 prefixEnd_2098271 359140522130088412920911 := by
  unfold tailWord_2098271
  simp only [CollatzResearch.WordTrace]
  refine ⟨76530230581329998001718667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51020153720886665334479111 76530230581329998001718667)
  ·
    refine ⟨114795345871994997002578001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76530230581329998001718667 114795345871994997002578001)
    ·
      refine ⟨86096509403996247751933501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114795345871994997002578001 86096509403996247751933501)
      ·
        refine ⟨32286191026498592906975063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86096509403996247751933501 32286191026498592906975063)
        ·
          refine ⟨48429286539747889360462595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32286191026498592906975063 48429286539747889360462595)
          ·
            refine ⟨72643929809621834040693893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48429286539747889360462595 72643929809621834040693893)
            ·
              refine ⟨13620736839304093882630105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72643929809621834040693893 13620736839304093882630105)
              ·
                refine ⟨10215552629478070411972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13620736839304093882630105 10215552629478070411972579)
                ·
                  refine ⟨15323328944217105617958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10215552629478070411972579 15323328944217105617958869)
                  ·
                    refine ⟨359140522130088412920911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15323328944217105617958869 359140522130088412920911)
                    ·
                      rfl

theorem cell23_2098271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_2098271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098271 prefixEnd_2098271 := by exact prefixLift 2098271
  have htrace : WordTrace (prefixWord ++ tailWord_2098271) baseStart_2098271 baseEnd_2098271 := by
    simpa [prefixWord, tailWord_2098271, baseEnd_2098271] using wordTrace_append hprefix tailTrace_2098271
  have hstable : (prefixWord ++ tailWord_2098271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098271).length < 2 ^ (prefixWord ++ tailWord_2098271).sum := by decide
  have hdescent : baseEnd_2098271 < baseStart_2098271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098369 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2098369 : Nat := 118140960795 + 2098369 * 2 ^ 59
def prefixEnd_2098369 : Nat := 4983230072969 + 3 ^ 40 * 2098369 * 2
def baseEnd_2098369 : Nat := 359157295831468618445761

theorem tailTrace_2098369 : CollatzResearch.WordTrace tailWord_2098369 prefixEnd_2098369 359157295831468618445761 := by
  unfold tailWord_2098369
  simp only [CollatzResearch.WordTrace]
  refine ⟨76533804934974960738786161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51022536623316640492524107 76533804934974960738786161)
  ·
    refine ⟨57400353701231220554089621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76533804934974960738786161 57400353701231220554089621)
    ·
      refine ⟨2690641579745213463472951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57400353701231220554089621 2690641579745213463472951)
      ·
        refine ⟨4035962369617820195209427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690641579745213463472951 4035962369617820195209427)
        ·
          refine ⟨6053943554426730292814141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035962369617820195209427 6053943554426730292814141)
          ·
            refine ⟨2270228832910023859805303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6053943554426730292814141 2270228832910023859805303)
            ·
              refine ⟨3405343249365035789707955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270228832910023859805303 3405343249365035789707955)
              ·
                refine ⟨5108014874047553684561933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405343249365035789707955 5108014874047553684561933)
                ·
                  refine ⟨1915505577767832631710725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5108014874047553684561933 1915505577767832631710725)
                  ·
                    refine ⟨359157295831468618445761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915505577767832631710725 359157295831468618445761)
                    ·
                      rfl

theorem cell23_2098369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2098369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098369 prefixEnd_2098369 := by exact prefixLift 2098369
  have htrace : WordTrace (prefixWord ++ tailWord_2098369) baseStart_2098369 baseEnd_2098369 := by
    simpa [prefixWord, tailWord_2098369, baseEnd_2098369] using wordTrace_append hprefix tailTrace_2098369
  have hstable : (prefixWord ++ tailWord_2098369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098369).length < 2 ^ (prefixWord ++ tailWord_2098369).sum := by decide
  have hdescent : baseEnd_2098369 < baseStart_2098369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098385 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_2098385 : Nat := 118140960795 + 2098385 * 2 ^ 59
def prefixEnd_2098385 : Nat := 4983230072969 + 3 ^ 40 * 2098385 * 2
def baseEnd_2098385 : Nat := 1077480103184877792737209

theorem tailTrace_2098385 : CollatzResearch.WordTrace tailWord_2098385 prefixEnd_2098385 1077480103184877792737209 := by
  unfold tailWord_2098385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76534388502916995471368609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51022925668611330314245739 76534388502916995471368609)
  ·
    refine ⟨57400791377187746603526457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76534388502916995471368609 57400791377187746603526457)
    ·
      refine ⟨43050593532890809952644843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57400791377187746603526457 43050593532890809952644843)
      ·
        refine ⟨64575890299336214928967265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43050593532890809952644843 64575890299336214928967265)
        ·
          refine ⟨48431917724502161196725449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64575890299336214928967265 48431917724502161196725449)
          ·
            refine ⟨36323938293376620897544087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48431917724502161196725449 36323938293376620897544087)
            ·
              refine ⟨54485907440064931346316131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36323938293376620897544087 54485907440064931346316131)
              ·
                refine ⟨81728861160097397019474197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54485907440064931346316131 81728861160097397019474197)
                ·
                  refine ⟨3831040366879565485287853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81728861160097397019474197 3831040366879565485287853)
                  ·
                    refine ⟨1436640137579837056982945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3831040366879565485287853 1436640137579837056982945)
                    ·
                      refine ⟨1077480103184877792737209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436640137579837056982945 1077480103184877792737209)
                      ·
                        rfl

theorem cell23_2098385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_2098385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098385 prefixEnd_2098385 := by exact prefixLift 2098385
  have htrace : WordTrace (prefixWord ++ tailWord_2098385) baseStart_2098385 baseEnd_2098385 := by
    simpa [prefixWord, tailWord_2098385, baseEnd_2098385] using wordTrace_append hprefix tailTrace_2098385
  have hstable : (prefixWord ++ tailWord_2098385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098385).length < 2 ^ (prefixWord ++ tailWord_2098385).sum := by decide
  have hdescent : baseEnd_2098385 < baseStart_2098385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098412 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_2098412 : Nat := 118140960795 + 2098412 * 2 ^ 59
def prefixEnd_2098412 : Nat := 4983230072969 + 3 ^ 40 * 2098412 * 2
def baseEnd_2098412 : Nat := 359164655720849729033195

theorem tailTrace_2098412 : CollatzResearch.WordTrace tailWord_2098412 prefixEnd_2098412 359164655720849729033195 := by
  unfold tailWord_2098412
  simp only [CollatzResearch.WordTrace]
  refine ⟨38267686636909589541300745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51023582182546119388400993 38267686636909589541300745)
  ·
    refine ⟨28700764977682192155975559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38267686636909589541300745 28700764977682192155975559)
    ·
      refine ⟨43051147466523288233963339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28700764977682192155975559 43051147466523288233963339)
      ·
        refine ⟨64576721199784932350945009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43051147466523288233963339 64576721199784932350945009)
        ·
          refine ⟨48432540899838699263208757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64576721199784932350945009 48432540899838699263208757)
          ·
            refine ⟨4540550709359878055925821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48432540899838699263208757 4540550709359878055925821)
            ·
              refine ⟨1702706516009954270972183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540550709359878055925821 1702706516009954270972183)
              ·
                refine ⟨2554059774014931406458275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702706516009954270972183 2554059774014931406458275)
                ·
                  refine ⟨3831089661022397109687413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554059774014931406458275 3831089661022397109687413)
                  ·
                    refine ⟨359164655720849729033195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3831089661022397109687413 359164655720849729033195)
                    ·
                      rfl

theorem cell23_2098412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_2098412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098412 prefixEnd_2098412 := by exact prefixLift 2098412
  have htrace : WordTrace (prefixWord ++ tailWord_2098412) baseStart_2098412 baseEnd_2098412 := by
    simpa [prefixWord, tailWord_2098412, baseEnd_2098412] using wordTrace_append hprefix tailTrace_2098412
  have hstable : (prefixWord ++ tailWord_2098412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098412).length < 2 ^ (prefixWord ++ tailWord_2098412).sum := by decide
  have hdescent : baseEnd_2098412 < baseStart_2098412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098432 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2]
def baseStart_2098432 : Nat := 118140960795 + 2098432 * 2 ^ 59
def prefixEnd_2098432 : Nat := 4983230072969 + 3 ^ 40 * 2098432 * 2
def baseEnd_2098432 : Nat := 1077504236775639108849493

theorem tailTrace_2098432 : CollatzResearch.WordTrace tailWord_2098432 prefixEnd_2098432 1077504236775639108849493 := by
  unfold tailWord_2098432
  simp only [CollatzResearch.WordTrace]
  refine ⟨38268051366873361249164775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51024068489164481665553033 38268051366873361249164775)
  ·
    refine ⟨57402077050310041873747163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38268051366873361249164775 57402077050310041873747163)
    ·
      refine ⟨86103115575465062810620745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57402077050310041873747163 86103115575465062810620745)
      ·
        refine ⟨64577336681598797107965559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86103115575465062810620745 64577336681598797107965559)
        ·
          refine ⟨96866005022398195661948339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64577336681598797107965559 96866005022398195661948339)
          ·
            refine ⟨145299007533597293492922509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96866005022398195661948339 145299007533597293492922509)
            ·
              refine ⟨54487127825098985059845941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145299007533597293492922509 54487127825098985059845941)
              ·
                refine ⟨5108168233603029849360557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54487127825098985059845941 5108168233603029849360557)
                ·
                  refine ⟨1915563087601136193510209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5108168233603029849360557 1915563087601136193510209)
                  ·
                    refine ⟨1436672315700852145132657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915563087601136193510209 1436672315700852145132657)
                    ·
                      refine ⟨1077504236775639108849493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436672315700852145132657 1077504236775639108849493)
                      ·
                        rfl

theorem cell23_2098432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_2098432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098432 prefixEnd_2098432 := by exact prefixLift 2098432
  have htrace : WordTrace (prefixWord ++ tailWord_2098432) baseStart_2098432 baseEnd_2098432 := by
    simpa [prefixWord, tailWord_2098432, baseEnd_2098432] using wordTrace_append hprefix tailTrace_2098432
  have hstable : (prefixWord ++ tailWord_2098432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098432).length < 2 ^ (prefixWord ++ tailWord_2098432).sum := by decide
  have hdescent : baseEnd_2098432 < baseStart_2098432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098435 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3]
def baseStart_2098435 : Nat := 118140960795 + 2098435 * 2 ^ 59
def prefixEnd_2098435 : Nat := 4983230072969 + 3 ^ 40 * 2098435 * 2
def baseEnd_2098435 : Nat := 1077505777217602597111979

theorem tailTrace_2098435 : CollatzResearch.WordTrace tailWord_2098435 prefixEnd_2098435 1077505777217602597111979 := by
  unfold tailWord_2098435
  simp only [CollatzResearch.WordTrace]
  refine ⟨76536212152735854010688759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51024141435157236007125839 76536212152735854010688759)
  ·
    refine ⟨114804318229103781016033139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76536212152735854010688759 114804318229103781016033139)
    ·
      refine ⟨172206477343655671524049709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114804318229103781016033139 172206477343655671524049709)
      ·
        refine ⟨64577429003870876821518641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172206477343655671524049709 64577429003870876821518641)
        ·
          refine ⟨48433071752903157616138981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64577429003870876821518641 48433071752903157616138981)
          ·
            refine ⟨9081200953669342053026059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48433071752903157616138981 9081200953669342053026059)
            ·
              refine ⟨13621801430504013079539089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9081200953669342053026059 13621801430504013079539089)
              ·
                refine ⟨10216351072878009809654317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13621801430504013079539089 10216351072878009809654317)
                ·
                  refine ⟨3831131652329253678620369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10216351072878009809654317 3831131652329253678620369)
                  ·
                    refine ⟨2873348739246940258965277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831131652329253678620369 2873348739246940258965277)
                    ·
                      refine ⟨1077505777217602597111979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873348739246940258965277 1077505777217602597111979)
                      ·
                        rfl

theorem cell23_2098435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_2098435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098435 prefixEnd_2098435 := by exact prefixLift 2098435
  have htrace : WordTrace (prefixWord ++ tailWord_2098435) baseStart_2098435 baseEnd_2098435 := by
    simpa [prefixWord, tailWord_2098435, baseEnd_2098435] using wordTrace_append hprefix tailTrace_2098435
  have hstable : (prefixWord ++ tailWord_2098435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098435).length < 2 ^ (prefixWord ++ tailWord_2098435).sum := by decide
  have hdescent : baseEnd_2098435 < baseStart_2098435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098455 : List Nat := [1, 1, 3, 4, 1, 1, 5, 7]
def baseStart_2098455 : Nat := 118140960795 + 2098455 * 2 ^ 59
def prefixEnd_2098455 : Nat := 4983230072969 + 3 ^ 40 * 2098455 * 2
def baseEnd_2098455 : Nat := 39908001734470093291181

theorem tailTrace_2098455 : CollatzResearch.WordTrace tailWord_2098455 prefixEnd_2098455 39908001734470093291181 := by
  unfold tailWord_2098455
  simp only [CollatzResearch.WordTrace]
  refine ⟨76536941612663397426416819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51024627741775598284277879 76536941612663397426416819)
  ·
    refine ⟨114805412418995096139625229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76536941612663397426416819 114805412418995096139625229)
    ·
      refine ⟨43052029657123161052359461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114805412418995096139625229 43052029657123161052359461)
      ·
        refine ⟨8072255560710592697317399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43052029657123161052359461 8072255560710592697317399)
        ·
          refine ⟨12108383341065889045976099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072255560710592697317399 12108383341065889045976099)
          ·
            refine ⟨18162575011598833568964149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12108383341065889045976099 18162575011598833568964149)
            ·
              refine ⟨1702741407337390647090389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18162575011598833568964149 1702741407337390647090389)
              ·
                refine ⟨39908001734470093291181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1702741407337390647090389 39908001734470093291181)
                ·
                  rfl

theorem cell23_2098455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 7].length) (baseStart_2098455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098455 prefixEnd_2098455 := by exact prefixLift 2098455
  have htrace : WordTrace (prefixWord ++ tailWord_2098455) baseStart_2098455 baseEnd_2098455 := by
    simpa [prefixWord, tailWord_2098455, baseEnd_2098455] using wordTrace_append hprefix tailTrace_2098455
  have hstable : (prefixWord ++ tailWord_2098455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098455).length < 2 ^ (prefixWord ++ tailWord_2098455).sum := by decide
  have hdescent : baseEnd_2098455 < baseStart_2098455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098466 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_2098466 : Nat := 118140960795 + 2098466 * 2 ^ 59
def prefixEnd_2098466 : Nat := 4983230072969 + 3 ^ 40 * 2098466 * 2
def baseEnd_2098466 : Nat := 1077521695117891975824337

theorem tailTrace_2098466 : CollatzResearch.WordTrace tailWord_2098466 prefixEnd_2098466 1077521695117891975824337 := by
  unfold tailWord_2098466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19134335703905886576266813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51024895210415697536711501 19134335703905886576266813)
  ·
    refine ⟨7175375888964707466100055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19134335703905886576266813 7175375888964707466100055)
    ·
      refine ⟨10763063833447061199150083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175375888964707466100055 10763063833447061199150083)
      ·
        refine ⟨16144595750170591798725125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10763063833447061199150083 16144595750170591798725125)
        ·
          refine ⟨3027111703156985962260961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16144595750170591798725125 3027111703156985962260961)
          ·
            refine ⟨2270333777367739471695721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027111703156985962260961 2270333777367739471695721)
            ·
              refine ⟨1702750333025804603771791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270333777367739471695721 1702750333025804603771791)
              ·
                refine ⟨2554125499538706905657687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702750333025804603771791 2554125499538706905657687)
                ·
                  refine ⟨3831188249308060358486531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554125499538706905657687 3831188249308060358486531)
                  ·
                    refine ⟨5746782373962090537729797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831188249308060358486531 5746782373962090537729797)
                    ·
                      refine ⟨1077521695117891975824337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5746782373962090537729797 1077521695117891975824337)
                      ·
                        rfl

theorem cell23_2098466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_2098466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098466 prefixEnd_2098466 := by exact prefixLift 2098466
  have htrace : WordTrace (prefixWord ++ tailWord_2098466) baseStart_2098466 baseEnd_2098466 := by
    simpa [prefixWord, tailWord_2098466, baseEnd_2098466] using wordTrace_append hprefix tailTrace_2098466
  have hstable : (prefixWord ++ tailWord_2098466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098466).length < 2 ^ (prefixWord ++ tailWord_2098466).sum := by decide
  have hdescent : baseEnd_2098466 < baseStart_2098466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098469 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_2098469 : Nat := 118140960795 + 2098469 * 2 ^ 59
def prefixEnd_2098469 : Nat := 4983230072969 + 3 ^ 40 * 2098469 * 2
def baseEnd_2098469 : Nat := 1077523235559855464086823

theorem tailTrace_2098469 : CollatzResearch.WordTrace tailWord_2098469 prefixEnd_2098469 1077523235559855464086823 := by
  unfold tailWord_2098469
  simp only [CollatzResearch.WordTrace]
  refine ⟨76537452234612677817426461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51024968156408451878284307 76537452234612677817426461)
  ·
    refine ⟨28701544587979754181534923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76537452234612677817426461 28701544587979754181534923)
    ·
      refine ⟨43052316881969631272302385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28701544587979754181534923 43052316881969631272302385)
      ·
        refine ⟨32289237661477223454226789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43052316881969631272302385 32289237661477223454226789)
        ·
          refine ⟨6054232061526979397667523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32289237661477223454226789 6054232061526979397667523)
          ·
            refine ⟨9081348092290469096501285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6054232061526979397667523 9081348092290469096501285)
            ·
              refine ⟨1702752767304462955593991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9081348092290469096501285 1702752767304462955593991)
              ·
                refine ⟨2554129150956694433390987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702752767304462955593991 2554129150956694433390987)
                ·
                  refine ⟨3831193726435041650086481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554129150956694433390987 3831193726435041650086481)
                  ·
                    refine ⟨2873395294826281237564861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831193726435041650086481 2873395294826281237564861)
                    ·
                      refine ⟨1077523235559855464086823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873395294826281237564861 1077523235559855464086823)
                      ·
                        rfl

theorem cell23_2098469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_2098469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098469 prefixEnd_2098469 := by exact prefixLift 2098469
  have htrace : WordTrace (prefixWord ++ tailWord_2098469) baseStart_2098469 baseEnd_2098469 := by
    simpa [prefixWord, tailWord_2098469, baseEnd_2098469] using wordTrace_append hprefix tailTrace_2098469
  have hstable : (prefixWord ++ tailWord_2098469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098469).length < 2 ^ (prefixWord ++ tailWord_2098469).sum := by decide
  have hdescent : baseEnd_2098469 < baseStart_2098469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098522 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_2098522 : Nat := 118140960795 + 2098522 * 2 ^ 59
def prefixEnd_2098522 : Nat := 4983230072969 + 3 ^ 40 * 2098522 * 2
def baseEnd_2098522 : Nat := 1077550450034543756724079

theorem tailTrace_2098522 : CollatzResearch.WordTrace tailWord_2098522 prefixEnd_2098522 1077550450034543756724079 := by
  unfold tailWord_2098522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19134846325855166967276455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51026256868947111912737213 19134846325855166967276455)
  ·
    refine ⟨28702269488782750450914683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19134846325855166967276455 28702269488782750450914683)
    ·
      refine ⟨43053404233174125676372025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28702269488782750450914683 43053404233174125676372025)
      ·
        refine ⟨32290053174880594257279019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43053404233174125676372025 32290053174880594257279019)
        ·
          refine ⟨48435079762320891385918529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32290053174880594257279019 48435079762320891385918529)
          ·
            refine ⟨36326309821740668539438897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48435079762320891385918529 36326309821740668539438897)
            ·
              refine ⟨27244732366305501404579173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36326309821740668539438897 27244732366305501404579173)
              ·
                refine ⟨5108387318682281513358595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27244732366305501404579173 5108387318682281513358595)
                ·
                  refine ⟨7662580978023422270037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108387318682281513358595 7662580978023422270037893)
                  ·
                    refine ⟨1436733933379391675632105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7662580978023422270037893 1436733933379391675632105)
                    ·
                      refine ⟨1077550450034543756724079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436733933379391675632105 1077550450034543756724079)
                      ·
                        rfl

theorem cell23_2098522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_2098522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098522 prefixEnd_2098522 := by exact prefixLift 2098522
  have htrace : WordTrace (prefixWord ++ tailWord_2098522) baseStart_2098522 baseEnd_2098522 := by
    simpa [prefixWord, tailWord_2098522, baseEnd_2098522] using wordTrace_append hprefix tailTrace_2098522
  have hstable : (prefixWord ++ tailWord_2098522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098522).length < 2 ^ (prefixWord ++ tailWord_2098522).sum := by decide
  have hdescent : baseEnd_2098522 < baseStart_2098522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098545 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 7]
def baseStart_2098545 : Nat := 118140960795 + 2098545 * 2 ^ 59
def prefixEnd_2098545 : Nat := 4983230072969 + 3 ^ 40 * 2098545 * 2
def baseEnd_2098545 : Nat := 119729140009955240748497

theorem tailTrace_2098545 : CollatzResearch.WordTrace tailWord_2098545 prefixEnd_2098545 119729140009955240748497 := by
  unfold tailWord_2098545
  simp only [CollatzResearch.WordTrace]
  refine ⟨76540224182337342797193089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51026816121558228531462059 76540224182337342797193089)
  ·
    refine ⟨57405168136753007097894817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76540224182337342797193089 57405168136753007097894817)
    ·
      refine ⟨43053876102564755323421113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57405168136753007097894817 43053876102564755323421113)
      ·
        refine ⟨32290407076923566492565835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43053876102564755323421113 32290407076923566492565835)
        ·
          refine ⟨48435610615385349738848753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32290407076923566492565835 48435610615385349738848753)
          ·
            refine ⟨36326707961539012304136565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48435610615385349738848753 36326707961539012304136565)
            ·
              refine ⟨3405628871394282403512803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36326707961539012304136565 3405628871394282403512803)
              ·
                refine ⟨5108443307091423605269205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405628871394282403512803 5108443307091423605269205)
                ·
                  refine ⟨119729140009955240748497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5108443307091423605269205 119729140009955240748497)
                  ·
                    rfl

theorem cell23_2098545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_2098545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098545 prefixEnd_2098545 := by exact prefixLift 2098545
  have htrace : WordTrace (prefixWord ++ tailWord_2098545) baseStart_2098545 baseEnd_2098545 := by
    simpa [prefixWord, tailWord_2098545, baseEnd_2098545] using wordTrace_append hprefix tailTrace_2098545
  have hstable : (prefixWord ++ tailWord_2098545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098545).length < 2 ^ (prefixWord ++ tailWord_2098545).sum := by decide
  have hdescent : baseEnd_2098545 < baseStart_2098545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098555 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3]
def baseStart_2098555 : Nat := 118140960795 + 2098555 * 2 ^ 59
def prefixEnd_2098555 : Nat := 4983230072969 + 3 ^ 40 * 2098555 * 2
def baseEnd_2098555 : Nat := 1077567394896142127611427

theorem tailTrace_2098555 : CollatzResearch.WordTrace tailWord_2098555 prefixEnd_2098555 1077567394896142127611427 := by
  unfold tailWord_2098555
  simp only [CollatzResearch.WordTrace]
  refine ⟨76540588912301114505057119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51027059274867409670038079 76540588912301114505057119)
  ·
    refine ⟨114810883368451671757585679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76540588912301114505057119 114810883368451671757585679)
    ·
      refine ⟨172216325052677507636378519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114810883368451671757585679 172216325052677507636378519)
      ·
        refine ⟨258324487579016261454567779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172216325052677507636378519 258324487579016261454567779)
        ·
          refine ⟨387486731368524392181851669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258324487579016261454567779 387486731368524392181851669)
          ·
            refine ⟨18163440532899580883524297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 387486731368524392181851669 18163440532899580883524297)
            ·
              refine ⟨13622580399674685662643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163440532899580883524297 13622580399674685662643223)
              ·
                refine ⟨20433870599512028493964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13622580399674685662643223 20433870599512028493964835)
                ·
                  refine ⟨30650805899268042740947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20433870599512028493964835 30650805899268042740947253)
                  ·
                    refine ⟨2873513053056379006963805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30650805899268042740947253 2873513053056379006963805)
                    ·
                      refine ⟨1077567394896142127611427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873513053056379006963805 1077567394896142127611427)
                      ·
                        rfl

theorem cell23_2098555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].length) (baseStart_2098555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098555 prefixEnd_2098555 := by exact prefixLift 2098555
  have htrace : WordTrace (prefixWord ++ tailWord_2098555) baseStart_2098555 baseEnd_2098555 := by
    simpa [prefixWord, tailWord_2098555, baseEnd_2098555] using wordTrace_append hprefix tailTrace_2098555
  have hstable : (prefixWord ++ tailWord_2098555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098555).length < 2 ^ (prefixWord ++ tailWord_2098555).sum := by decide
  have hdescent : baseEnd_2098555 < baseStart_2098555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098585 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_2098585 : Nat := 118140960795 + 2098585 * 2 ^ 59
def prefixEnd_2098585 : Nat := 4983230072969 + 3 ^ 40 * 2098585 * 2
def baseEnd_2098585 : Nat := 1077582799315777010236289

theorem tailTrace_2098585 : CollatzResearch.WordTrace tailWord_2098585 prefixEnd_2098585 1077582799315777010236289 := by
  unfold tailWord_2098585
  simp only [CollatzResearch.WordTrace]
  refine ⟨76541683102192429628649209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51027788734794953085766139 76541683102192429628649209)
  ·
    refine ⟨57406262326644322221486907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76541683102192429628649209 57406262326644322221486907)
    ·
      refine ⟨86109393489966483332230361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57406262326644322221486907 86109393489966483332230361)
      ·
        refine ⟨64582045117474862499172771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86109393489966483332230361 64582045117474862499172771)
        ·
          refine ⟨96873067676212293748759157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64582045117474862499172771 96873067676212293748759157)
          ·
            refine ⟨9081850094644902538946171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96873067676212293748759157 9081850094644902538946171)
            ·
              refine ⟨13622775141967353808419257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9081850094644902538946171 13622775141967353808419257)
              ·
                refine ⟨10217081356475515356314443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13622775141967353808419257 10217081356475515356314443)
                ·
                  refine ⟨15325622034713273034471665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10217081356475515356314443 15325622034713273034471665)
                  ·
                    refine ⟨11494216526034954775853749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15325622034713273034471665 11494216526034954775853749)
                    ·
                      refine ⟨1077582799315777010236289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11494216526034954775853749 1077582799315777010236289)
                      ·
                        rfl

theorem cell23_2098585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_2098585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098585 prefixEnd_2098585 := by exact prefixLift 2098585
  have htrace : WordTrace (prefixWord ++ tailWord_2098585) baseStart_2098585 baseEnd_2098585 := by
    simpa [prefixWord, tailWord_2098585, baseEnd_2098585] using wordTrace_append hprefix tailTrace_2098585
  have hstable : (prefixWord ++ tailWord_2098585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098585).length < 2 ^ (prefixWord ++ tailWord_2098585).sum := by decide
  have hdescent : baseEnd_2098585 < baseStart_2098585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098590 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2098590 : Nat := 118140960795 + 2098590 * 2 ^ 59
def prefixEnd_2098590 : Nat := 4983230072969 + 3 ^ 40 * 2098590 * 2
def baseEnd_2098590 : Nat := 1077585366719049490673767

theorem tailTrace_2098590 : CollatzResearch.WordTrace tailWord_2098590 prefixEnd_2098590 1077585366719049490673767 := by
  unfold tailWord_2098590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567733183396789435322653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51027910311449543655054149 9567733183396789435322653)
  ·
    refine ⟨3587899943773796038245995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9567733183396789435322653 3587899943773796038245995)
    ·
      refine ⟨5381849915660694057368993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587899943773796038245995 5381849915660694057368993)
      ·
        refine ⟨4036387436745520543026745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5381849915660694057368993 4036387436745520543026745)
        ·
          refine ⟨3027290577559140407270059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4036387436745520543026745 3027290577559140407270059)
          ·
            refine ⟨4540935866338710610905089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027290577559140407270059 4540935866338710610905089)
            ·
              refine ⟨3405701899754032958178817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540935866338710610905089 3405701899754032958178817)
              ·
                refine ⟨2554276424815524718634113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405701899754032958178817 2554276424815524718634113)
                ·
                  refine ⟨1915707318611643538975585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554276424815524718634113 1915707318611643538975585)
                  ·
                    refine ⟨1436780488958732654231689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915707318611643538975585 1436780488958732654231689)
                    ·
                      refine ⟨1077585366719049490673767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436780488958732654231689 1077585366719049490673767)
                      ·
                        rfl

theorem cell23_2098590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2098590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098590 prefixEnd_2098590 := by exact prefixLift 2098590
  have htrace : WordTrace (prefixWord ++ tailWord_2098590) baseStart_2098590 baseEnd_2098590 := by
    simpa [prefixWord, tailWord_2098590, baseEnd_2098590] using wordTrace_append hprefix tailTrace_2098590
  have hstable : (prefixWord ++ tailWord_2098590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098590).length < 2 ^ (prefixWord ++ tailWord_2098590).sum := by decide
  have hdescent : baseEnd_2098590 < baseStart_2098590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098632 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_2098632 : Nat := 118140960795 + 2098632 * 2 ^ 59
def prefixEnd_2098632 : Nat := 4983230072969 + 3 ^ 40 * 2098632 * 2
def baseEnd_2098632 : Nat := 1077606932906538326348573

theorem tailTrace_2098632 : CollatzResearch.WordTrace tailWord_2098632 prefixEnd_2098632 1077606932906538326348573 := by
  unfold tailWord_2098632
  simp only [CollatzResearch.WordTrace]
  refine ⟨38271698666511078327805075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51028931555348104437073433 38271698666511078327805075)
  ·
    refine ⟨57407547999766617491707613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38271698666511078327805075 57407547999766617491707613)
    ·
      refine ⟨21527830499912481559390355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57407547999766617491707613 21527830499912481559390355)
      ·
        refine ⟨32291745749868722339085533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21527830499912481559390355 32291745749868722339085533)
        ·
          refine ⟨12109404656200770877157075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32291745749868722339085533 12109404656200770877157075)
          ·
            refine ⟨18164106984301156315735613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12109404656200770877157075 18164106984301156315735613)
            ·
              refine ⟨6811540119112933618400855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18164106984301156315735613 6811540119112933618400855)
              ·
                refine ⟨10217310178669400427601283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811540119112933618400855 10217310178669400427601283)
                ·
                  refine ⟨15325965268004100641401925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10217310178669400427601283 15325965268004100641401925)
                  ·
                    refine ⟨2873618487750768870262861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15325965268004100641401925 2873618487750768870262861)
                    ·
                      refine ⟨1077606932906538326348573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873618487750768870262861 1077606932906538326348573)
                      ·
                        rfl

theorem cell23_2098632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_2098632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098632 prefixEnd_2098632 := by exact prefixLift 2098632
  have htrace : WordTrace (prefixWord ++ tailWord_2098632) baseStart_2098632 baseEnd_2098632 := by
    simpa [prefixWord, tailWord_2098632, baseEnd_2098632] using wordTrace_append hprefix tailTrace_2098632
  have hstable : (prefixWord ++ tailWord_2098632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098632).length < 2 ^ (prefixWord ++ tailWord_2098632).sum := by decide
  have hdescent : baseEnd_2098632 < baseStart_2098632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098639 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 1, 4]
def baseStart_2098639 : Nat := 118140960795 + 2098639 * 2 ^ 59
def prefixEnd_2098639 : Nat := 4983230072969 + 3 ^ 40 * 2098639 * 2
def baseEnd_2098639 : Nat := 359203509090373266320347

theorem tailTrace_2098639 : CollatzResearch.WordTrace tailWord_2098639 prefixEnd_2098639 359203509090373266320347 := by
  unfold tailWord_2098639
  simp only [CollatzResearch.WordTrace]
  refine ⟨76543652643996796851114971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51029101762664531234076647 76543652643996796851114971)
  ·
    refine ⟨114815478965995195276672457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76543652643996796851114971 114815478965995195276672457)
    ·
      refine ⟨86111609224496396457504343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114815478965995195276672457 86111609224496396457504343)
      ·
        refine ⟨129167413836744594686256515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86111609224496396457504343 129167413836744594686256515)
        ·
          refine ⟨193751120755116892029384773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129167413836744594686256515 193751120755116892029384773)
          ·
            refine ⟨36328335141584417255509645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193751120755116892029384773 36328335141584417255509645)
            ·
              refine ⟨13623125678094156470816117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36328335141584417255509645 13623125678094156470816117)
              ·
                refine ⟨1277168032321327169139011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13623125678094156470816117 1277168032321327169139011)
                ·
                  refine ⟨1915752048481990753708517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277168032321327169139011 1915752048481990753708517)
                  ·
                    refine ⟨359203509090373266320347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915752048481990753708517 359203509090373266320347)
                    ·
                      rfl

theorem cell23_2098639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_2098639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098639 prefixEnd_2098639 := by exact prefixLift 2098639
  have htrace : WordTrace (prefixWord ++ tailWord_2098639) baseStart_2098639 baseEnd_2098639 := by
    simpa [prefixWord, tailWord_2098639, baseEnd_2098639] using wordTrace_append hprefix tailTrace_2098639
  have hstable : (prefixWord ++ tailWord_2098639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098639).length < 2 ^ (prefixWord ++ tailWord_2098639).sum := by decide
  have hdescent : baseEnd_2098639 < baseStart_2098639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098646 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2098646 : Nat := 118140960795 + 2098646 * 2 ^ 59
def prefixEnd_2098646 : Nat := 4983230072969 + 3 ^ 40 * 2098646 * 2
def baseEnd_2098646 : Nat := 1077614121635701271573509

theorem tailTrace_2098646 : CollatzResearch.WordTrace tailWord_2098646 prefixEnd_2098646 1077614121635701271573509 := by
  unfold tailWord_2098646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783994247185714815413737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51029271969980958031079861 4783994247185714815413737)
  ·
    refine ⟨3587995685389286111560303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4783994247185714815413737 3587995685389286111560303)
    ·
      refine ⟨5381993528083929167340455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587995685389286111560303 5381993528083929167340455)
      ·
        refine ⟨8072990292125893751010683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381993528083929167340455 8072990292125893751010683)
        ·
          refine ⟨12109485438188840626516025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072990292125893751010683 12109485438188840626516025)
          ·
            refine ⟨9082114078641630469887019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12109485438188840626516025 9082114078641630469887019)
            ·
              refine ⟨13623171117962445704830529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9082114078641630469887019 13623171117962445704830529)
              ·
                refine ⟨10217378338471834278622897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13623171117962445704830529 10217378338471834278622897)
                ·
                  refine ⟨7663033753853875708967173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10217378338471834278622897 7663033753853875708967173)
                  ·
                    refine ⟨1436818828847601695431345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7663033753853875708967173 1436818828847601695431345)
                    ·
                      refine ⟨1077614121635701271573509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436818828847601695431345 1077614121635701271573509)
                      ·
                        rfl

theorem cell23_2098646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2098646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098646 prefixEnd_2098646 := by exact prefixLift 2098646
  have htrace : WordTrace (prefixWord ++ tailWord_2098646) baseStart_2098646 baseEnd_2098646 := by
    simpa [prefixWord, tailWord_2098646, baseEnd_2098646] using wordTrace_append hprefix tailTrace_2098646
  have hstable : (prefixWord ++ tailWord_2098646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098646).length < 2 ^ (prefixWord ++ tailWord_2098646).sum := by decide
  have hdescent : baseEnd_2098646 < baseStart_2098646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098655 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2098655 : Nat := 118140960795 + 2098655 * 2 ^ 59
def prefixEnd_2098655 : Nat := 4983230072969 + 3 ^ 40 * 2098655 * 2
def baseEnd_2098655 : Nat := 1077618742961591736360967

theorem tailTrace_2098655 : CollatzResearch.WordTrace tailWord_2098655 prefixEnd_2098655 1077618742961591736360967 := by
  unfold tailWord_2098655
  simp only [CollatzResearch.WordTrace]
  refine ⟨76544236211938831583697419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51029490807959221055798279 76544236211938831583697419)
  ·
    refine ⟨114816354317908247375546129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76544236211938831583697419 114816354317908247375546129)
    ·
      refine ⟨86112265738431185531659597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114816354317908247375546129 86112265738431185531659597)
      ·
        refine ⟨32292099651911694574372349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86112265738431185531659597 32292099651911694574372349)
        ·
          refine ⟨12109537369466885465389631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32292099651911694574372349 12109537369466885465389631)
          ·
            refine ⟨18164306054200328198084447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12109537369466885465389631 18164306054200328198084447)
            ·
              refine ⟨27246459081300492297126671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18164306054200328198084447 27246459081300492297126671)
              ·
                refine ⟨40869688621950738445690007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27246459081300492297126671 40869688621950738445690007)
                ·
                  refine ⟨61304532932926107668535011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40869688621950738445690007 61304532932926107668535011)
                  ·
                    refine ⟨91956799399389161502802517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61304532932926107668535011 91956799399389161502802517)
                    ·
                      refine ⟨1077618742961591736360967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 91956799399389161502802517 1077618742961591736360967)
                      ·
                        rfl

theorem cell23_2098655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2098655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098655 prefixEnd_2098655 := by exact prefixLift 2098655
  have htrace : WordTrace (prefixWord ++ tailWord_2098655) baseStart_2098655 baseEnd_2098655 := by
    simpa [prefixWord, tailWord_2098655, baseEnd_2098655] using wordTrace_append hprefix tailTrace_2098655
  have hstable : (prefixWord ++ tailWord_2098655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098655).length < 2 ^ (prefixWord ++ tailWord_2098655).sum := by decide
  have hdescent : baseEnd_2098655 < baseStart_2098655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098690 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2098690 : Nat := 118140960795 + 2098690 * 2 ^ 59
def prefixEnd_2098690 : Nat := 4983230072969 + 3 ^ 40 * 2098690 * 2
def baseEnd_2098690 : Nat := 359212238261499699807769

theorem tailTrace_2098690 : CollatzResearch.WordTrace tailWord_2098690 prefixEnd_2098690 359212238261499699807769 := by
  unfold tailWord_2098690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19136378191703008140305381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51030341844541355040814349 19136378191703008140305381)
  ·
    refine ⟨3588070910944314026307259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19136378191703008140305381 3588070910944314026307259)
    ·
      refine ⟨5382106366416471039460889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3588070910944314026307259 5382106366416471039460889)
      ·
        refine ⟨4036579774812353279595667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5382106366416471039460889 4036579774812353279595667)
        ·
          refine ⟨6054869662218529919393501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036579774812353279595667 6054869662218529919393501)
          ·
            refine ⟨2270576123331948719772563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6054869662218529919393501 2270576123331948719772563)
            ·
              refine ⟨3405864184997923079658845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270576123331948719772563 3405864184997923079658845)
              ·
                refine ⟨1277199069374221154872067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3405864184997923079658845 1277199069374221154872067)
                ·
                  refine ⟨1915798604061331732308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277199069374221154872067 1915798604061331732308101)
                  ·
                    refine ⟨359212238261499699807769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915798604061331732308101 359212238261499699807769)
                    ·
                      rfl

theorem cell23_2098690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2098690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098690 prefixEnd_2098690 := by exact prefixLift 2098690
  have htrace : WordTrace (prefixWord ++ tailWord_2098690) baseStart_2098690 baseEnd_2098690 := by
    simpa [prefixWord, tailWord_2098690, baseEnd_2098690] using wordTrace_append hprefix tailTrace_2098690
  have hstable : (prefixWord ++ tailWord_2098690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098690).length < 2 ^ (prefixWord ++ tailWord_2098690).sum := by decide
  have hdescent : baseEnd_2098690 < baseStart_2098690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098739 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3]
def baseStart_2098739 : Nat := 118140960795 + 2098739 * 2 ^ 59
def prefixEnd_2098739 : Nat := 4983230072969 + 3 ^ 40 * 2098739 * 2
def baseEnd_2098739 : Nat := 1077661875336569407710581

theorem tailTrace_2098739 : CollatzResearch.WordTrace tailWord_2098739 prefixEnd_2098739 1077661875336569407710581 := by
  unfold tailWord_2098739
  simp only [CollatzResearch.WordTrace]
  refine ⟨76547299943634513929755271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51031533295756342619836847 76547299943634513929755271)
  ·
    refine ⟨114820949915451770894632907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76547299943634513929755271 114820949915451770894632907)
    ·
      refine ⟨172231424873177656341949361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114820949915451770894632907 172231424873177656341949361)
      ·
        refine ⟨129173568654883242256462021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172231424873177656341949361 129173568654883242256462021)
        ·
          refine ⟨24220044122790607923086629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129173568654883242256462021 24220044122790607923086629)
          ·
            refine ⟨4541258273023238985578743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24220044122790607923086629 4541258273023238985578743)
            ·
              refine ⟨6811887409534858478368115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541258273023238985578743 6811887409534858478368115)
              ·
                refine ⟨10217831114302287717552173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811887409534858478368115 10217831114302287717552173)
                ·
                  refine ⟨3831686667863357894082065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10217831114302287717552173 3831686667863357894082065)
                  ·
                    refine ⟨2873765000897518420561549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831686667863357894082065 2873765000897518420561549)
                    ·
                      refine ⟨1077661875336569407710581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873765000897518420561549 1077661875336569407710581)
                      ·
                        rfl

theorem cell23_2098739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_2098739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098739 prefixEnd_2098739 := by exact prefixLift 2098739
  have htrace : WordTrace (prefixWord ++ tailWord_2098739) baseStart_2098739 baseEnd_2098739 := by
    simpa [prefixWord, tailWord_2098739, baseEnd_2098739] using wordTrace_append hprefix tailTrace_2098739
  have hstable : (prefixWord ++ tailWord_2098739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098739).length < 2 ^ (prefixWord ++ tailWord_2098739).sum := by decide
  have hdescent : baseEnd_2098739 < baseStart_2098739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098770 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_2098770 : Nat := 118140960795 + 2098770 * 2 ^ 59
def prefixEnd_2098770 : Nat := 4983230072969 + 3 ^ 40 * 2098770 * 2
def baseEnd_2098770 : Nat := 1077677793236858786422939

theorem tailTrace_2098770 : CollatzResearch.WordTrace tailWord_2098770 prefixEnd_2098770 1077677793236858786422939 := by
  unfold tailWord_2098770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19137107651630551556033441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51032287071014804149422509 19137107651630551556033441)
  ·
    refine ⟨14352830738722913667025081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19137107651630551556033441 14352830738722913667025081)
    ·
      refine ⟨10764623054042185250268811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14352830738722913667025081 10764623054042185250268811)
      ·
        refine ⟨16146934581063277875403217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10764623054042185250268811 16146934581063277875403217)
        ·
          refine ⟨12110200935797458406552413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16146934581063277875403217 12110200935797458406552413)
          ·
            refine ⟨4541325350924046902457155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12110200935797458406552413 4541325350924046902457155)
            ·
              refine ⟨6811988026386070353685733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541325350924046902457155 6811988026386070353685733)
              ·
                refine ⟨1277247754947388191316075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6811988026386070353685733 1277247754947388191316075)
                ·
                  refine ⟨1915871632421082286974113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277247754947388191316075 1915871632421082286974113)
                  ·
                    refine ⟨1436903724315811715230585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915871632421082286974113 1436903724315811715230585)
                    ·
                      refine ⟨1077677793236858786422939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436903724315811715230585 1077677793236858786422939)
                      ·
                        rfl

theorem cell23_2098770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_2098770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098770 prefixEnd_2098770 := by exact prefixLift 2098770
  have htrace : WordTrace (prefixWord ++ tailWord_2098770) baseStart_2098770 baseEnd_2098770 := by
    simpa [prefixWord, tailWord_2098770, baseEnd_2098770] using wordTrace_append hprefix tailTrace_2098770
  have hstable : (prefixWord ++ tailWord_2098770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098770).length < 2 ^ (prefixWord ++ tailWord_2098770).sum := by decide
  have hdescent : baseEnd_2098770 < baseStart_2098770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098772 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2098772 : Nat := 118140960795 + 2098772 * 2 ^ 59
def prefixEnd_2098772 : Nat := 4983230072969 + 3 ^ 40 * 2098772 * 2
def baseEnd_2098772 : Nat := 359226273399389259532643

theorem tailTrace_2098772 : CollatzResearch.WordTrace tailWord_2098772 prefixEnd_2098772 359226273399389259532643 := by
  unfold tailWord_2098772
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274251776257480282853285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51032335701676640377137713 38274251776257480282853285)
  ·
    refine ⟨7176422208048277553034991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38274251776257480282853285 7176422208048277553034991)
    ·
      refine ⟨10764633312072416329552487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176422208048277553034991 10764633312072416329552487)
      ·
        refine ⟨16146949968108624494328731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10764633312072416329552487 16146949968108624494328731)
        ·
          refine ⟨24220424952162936741493097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16146949968108624494328731 24220424952162936741493097)
          ·
            refine ⟨18165318714122202556119823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24220424952162936741493097 18165318714122202556119823)
            ·
              refine ⟨27247978071183303834179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18165318714122202556119823 27247978071183303834179735)
              ·
                refine ⟨40871967106774955751269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27247978071183303834179735 40871967106774955751269603)
                ·
                  refine ⟨61307950660162433626904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40871967106774955751269603 61307950660162433626904405)
                  ·
                    refine ⟨359226273399389259532643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61307950660162433626904405 359226273399389259532643)
                    ·
                      rfl

theorem cell23_2098772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2098772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098772 prefixEnd_2098772 := by exact prefixLift 2098772
  have htrace : WordTrace (prefixWord ++ tailWord_2098772) baseStart_2098772 baseEnd_2098772 := by
    simpa [prefixWord, tailWord_2098772, baseEnd_2098772] using wordTrace_append hprefix tailTrace_2098772
  have hstable : (prefixWord ++ tailWord_2098772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098772).length < 2 ^ (prefixWord ++ tailWord_2098772).sum := by decide
  have hdescent : baseEnd_2098772 < baseStart_2098772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098796 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_2098796 : Nat := 118140960795 + 2098796 * 2 ^ 59
def prefixEnd_2098796 : Nat := 4983230072969 + 3 ^ 40 * 2098796 * 2
def baseEnd_2098796 : Nat := 1077691143733875684697819

theorem tailTrace_2098796 : CollatzResearch.WordTrace tailWord_2098796 prefixEnd_2098796 1077691143733875684697819 := by
  unfold tailWord_2098796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274689452214006332290121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51032919269618675109720161 38274689452214006332290121)
  ·
    refine ⟨28706017089160504749217591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38274689452214006332290121 28706017089160504749217591)
    ·
      refine ⟨43059025633740757123826387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28706017089160504749217591 43059025633740757123826387)
      ·
        refine ⟨64588538450611135685739581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43059025633740757123826387 64588538450611135685739581)
        ·
          refine ⟨24220701918979175882152343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64588538450611135685739581 24220701918979175882152343)
          ·
            refine ⟨36331052878468763823228515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24220701918979175882152343 36331052878468763823228515)
            ·
              refine ⟨54496579317703145734842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36331052878468763823228515 54496579317703145734842773)
              ·
                refine ⟨2554527155517334956320755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54496579317703145734842773 2554527155517334956320755)
                ·
                  refine ⟨3831790733276002434481133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554527155517334956320755 3831790733276002434481133)
                  ·
                    refine ⟨1436921524978500912930425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3831790733276002434481133 1436921524978500912930425)
                    ·
                      refine ⟨1077691143733875684697819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436921524978500912930425 1077691143733875684697819)
                      ·
                        rfl

theorem cell23_2098796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_2098796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098796 prefixEnd_2098796 := by exact prefixLift 2098796
  have htrace : WordTrace (prefixWord ++ tailWord_2098796) baseStart_2098796 baseEnd_2098796 := by
    simpa [prefixWord, tailWord_2098796, baseEnd_2098796] using wordTrace_append hprefix tailTrace_2098796
  have hstable : (prefixWord ++ tailWord_2098796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098796).length < 2 ^ (prefixWord ++ tailWord_2098796).sum := by decide
  have hdescent : baseEnd_2098796 < baseStart_2098796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098812 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2098812 : Nat := 118140960795 + 2098812 * 2 ^ 59
def prefixEnd_2098812 : Nat := 4983230072969 + 3 ^ 40 * 2098812 * 2
def baseEnd_2098812 : Nat := 1077699359424347622097745

theorem tailTrace_2098812 : CollatzResearch.WordTrace tailWord_2098812 prefixEnd_2098812 1077699359424347622097745 := by
  unfold tailWord_2098812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274981236185023698581345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51033308314913364931441793 38274981236185023698581345)
  ·
    refine ⟨28706235927138767773936009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38274981236185023698581345 28706235927138767773936009)
    ·
      refine ⟨21529676945354075830452007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28706235927138767773936009 21529676945354075830452007)
      ·
        refine ⟨32294515418031113745678011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21529676945354075830452007 32294515418031113745678011)
        ·
          refine ⟨48441773127046670618517017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32294515418031113745678011 48441773127046670618517017)
          ·
            refine ⟨36331329845285002963887763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48441773127046670618517017 36331329845285002963887763)
            ·
              refine ⟨54496994767927504445831645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36331329845285002963887763 54496994767927504445831645)
              ·
                refine ⟨20436373037972814167186867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54496994767927504445831645 20436373037972814167186867)
                ·
                  refine ⟨30654559556959221250780301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20436373037972814167186867 30654559556959221250780301)
                  ·
                    refine ⟨11495459833859707969042613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30654559556959221250780301 11495459833859707969042613)
                    ·
                      refine ⟨1077699359424347622097745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11495459833859707969042613 1077699359424347622097745)
                      ·
                        rfl

theorem cell23_2098812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2098812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098812 prefixEnd_2098812 := by exact prefixLift 2098812
  have htrace : WordTrace (prefixWord ++ tailWord_2098812) baseStart_2098812 baseEnd_2098812 := by
    simpa [prefixWord, tailWord_2098812, baseEnd_2098812] using wordTrace_append hprefix tailTrace_2098812
  have hstable : (prefixWord ++ tailWord_2098812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098812).length < 2 ^ (prefixWord ++ tailWord_2098812).sum := by decide
  have hdescent : baseEnd_2098812 < baseStart_2098812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098813 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_2098813 : Nat := 118140960795 + 2098813 * 2 ^ 59
def prefixEnd_2098813 : Nat := 4983230072969 + 3 ^ 40 * 2098813 * 2
def baseEnd_2098813 : Nat := 1077699872905002118185241

theorem tailTrace_2098813 : CollatzResearch.WordTrace tailWord_2098813 prefixEnd_2098813 1077699872905002118185241 := by
  unfold tailWord_2098813
  simp only [CollatzResearch.WordTrace]
  refine ⟨76549998945366424567949093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51033332630244283045299395 76549998945366424567949093)
  ·
    refine ⟨14353124802256204606490455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76549998945366424567949093 14353124802256204606490455)
    ·
      refine ⟨21529687203384306909735683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14353124802256204606490455 21529687203384306909735683)
      ·
        refine ⟨32294530805076460364603525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21529687203384306909735683 32294530805076460364603525)
        ·
          refine ⟨6055224525951836318363161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32294530805076460364603525 6055224525951836318363161)
          ·
            refine ⟨4541418394463877238772371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6055224525951836318363161 4541418394463877238772371)
            ·
              refine ⟨6812127591695815858158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541418394463877238772371 6812127591695815858158557)
              ·
                refine ⟨2554547846885930946809459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812127591695815858158557 2554547846885930946809459)
                ·
                  refine ⟨3831821770328896420214189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554547846885930946809459 3831821770328896420214189)
                  ·
                    refine ⟨1436933163873336157580321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3831821770328896420214189 1436933163873336157580321)
                    ·
                      refine ⟨1077699872905002118185241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1436933163873336157580321 1077699872905002118185241)
                      ·
                        rfl

theorem cell23_2098813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_2098813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098813 prefixEnd_2098813 := by exact prefixLift 2098813
  have htrace : WordTrace (prefixWord ++ tailWord_2098813) baseStart_2098813 baseEnd_2098813 := by
    simpa [prefixWord, tailWord_2098813, baseEnd_2098813] using wordTrace_append hprefix tailTrace_2098813
  have hstable : (prefixWord ++ tailWord_2098813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098813).length < 2 ^ (prefixWord ++ tailWord_2098813).sum := by decide
  have hdescent : baseEnd_2098813 < baseStart_2098813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098820 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2098820 : Nat := 118140960795 + 2098820 * 2 ^ 59
def prefixEnd_2098820 : Nat := 4983230072969 + 3 ^ 40 * 2098820 * 2
def baseEnd_2098820 : Nat := 1077703467269583590797709

theorem tailTrace_2098820 : CollatzResearch.WordTrace tailWord_2098820 prefixEnd_2098820 1077703467269583590797709 := by
  unfold tailWord_2098820
  simp only [CollatzResearch.WordTrace]
  refine ⟨38275127128170532381726957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51033502837560709842302609 38275127128170532381726957)
  ·
    refine ⟨14353172673063949643147609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38275127128170532381726957 14353172673063949643147609)
    ·
      refine ⟨10764879504797962232360707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14353172673063949643147609 10764879504797962232360707)
      ·
        refine ⟨16147319257196943348541061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10764879504797962232360707 16147319257196943348541061)
        ·
          refine ⟨3027622360724426877851449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16147319257196943348541061 3027622360724426877851449)
          ·
            refine ⟨2270716770543320158388587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027622360724426877851449 2270716770543320158388587)
            ·
              refine ⟨3406075155814980237582881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270716770543320158388587 3406075155814980237582881)
              ·
                refine ⟨2554556366861235178187161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406075155814980237582881 2554556366861235178187161)
                ·
                  refine ⟨1915917275145926383640371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554556366861235178187161 1915917275145926383640371)
                  ·
                    refine ⟨2873875912718889575460557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1915917275145926383640371 2873875912718889575460557)
                    ·
                      refine ⟨1077703467269583590797709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2873875912718889575460557 1077703467269583590797709)
                      ·
                        rfl

theorem cell23_2098820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2098820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098820 prefixEnd_2098820 := by exact prefixLift 2098820
  have htrace : WordTrace (prefixWord ++ tailWord_2098820) baseStart_2098820 baseEnd_2098820 := by
    simpa [prefixWord, tailWord_2098820, baseEnd_2098820] using wordTrace_append hprefix tailTrace_2098820
  have hstable : (prefixWord ++ tailWord_2098820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098820).length < 2 ^ (prefixWord ++ tailWord_2098820).sum := by decide
  have hdescent : baseEnd_2098820 < baseStart_2098820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098839 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2098839 : Nat := 118140960795 + 2098839 * 2 ^ 59
def prefixEnd_2098839 : Nat := 4983230072969 + 3 ^ 40 * 2098839 * 2
def baseEnd_2098839 : Nat := 1077713223402019016460121

theorem tailTrace_2098839 : CollatzResearch.WordTrace tailWord_2098839 prefixEnd_2098839 1077713223402019016460121 := by
  unfold tailWord_2098839
  simp only [CollatzResearch.WordTrace]
  refine ⟨76550947243272231008395571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51033964828848154005597047 76550947243272231008395571)
  ·
    refine ⟨114826420864908346512593357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76550947243272231008395571 114826420864908346512593357)
    ·
      refine ⟨43059907824340629942222509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114826420864908346512593357 43059907824340629942222509)
      ·
        refine ⟨16147465434127736228333441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43059907824340629942222509 16147465434127736228333441)
        ·
          refine ⟨12110599075595802171250081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16147465434127736228333441 12110599075595802171250081)
          ·
            refine ⟨9082949306696851628437561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12110599075595802171250081 9082949306696851628437561)
            ·
              refine ⟨6812211980022638721328171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9082949306696851628437561 6812211980022638721328171)
              ·
                refine ⟨10218317970033958081992257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812211980022638721328171 10218317970033958081992257)
                ·
                  refine ⟨7663738477525468561494193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10218317970033958081992257 7663738477525468561494193)
                  ·
                    refine ⟨5747803858144101421120645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7663738477525468561494193 5747803858144101421120645)
                    ·
                      refine ⟨1077713223402019016460121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5747803858144101421120645 1077713223402019016460121)
                      ·
                        rfl

theorem cell23_2098839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2098839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098839 prefixEnd_2098839 := by exact prefixLift 2098839
  have htrace : WordTrace (prefixWord ++ tailWord_2098839) baseStart_2098839 baseEnd_2098839 := by
    simpa [prefixWord, tailWord_2098839, baseEnd_2098839] using wordTrace_append hprefix tailTrace_2098839
  have hstable : (prefixWord ++ tailWord_2098839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098839).length < 2 ^ (prefixWord ++ tailWord_2098839).sum := by decide
  have hdescent : baseEnd_2098839 < baseStart_2098839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098849 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 7]
def baseStart_2098849 : Nat := 118140960795 + 2098849 * 2 ^ 59
def prefixEnd_2098849 : Nat := 4983230072969 + 3 ^ 40 * 2098849 * 2
def baseEnd_2098849 : Nat := 119746484245395997481675

theorem tailTrace_2098849 : CollatzResearch.WordTrace tailWord_2098849 prefixEnd_2098849 119746484245395997481675 := by
  unfold tailWord_2098849
  simp only [CollatzResearch.WordTrace]
  refine ⟨76551311973236002716259601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51034207982157335144173067 76551311973236002716259601)
  ·
    refine ⟨57413483979927002037194701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76551311973236002716259601 57413483979927002037194701)
    ·
      refine ⟨21530056492472625763948013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57413483979927002037194701 21530056492472625763948013)
      ·
        refine ⟨8073771184677234661480505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21530056492472625763948013 8073771184677234661480505)
        ·
          refine ⟨6055328388507925996110379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8073771184677234661480505 6055328388507925996110379)
          ·
            refine ⟨9082992582761888994165569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6055328388507925996110379 9082992582761888994165569)
            ·
              refine ⟨6812244437071416745624177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9082992582761888994165569 6812244437071416745624177)
              ·
                refine ⟨5109183327803562559218133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6812244437071416745624177 5109183327803562559218133)
                ·
                  refine ⟨119746484245395997481675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5109183327803562559218133 119746484245395997481675)
                  ·
                    rfl

theorem cell23_2098849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_2098849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098849 prefixEnd_2098849 := by exact prefixLift 2098849
  have htrace : WordTrace (prefixWord ++ tailWord_2098849) baseStart_2098849 baseEnd_2098849 := by
    simpa [prefixWord, tailWord_2098849, baseEnd_2098849] using wordTrace_append hprefix tailTrace_2098849
  have hstable : (prefixWord ++ tailWord_2098849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098849).length < 2 ^ (prefixWord ++ tailWord_2098849).sum := by decide
  have hdescent : baseEnd_2098849 < baseStart_2098849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098866 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_2098866 : Nat := 118140960795 + 2098866 * 2 ^ 59
def prefixEnd_2098866 : Nat := 4983230072969 + 3 ^ 40 * 2098866 * 2
def baseEnd_2098866 : Nat := 119747454153298934535833

theorem tailTrace_2098866 : CollatzResearch.WordTrace tailWord_2098866 prefixEnd_2098866 119747454153298934535833 := by
  unfold tailWord_2098866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19137983003543603654907113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51034621342782943079752301 19137983003543603654907113)
  ·
    refine ⟨14353487252657702741180335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19137983003543603654907113 14353487252657702741180335)
    ·
      refine ⟨21530230878986554111770503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14353487252657702741180335 21530230878986554111770503)
      ·
        refine ⟨32295346318479831167655755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21530230878986554111770503 32295346318479831167655755)
        ·
          refine ⟨48443019477719746751483633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32295346318479831167655755 48443019477719746751483633)
          ·
            refine ⟨36332264608289810063612725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48443019477719746751483633 36332264608289810063612725)
            ·
              refine ⟨3406149807027169693463693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36332264608289810063612725 3406149807027169693463693)
              ·
                refine ⟨1277306177635188635048885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3406149807027169693463693 1277306177635188635048885)
                ·
                  refine ⟨119747454153298934535833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277306177635188635048885 119747454153298934535833)
                  ·
                    rfl

theorem cell23_2098866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_2098866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098866 prefixEnd_2098866 := by exact prefixLift 2098866
  have htrace : WordTrace (prefixWord ++ tailWord_2098866) baseStart_2098866 baseEnd_2098866 := by
    simpa [prefixWord, tailWord_2098866, baseEnd_2098866] using wordTrace_append hprefix tailTrace_2098866
  have hstable : (prefixWord ++ tailWord_2098866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098866).length < 2 ^ (prefixWord ++ tailWord_2098866).sum := by decide
  have hdescent : baseEnd_2098866 < baseStart_2098866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098872 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2098872 : Nat := 118140960795 + 2098872 * 2 ^ 59
def prefixEnd_2098872 : Nat := 4983230072969 + 3 ^ 40 * 2098872 * 2
def baseEnd_2098872 : Nat := 1077730168263617387347469

theorem tailTrace_2098872 : CollatzResearch.WordTrace tailWord_2098872 prefixEnd_2098872 1077730168263617387347469 := by
  unfold tailWord_2098872
  simp only [CollatzResearch.WordTrace]
  refine ⟨38276075426076338822173435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51034767234768451762897913 38276075426076338822173435)
  ·
    refine ⟨57414113139114508233260153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38276075426076338822173435 57414113139114508233260153)
    ·
      refine ⟨43060584854335881174945115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57414113139114508233260153 43060584854335881174945115)
      ·
        refine ⟨64590877281503821762417673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43060584854335881174945115 64590877281503821762417673)
        ·
          refine ⟨48443157961127866321813255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64590877281503821762417673 48443157961127866321813255)
          ·
            refine ⟨72664736941691799482719883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48443157961127866321813255 72664736941691799482719883)
            ·
              refine ⟨108997105412537699224079825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72664736941691799482719883 108997105412537699224079825)
              ·
                refine ⟨81747829059403274418059869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108997105412537699224079825 81747829059403274418059869)
                ·
                  refine ⟨30655435897276227906772451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81747829059403274418059869 30655435897276227906772451)
                  ·
                    refine ⟨45983153845914341860158677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30655435897276227906772451 45983153845914341860158677)
                    ·
                      refine ⟨1077730168263617387347469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45983153845914341860158677 1077730168263617387347469)
                      ·
                        rfl

theorem cell23_2098872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2098872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098872 prefixEnd_2098872 := by exact prefixLift 2098872
  have htrace : WordTrace (prefixWord ++ tailWord_2098872) baseStart_2098872 baseEnd_2098872 := by
    simpa [prefixWord, tailWord_2098872, baseEnd_2098872] using wordTrace_append hprefix tailTrace_2098872
  have hstable : (prefixWord ++ tailWord_2098872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098872).length < 2 ^ (prefixWord ++ tailWord_2098872).sum := by decide
  have hdescent : baseEnd_2098872 < baseStart_2098872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098879 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 2, 5]
def baseStart_2098879 : Nat := 118140960795 + 2098879 * 2 ^ 59
def prefixEnd_2098879 : Nat := 4983230072969 + 3 ^ 40 * 2098879 * 2
def baseEnd_2098879 : Nat := 359244587542732953319979

theorem tailTrace_2098879 : CollatzResearch.WordTrace tailWord_2098879 prefixEnd_2098879 359244587542732953319979 := by
  unfold tailWord_2098879
  simp only [CollatzResearch.WordTrace]
  refine ⟨76552406163127317839851691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51034937442084878559901127 76552406163127317839851691)
  ·
    refine ⟨114828609244690976759777537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76552406163127317839851691 114828609244690976759777537)
    ·
      refine ⟨86121456933518232569833153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114828609244690976759777537 86121456933518232569833153)
      ·
        refine ⟨64591092700138674427374865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86121456933518232569833153 64591092700138674427374865)
        ·
          refine ⟨48443319525104005820531149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64591092700138674427374865 48443319525104005820531149)
          ·
            refine ⟨18166244821914002182699181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48443319525104005820531149 18166244821914002182699181)
            ·
              refine ⟨6812341808217750818512193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18166244821914002182699181 6812341808217750818512193)
              ·
                refine ⟨5109256356163313113884145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6812341808217750818512193 5109256356163313113884145)
                ·
                  refine ⟨3831942267122484835413109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5109256356163313113884145 3831942267122484835413109)
                  ·
                    refine ⟨359244587542732953319979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3831942267122484835413109 359244587542732953319979)
                    ·
                      rfl

theorem cell23_2098879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_2098879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098879 prefixEnd_2098879 := by exact prefixLift 2098879
  have htrace : WordTrace (prefixWord ++ tailWord_2098879) baseStart_2098879 baseEnd_2098879 := by
    simpa [prefixWord, tailWord_2098879, baseEnd_2098879] using wordTrace_append hprefix tailTrace_2098879
  have hstable : (prefixWord ++ tailWord_2098879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098879).length < 2 ^ (prefixWord ++ tailWord_2098879).sum := by decide
  have hdescent : baseEnd_2098879 < baseStart_2098879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098916 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_2098916 : Nat := 118140960795 + 2098916 * 2 ^ 59
def prefixEnd_2098916 : Nat := 4983230072969 + 3 ^ 40 * 2098916 * 2
def baseEnd_2098916 : Nat := 1077752761412415215197267

theorem tailTrace_2098916 : CollatzResearch.WordTrace tailWord_2098916 prefixEnd_2098916 1077752761412415215197267 := by
  unfold tailWord_2098916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38276877831996636579474301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51035837109328848772632401 38276877831996636579474301)
  ·
    refine ⟨14353829186998738717302863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38276877831996636579474301 14353829186998738717302863)
    ·
      refine ⟨21530743780498108075954295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14353829186998738717302863 21530743780498108075954295)
      ·
        refine ⟨32296115670747162113931443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21530743780498108075954295 32296115670747162113931443)
        ·
          refine ⟨48444173506120743170897165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32296115670747162113931443 48444173506120743170897165)
          ·
            refine ⟨18166565064795278689086437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48444173506120743170897165 18166565064795278689086437)
            ·
              refine ⟨3406230949649114754203707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18166565064795278689086437 3406230949649114754203707)
              ·
                refine ⟨5109346424473672131305561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406230949649114754203707 5109346424473672131305561)
                ·
                  refine ⟨3832009818355254098479171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5109346424473672131305561 3832009818355254098479171)
                  ·
                    refine ⟨5748014727532881147718757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832009818355254098479171 5748014727532881147718757)
                    ·
                      refine ⟨1077752761412415215197267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5748014727532881147718757 1077752761412415215197267)
                      ·
                        rfl

theorem cell23_2098916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_2098916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098916 prefixEnd_2098916 := by exact prefixLift 2098916
  have htrace : WordTrace (prefixWord ++ tailWord_2098916) baseStart_2098916 baseEnd_2098916 := by
    simpa [prefixWord, tailWord_2098916, baseEnd_2098916] using wordTrace_append hprefix tailTrace_2098916
  have hstable : (prefixWord ++ tailWord_2098916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098916).length < 2 ^ (prefixWord ++ tailWord_2098916).sum := by decide
  have hdescent : baseEnd_2098916 < baseStart_2098916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098949 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_2098949 : Nat := 118140960795 + 2098949 * 2 ^ 59
def prefixEnd_2098949 : Nat := 4983230072969 + 3 ^ 40 * 2098949 * 2
def baseEnd_2098949 : Nat := 1077769706274013586084615

theorem tailTrace_2098949 : CollatzResearch.WordTrace tailWord_2098949 prefixEnd_2098949 1077769706274013586084615 := by
  unfold tailWord_2098949
  simp only [CollatzResearch.WordTrace]
  refine ⟨76554959272873719794899901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51036639515249146529933267 76554959272873719794899901)
  ·
    refine ⟨28708109727327644923087463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76554959272873719794899901 28708109727327644923087463)
    ·
      refine ⟨43062164590991467384631195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28708109727327644923087463 43062164590991467384631195)
      ·
        refine ⟨64593246886487201076946793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43062164590991467384631195 64593246886487201076946793)
        ·
          refine ⟨48444935164865400807710095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64593246886487201076946793 48444935164865400807710095)
          ·
            refine ⟨72667402747298101211565143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48444935164865400807710095 72667402747298101211565143)
            ·
              refine ⟨109001104120947151817347715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72667402747298101211565143 109001104120947151817347715)
              ·
                refine ⟨163501656181420727726021573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109001104120947151817347715 163501656181420727726021573)
                ·
                  refine ⟨30656560534016386448629045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163501656181420727726021573 30656560534016386448629045)
                  ·
                    refine ⟨2874052550064036229558973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30656560534016386448629045 2874052550064036229558973)
                    ·
                      refine ⟨1077769706274013586084615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874052550064036229558973 1077769706274013586084615)
                      ·
                        rfl

theorem cell23_2098949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_2098949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098949 prefixEnd_2098949 := by exact prefixLift 2098949
  have htrace : WordTrace (prefixWord ++ tailWord_2098949) baseStart_2098949 baseEnd_2098949 := by
    simpa [prefixWord, tailWord_2098949, baseEnd_2098949] using wordTrace_append hprefix tailTrace_2098949
  have hstable : (prefixWord ++ tailWord_2098949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098949).length < 2 ^ (prefixWord ++ tailWord_2098949).sum := by decide
  have hdescent : baseEnd_2098949 < baseStart_2098949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098964 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2098964 : Nat := 118140960795 + 2098964 * 2 ^ 59
def prefixEnd_2098964 : Nat := 4983230072969 + 3 ^ 40 * 2098964 * 2
def baseEnd_2098964 : Nat := 359259136161277009132349

theorem tailTrace_2098964 : CollatzResearch.WordTrace tailWord_2098964 prefixEnd_2098964 359259136161277009132349 := by
  unfold tailWord_2098964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38277753183909688678347973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51037004245212918237797297 38277753183909688678347973)
  ·
    refine ⟨7177078721983066627190245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38277753183909688678347973 7177078721983066627190245)
    ·
      refine ⟨1345702260371824992598171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7177078721983066627190245 1345702260371824992598171)
      ·
        refine ⟨2018553390557737488897257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345702260371824992598171 2018553390557737488897257)
        ·
          refine ⟨1513915042918303116672943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018553390557737488897257 1513915042918303116672943)
          ·
            refine ⟨2270872564377454675009415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513915042918303116672943 2270872564377454675009415)
            ·
              refine ⟨3406308846566182012514123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270872564377454675009415 3406308846566182012514123)
              ·
                refine ⟨5109463269849273018771185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406308846566182012514123 5109463269849273018771185)
                ·
                  refine ⟨3832097452386954764078389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5109463269849273018771185 3832097452386954764078389)
                  ·
                    refine ⟨359259136161277009132349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3832097452386954764078389 359259136161277009132349)
                    ·
                      rfl

theorem cell23_2098964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2098964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098964 prefixEnd_2098964 := by exact prefixLift 2098964
  have htrace : WordTrace (prefixWord ++ tailWord_2098964) baseStart_2098964 baseEnd_2098964 := by
    simpa [prefixWord, tailWord_2098964, baseEnd_2098964] using wordTrace_append hprefix tailTrace_2098964
  have hstable : (prefixWord ++ tailWord_2098964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098964).length < 2 ^ (prefixWord ++ tailWord_2098964).sum := by decide
  have hdescent : baseEnd_2098964 < baseStart_2098964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098990 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_2098990 : Nat := 118140960795 + 2098990 * 2 ^ 59
def prefixEnd_2098990 : Nat := 4983230072969 + 3 ^ 40 * 2098990 * 2
def baseEnd_2098990 : Nat := 119754528775649769519103

theorem tailTrace_2098990 : CollatzResearch.WordTrace tailWord_2098990 prefixEnd_2098990 119754528775649769519103 := by
  unfold tailWord_2098990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569556833215647974642803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51037636443816789198094949 9569556833215647974642803)
  ·
    refine ⟨14354335249823471961964205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9569556833215647974642803 14354335249823471961964205)
    ·
      refine ⟨5382875718683801985736577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14354335249823471961964205 5382875718683801985736577)
      ·
        refine ⟨4037156789012851489302433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5382875718683801985736577 4037156789012851489302433)
        ·
          refine ⟨3027867591759638616976825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037156789012851489302433 3027867591759638616976825)
          ·
            refine ⟨2270900693819728962732619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027867591759638616976825 2270900693819728962732619)
            ·
              refine ⟨3406351040729593444098929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270900693819728962732619 3406351040729593444098929)
              ·
                refine ⟨2554763280547195083074197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406351040729593444098929 2554763280547195083074197)
                ·
                  refine ⟨119754528775649769519103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2554763280547195083074197 119754528775649769519103)
                  ·
                    rfl

theorem cell23_2098990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_2098990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2098990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2098990 prefixEnd_2098990 := by exact prefixLift 2098990
  have htrace : WordTrace (prefixWord ++ tailWord_2098990) baseStart_2098990 baseEnd_2098990 := by
    simpa [prefixWord, tailWord_2098990, baseEnd_2098990] using wordTrace_append hprefix tailTrace_2098990
  have hstable : (prefixWord ++ tailWord_2098990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098990).length < 2 ^ (prefixWord ++ tailWord_2098990).sum := by decide
  have hdescent : baseEnd_2098990 < baseStart_2098990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099000 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_2099000 : Nat := 118140960795 + 2099000 * 2 ^ 59
def prefixEnd_2099000 : Nat := 4983230072969 + 3 ^ 40 * 2099000 * 2
def baseEnd_2099000 : Nat := 1077795893787392886546881

theorem tailTrace_2099000 : CollatzResearch.WordTrace tailWord_2099000 prefixEnd_2099000 1077795893787392886546881 := by
  unfold tailWord_2099000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38278409697844477752503227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51037879597125970336670969 38278409697844477752503227)
  ·
    refine ⟨57417614546766716628754841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38278409697844477752503227 57417614546766716628754841)
    ·
      refine ⟨43063210910075037471566131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57417614546766716628754841 43063210910075037471566131)
      ·
        refine ⟨64594816365112556207349197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43063210910075037471566131 64594816365112556207349197)
        ·
          refine ⟨24223056136917208577755949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64594816365112556207349197 24223056136917208577755949)
          ·
            refine ⟨9083646051343953216658481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24223056136917208577755949 9083646051343953216658481)
            ·
              refine ⟨6812734538507964912493861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9083646051343953216658481 6812734538507964912493861)
              ·
                refine ⟨1277387725970243421092599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6812734538507964912493861 1277387725970243421092599)
                ·
                  refine ⟨1916081588955365131638899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277387725970243421092599 1916081588955365131638899)
                  ·
                    refine ⟨2874122383433047697458349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1916081588955365131638899 2874122383433047697458349)
                    ·
                      refine ⟨1077795893787392886546881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874122383433047697458349 1077795893787392886546881)
                      ·
                        rfl

theorem cell23_2099000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_2099000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099000 prefixEnd_2099000 := by exact prefixLift 2099000
  have htrace : WordTrace (prefixWord ++ tailWord_2099000) baseStart_2099000 baseEnd_2099000 := by
    simpa [prefixWord, tailWord_2099000, baseEnd_2099000] using wordTrace_append hprefix tailTrace_2099000
  have hstable : (prefixWord ++ tailWord_2099000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099000).length < 2 ^ (prefixWord ++ tailWord_2099000).sum := by decide
  have hdescent : baseEnd_2099000 < baseStart_2099000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099016 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_2099016 : Nat := 118140960795 + 2099016 * 2 ^ 59
def prefixEnd_2099016 : Nat := 4983230072969 + 3 ^ 40 * 2099016 * 2
def baseEnd_2099016 : Nat := 359268036492621607982269

theorem tailTrace_2099016 : CollatzResearch.WordTrace tailWord_2099016 prefixEnd_2099016 359268036492621607982269 := by
  unfold tailWord_2099016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38278701481815495118794451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51038268642420660158392601 38278701481815495118794451)
  ·
    refine ⟨57418052222723242678191677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38278701481815495118794451 57418052222723242678191677)
    ·
      refine ⟨21531769583521216004321879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57418052222723242678191677 21531769583521216004321879)
      ·
        refine ⟨32297654375281824006482819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21531769583521216004321879 32297654375281824006482819)
        ·
          refine ⟨48446481562922736009724229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32297654375281824006482819 48446481562922736009724229)
          ·
            refine ⟨9083715293048013001823293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48446481562922736009724229 9083715293048013001823293)
            ·
              refine ⟨3406393234893004875683735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9083715293048013001823293 3406393234893004875683735)
              ·
                refine ⟨5109589852339507313525603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406393234893004875683735 5109589852339507313525603)
                ·
                  refine ⟨7664384778509260970288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109589852339507313525603 7664384778509260970288405)
                  ·
                    refine ⟨359268036492621607982269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7664384778509260970288405 359268036492621607982269)
                    ·
                      rfl

theorem cell23_2099016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_2099016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099016 prefixEnd_2099016 := by exact prefixLift 2099016
  have htrace : WordTrace (prefixWord ++ tailWord_2099016) baseStart_2099016 baseEnd_2099016 := by
    simpa [prefixWord, tailWord_2099016, baseEnd_2099016] using wordTrace_append hprefix tailTrace_2099016
  have hstable : (prefixWord ++ tailWord_2099016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099016).length < 2 ^ (prefixWord ++ tailWord_2099016).sum := by decide
  have hdescent : baseEnd_2099016 < baseStart_2099016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099043 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2099043 : Nat := 118140960795 + 2099043 * 2 ^ 59
def prefixEnd_2099043 : Nat := 4983230072969 + 3 ^ 40 * 2099043 * 2
def baseEnd_2099043 : Nat := 1077817973455536218309183

theorem tailTrace_2099043 : CollatzResearch.WordTrace tailWord_2099043 prefixEnd_2099043 1077817973455536218309183 := by
  unfold tailWord_2099043
  simp only [CollatzResearch.WordTrace]
  refine ⟨76558387734533173848821783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51038925156355449232547855 76558387734533173848821783)
  ·
    refine ⟨114837581601799760773232675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76558387734533173848821783 114837581601799760773232675)
    ·
      refine ⟨172256372402699641159849013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114837581601799760773232675 172256372402699641159849013)
      ·
        refine ⟨16149034912753091358735845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172256372402699641159849013 16149034912753091358735845)
        ·
          refine ⟨3027944046141204629762971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16149034912753091358735845 3027944046141204629762971)
          ·
            refine ⟨4541916069211806944644457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027944046141204629762971 4541916069211806944644457)
            ·
              refine ⟨3406437051908855208483343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541916069211806944644457 3406437051908855208483343)
              ·
                refine ⟨5109655577863282812725015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406437051908855208483343 5109655577863282812725015)
                ·
                  refine ⟨7664483366794924219087523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109655577863282812725015 7664483366794924219087523)
                  ·
                    refine ⟨11496725050192386328631285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7664483366794924219087523 11496725050192386328631285)
                    ·
                      refine ⟨1077817973455536218309183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11496725050192386328631285 1077817973455536218309183)
                      ·
                        rfl

theorem cell23_2099043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2099043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099043 prefixEnd_2099043 := by exact prefixLift 2099043
  have htrace : WordTrace (prefixWord ++ tailWord_2099043) baseStart_2099043 baseEnd_2099043 := by
    simpa [prefixWord, tailWord_2099043, baseEnd_2099043] using wordTrace_append hprefix tailTrace_2099043
  have hstable : (prefixWord ++ tailWord_2099043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099043).length < 2 ^ (prefixWord ++ tailWord_2099043).sum := by decide
  have hdescent : baseEnd_2099043 < baseStart_2099043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099059 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 7]
def baseStart_2099059 : Nat := 118140960795 + 2099059 * 2 ^ 59
def prefixEnd_2099059 : Nat := 4983230072969 + 3 ^ 40 * 2099059 * 2
def baseEnd_2099059 : Nat := 359275396382002718569703

theorem tailTrace_2099059 : CollatzResearch.WordTrace tailWord_2099059 prefixEnd_2099059 359275396382002718569703 := by
  unfold tailWord_2099059
  simp only [CollatzResearch.WordTrace]
  refine ⟨76558971302475208581404231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51039314201650139054269487 76558971302475208581404231)
  ·
    refine ⟨114838456953712812872106347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76558971302475208581404231 114838456953712812872106347)
    ·
      refine ⟨172257685430569219308159521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114838456953712812872106347 172257685430569219308159521)
      ·
        refine ⟨129193264072926914481119641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172257685430569219308159521 129193264072926914481119641)
        ·
          refine ⟨96894948054695185860839731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129193264072926914481119641 96894948054695185860839731)
          ·
            refine ⟨145342422082042778791259597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96894948054695185860839731 145342422082042778791259597)
            ·
              refine ⟨54503408280766042046722349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145342422082042778791259597 54503408280766042046722349)
              ·
                refine ⟨20438778105287265767520881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54503408280766042046722349 20438778105287265767520881)
                ·
                  refine ⟨15329083578965449325640661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20438778105287265767520881 15329083578965449325640661)
                  ·
                    refine ⟨359275396382002718569703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15329083578965449325640661 359275396382002718569703)
                    ·
                      rfl

theorem cell23_2099059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_2099059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099059 prefixEnd_2099059 := by exact prefixLift 2099059
  have htrace : WordTrace (prefixWord ++ tailWord_2099059) baseStart_2099059 baseEnd_2099059 := by
    simpa [prefixWord, tailWord_2099059, baseEnd_2099059] using wordTrace_append hprefix tailTrace_2099059
  have hstable : (prefixWord ++ tailWord_2099059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099059).length < 2 ^ (prefixWord ++ tailWord_2099059).sum := by decide
  have hdescent : baseEnd_2099059 < baseStart_2099059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099090 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2099090 : Nat := 118140960795 + 2099090 * 2 ^ 59
def prefixEnd_2099090 : Nat := 4983230072969 + 3 ^ 40 * 2099090 * 2
def baseEnd_2099090 : Nat := 1077842107046297534421467

theorem tailTrace_2099090 : CollatzResearch.WordTrace tailWord_2099090 prefixEnd_2099090 1077842107046297534421467 := by
  unfold tailWord_2099090
  simp only [CollatzResearch.WordTrace]
  refine ⟨19140025491340725218945681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51040067976908600583855149 19140025491340725218945681)
  ·
    refine ⟨14355019118505543914209261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19140025491340725218945681 14355019118505543914209261)
    ·
      refine ⟨5383132169439578967828473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14355019118505543914209261 5383132169439578967828473)
      ·
        refine ⟨4037349127079684225871355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5383132169439578967828473 4037349127079684225871355)
        ·
          refine ⟨6056023690619526338807033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4037349127079684225871355 6056023690619526338807033)
          ·
            refine ⟨4542017767964644754105275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6056023690619526338807033 4542017767964644754105275)
            ·
              refine ⟨6813026651946967131157913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542017767964644754105275 6813026651946967131157913)
              ·
                refine ⟨5109769988960225348368435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6813026651946967131157913 5109769988960225348368435)
                ·
                  refine ⟨7664654983440338022552653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109769988960225348368435 7664654983440338022552653)
                  ·
                    refine ⟨2874245618790126758457245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7664654983440338022552653 2874245618790126758457245)
                    ·
                      refine ⟨1077842107046297534421467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874245618790126758457245 1077842107046297534421467)
                      ·
                        rfl

theorem cell23_2099090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2099090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099090 prefixEnd_2099090 := by exact prefixLift 2099090
  have htrace : WordTrace (prefixWord ++ tailWord_2099090) baseStart_2099090 baseEnd_2099090 := by
    simpa [prefixWord, tailWord_2099090, baseEnd_2099090] using wordTrace_append hprefix tailTrace_2099090
  have hstable : (prefixWord ++ tailWord_2099090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099090).length < 2 ^ (prefixWord ++ tailWord_2099090).sum := by decide
  have hdescent : baseEnd_2099090 < baseStart_2099090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099094 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2099094 : Nat := 118140960795 + 2099094 * 2 ^ 59
def prefixEnd_2099094 : Nat := 4983230072969 + 3 ^ 40 * 2099094 * 2
def baseEnd_2099094 : Nat := 1077844160968915518771449

theorem tailTrace_2099094 : CollatzResearch.WordTrace tailWord_2099094 prefixEnd_2099094 1077844160968915518771449 := by
  unfold tailWord_2099094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785015491084275597433021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51040165238232273039285557 4785015491084275597433021)
  ·
    refine ⟨1794380809156603349037383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4785015491084275597433021 1794380809156603349037383)
    ·
      refine ⟨2691571213734905023556075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794380809156603349037383 2691571213734905023556075)
      ·
        refine ⟨4037356820602357535334113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691571213734905023556075 4037356820602357535334113)
        ·
          refine ⟨3028017615451768151500585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037356820602357535334113 3028017615451768151500585)
          ·
            refine ⟨2271013211588826113625439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3028017615451768151500585 2271013211588826113625439)
            ·
              refine ⟨3406519817383239170438159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271013211588826113625439 3406519817383239170438159)
              ·
                refine ⟨5109779726074858755657239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406519817383239170438159 5109779726074858755657239)
                ·
                  refine ⟨7664669589112288133485859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109779726074858755657239 7664669589112288133485859)
                  ·
                    refine ⟨11497004383668432200228789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7664669589112288133485859 11497004383668432200228789)
                    ·
                      refine ⟨1077844160968915518771449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11497004383668432200228789 1077844160968915518771449)
                      ·
                        rfl

theorem cell23_2099094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2099094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099094 prefixEnd_2099094 := by exact prefixLift 2099094
  have htrace : WordTrace (prefixWord ++ tailWord_2099094) baseStart_2099094 baseEnd_2099094 := by
    simpa [prefixWord, tailWord_2099094, baseEnd_2099094] using wordTrace_append hprefix tailTrace_2099094
  have hstable : (prefixWord ++ tailWord_2099094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099094).length < 2 ^ (prefixWord ++ tailWord_2099094).sum := by decide
  have hdescent : baseEnd_2099094 < baseStart_2099094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099136 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 7]
def baseStart_2099136 : Nat := 118140960795 + 2099136 * 2 ^ 59
def prefixEnd_2099136 : Nat := 4983230072969 + 3 ^ 40 * 2099136 * 2
def baseEnd_2099136 : Nat := 119762858572933817160695

theorem tailTrace_2099136 : CollatzResearch.WordTrace tailWord_2099136 prefixEnd_2099136 119762858572933817160695 := by
  unfold tailWord_2099136
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280889861598125365978631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51041186482130833821304841 38280889861598125365978631)
  ·
    refine ⟨57421334792397188048967947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38280889861598125365978631 57421334792397188048967947)
    ·
      refine ⟨86132002188595782073451921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57421334792397188048967947 86132002188595782073451921)
      ·
        refine ⟨64599001641446836555088941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86132002188595782073451921 64599001641446836555088941)
        ·
          refine ⟨24224625615542563708158353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64599001641446836555088941 24224625615542563708158353)
          ·
            refine ⟨18168469211656922781118765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24224625615542563708158353 18168469211656922781118765)
            ·
              refine ⟨6813175954371346042919537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18168469211656922781118765 6813175954371346042919537)
              ·
                refine ⟨5109881965778509532189653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6813175954371346042919537 5109881965778509532189653)
                ·
                  refine ⟨119762858572933817160695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5109881965778509532189653 119762858572933817160695)
                  ·
                    rfl

theorem cell23_2099136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_2099136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099136 prefixEnd_2099136 := by exact prefixLift 2099136
  have htrace : WordTrace (prefixWord ++ tailWord_2099136) baseStart_2099136 baseEnd_2099136 := by
    simpa [prefixWord, tailWord_2099136, baseEnd_2099136] using wordTrace_append hprefix tailTrace_2099136
  have hstable : (prefixWord ++ tailWord_2099136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099136).length < 2 ^ (prefixWord ++ tailWord_2099136).sum := by decide
  have hdescent : baseEnd_2099136 < baseStart_2099136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099176 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2099176 : Nat := 118140960795 + 2099176 * 2 ^ 59
def prefixEnd_2099176 : Nat := 4983230072969 + 3 ^ 40 * 2099176 * 2
def baseEnd_2099176 : Nat := 1077886266382584197946071

theorem tailTrace_2099176 : CollatzResearch.WordTrace tailWord_2099176 prefixEnd_2099176 1077886266382584197946071 := by
  unfold tailWord_2099176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38281619321525668781706691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51042159095367558375608921 38281619321525668781706691)
  ·
    refine ⟨57422428982288503172560037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38281619321525668781706691 57422428982288503172560037)
    ·
      refine ⟨10766705434179094344855007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57422428982288503172560037 10766705434179094344855007)
      ·
        refine ⟨16150058151268641517282511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10766705434179094344855007 16150058151268641517282511)
        ·
          refine ⟨24225087226902962275923767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16150058151268641517282511 24225087226902962275923767)
          ·
            refine ⟨36337630840354443413885651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24225087226902962275923767 36337630840354443413885651)
            ·
              refine ⟨54506446260531665120828477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36337630840354443413885651 54506446260531665120828477)
              ·
                refine ⟨20439917347699374420310679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54506446260531665120828477 20439917347699374420310679)
                ·
                  refine ⟨30659876021549061630466019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20439917347699374420310679 30659876021549061630466019)
                  ·
                    refine ⟨45989814032323592445699029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30659876021549061630466019 45989814032323592445699029)
                    ·
                      refine ⟨1077886266382584197946071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45989814032323592445699029 1077886266382584197946071)
                      ·
                        rfl

theorem cell23_2099176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2099176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099176 prefixEnd_2099176 := by exact prefixLift 2099176
  have htrace : WordTrace (prefixWord ++ tailWord_2099176) baseStart_2099176 baseEnd_2099176 := by
    simpa [prefixWord, tailWord_2099176, baseEnd_2099176] using wordTrace_append hprefix tailTrace_2099176
  have hstable : (prefixWord ++ tailWord_2099176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099176).length < 2 ^ (prefixWord ++ tailWord_2099176).sum := by decide
  have hdescent : baseEnd_2099176 < baseStart_2099176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099181 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2099181 : Nat := 118140960795 + 2099181 * 2 ^ 59
def prefixEnd_2099181 : Nat := 4983230072969 + 3 ^ 40 * 2099181 * 2
def baseEnd_2099181 : Nat := 1077888833785856678383549

theorem tailTrace_2099181 : CollatzResearch.WordTrace tailWord_2099181 prefixEnd_2099181 1077888833785856678383549 := by
  unfold tailWord_2099181
  simp only [CollatzResearch.WordTrace]
  refine ⟨76563421008033223417345397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51042280672022148944896931 76563421008033223417345397)
  ·
    refine ⟨7177820719503114695376131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76563421008033223417345397 7177820719503114695376131)
    ·
      refine ⟨10766731079254672043064197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7177820719503114695376131 10766731079254672043064197)
      ·
        refine ⟨2018762077360251008074537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10766731079254672043064197 2018762077360251008074537)
        ·
          refine ⟨1514071558020188256055903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018762077360251008074537 1514071558020188256055903)
          ·
            refine ⟨2271107337030282384083855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514071558020188256055903 2271107337030282384083855)
            ·
              refine ⟨3406661005545423576125783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271107337030282384083855 3406661005545423576125783)
              ·
                refine ⟨5109991508318135364188675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406661005545423576125783 5109991508318135364188675)
                ·
                  refine ⟨7664987262477203046283013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109991508318135364188675 7664987262477203046283013)
                  ·
                    refine ⟨1437185111714475571178065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7664987262477203046283013 1437185111714475571178065)
                    ·
                      refine ⟨1077888833785856678383549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437185111714475571178065 1077888833785856678383549)
                      ·
                        rfl

theorem cell23_2099181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2099181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099181 prefixEnd_2099181 := by exact prefixLift 2099181
  have htrace : WordTrace (prefixWord ++ tailWord_2099181) baseStart_2099181 baseEnd_2099181 := by
    simpa [prefixWord, tailWord_2099181, baseEnd_2099181] using wordTrace_append hprefix tailTrace_2099181
  have hstable : (prefixWord ++ tailWord_2099181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099181).length < 2 ^ (prefixWord ++ tailWord_2099181).sum := by decide
  have hdescent : baseEnd_2099181 < baseStart_2099181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099196 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_2099196 : Nat := 118140960795 + 2099196 * 2 ^ 59
def prefixEnd_2099196 : Nat := 4983230072969 + 3 ^ 40 * 2099196 * 2
def baseEnd_2099196 : Nat := 359298845331891373231993

theorem tailTrace_2099196 : CollatzResearch.WordTrace tailWord_2099196 prefixEnd_2099196 359298845331891373231993 := by
  unfold tailWord_2099196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38281984051489440489570721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51042645401985920652760961 38281984051489440489570721)
  ·
    refine ⟨28711488038617080367178041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38281984051489440489570721 28711488038617080367178041)
    ·
      refine ⟨21533616028962810275383531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28711488038617080367178041 21533616028962810275383531)
      ·
        refine ⟨32300424043444215413075297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21533616028962810275383531 32300424043444215413075297)
        ·
          refine ⟨24225318032583161559806473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32300424043444215413075297 24225318032583161559806473)
          ·
            refine ⟨18168988524437371169854855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24225318032583161559806473 18168988524437371169854855)
            ·
              refine ⟨27253482786656056754782283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18168988524437371169854855 27253482786656056754782283)
              ·
                refine ⟨40880224179984085132173425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27253482786656056754782283 40880224179984085132173425)
                ·
                  refine ⟨30660168134988063849130069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40880224179984085132173425 30660168134988063849130069)
                  ·
                    refine ⟨359298845331891373231993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30660168134988063849130069 359298845331891373231993)
                    ·
                      rfl

theorem cell23_2099196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2099196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099196 prefixEnd_2099196 := by exact prefixLift 2099196
  have htrace : WordTrace (prefixWord ++ tailWord_2099196) baseStart_2099196 baseEnd_2099196 := by
    simpa [prefixWord, tailWord_2099196, baseEnd_2099196] using wordTrace_append hprefix tailTrace_2099196
  have hstable : (prefixWord ++ tailWord_2099196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099196).length < 2 ^ (prefixWord ++ tailWord_2099196).sum := by decide
  have hdescent : baseEnd_2099196 < baseStart_2099196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099203 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 6, 2]
def baseStart_2099203 : Nat := 118140960795 + 2099203 * 2 ^ 59
def prefixEnd_2099203 : Nat := 4983230072969 + 3 ^ 40 * 2099203 * 2
def baseEnd_2099203 : Nat := 1077900130360255592308447

theorem tailTrace_2099203 : CollatzResearch.WordTrace tailWord_2099203 prefixEnd_2099203 1077900130360255592308447 := by
  unfold tailWord_2099203
  simp only [CollatzResearch.WordTrace]
  refine ⟨76564223413953521174646263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51042815609302347449764175 76564223413953521174646263)
  ·
    refine ⟨114846335120930281761969395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76564223413953521174646263 114846335120930281761969395)
    ·
      refine ⟨172269502681395422642954093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114846335120930281761969395 172269502681395422642954093)
      ·
        refine ⟨64601063505523283491107785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172269502681395422642954093 64601063505523283491107785)
        ·
          refine ⟨48450797629142462618330839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64601063505523283491107785 48450797629142462618330839)
          ·
            refine ⟨72676196443713693927496259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48450797629142462618330839 72676196443713693927496259)
            ·
              refine ⟨109014294665570540891244389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72676196443713693927496259 109014294665570540891244389)
              ·
                refine ⟨20440180249794476417108323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109014294665570540891244389 20440180249794476417108323)
                ·
                  refine ⟨30660270374691714625662485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20440180249794476417108323 30660270374691714625662485)
                  ·
                    refine ⟨1437200173813674123077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30660270374691714625662485 1437200173813674123077929)
                    ·
                      refine ⟨1077900130360255592308447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437200173813674123077929 1077900130360255592308447)
                      ·
                        rfl

theorem cell23_2099203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_2099203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099203 prefixEnd_2099203 := by exact prefixLift 2099203
  have htrace : WordTrace (prefixWord ++ tailWord_2099203) baseStart_2099203 baseEnd_2099203 := by
    simpa [prefixWord, tailWord_2099203, baseEnd_2099203] using wordTrace_append hprefix tailTrace_2099203
  have hstable : (prefixWord ++ tailWord_2099203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099203).length < 2 ^ (prefixWord ++ tailWord_2099203).sum := by decide
  have hdescent : baseEnd_2099203 < baseStart_2099203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099204 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 5]
def baseStart_2099204 : Nat := 118140960795 + 2099204 * 2 ^ 59
def prefixEnd_2099204 : Nat := 4983230072969 + 3 ^ 40 * 2099204 * 2
def baseEnd_2099204 : Nat := 119766738204545565377327

theorem tailTrace_2099204 : CollatzResearch.WordTrace tailWord_2099204 prefixEnd_2099204 119766738204545565377327 := by
  unfold tailWord_2099204
  simp only [CollatzResearch.WordTrace]
  refine ⟨38282129943474949172716333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51042839924633265563621777 38282129943474949172716333)
  ·
    refine ⟨14355798728803105939768625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38282129943474949172716333 14355798728803105939768625)
    ·
      refine ⟨10766849046602329454826469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14355798728803105939768625 10766849046602329454826469)
      ·
        refine ⟨2018784196237936772779963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10766849046602329454826469 2018784196237936772779963)
        ·
          refine ⟨3028176294356905159169945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018784196237936772779963 3028176294356905159169945)
          ·
            refine ⟨2271132220767678869377459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3028176294356905159169945 2271132220767678869377459)
            ·
              refine ⟨3406698331151518304066189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271132220767678869377459 3406698331151518304066189)
              ·
                refine ⟨1277511874181819364024821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3406698331151518304066189 1277511874181819364024821)
                ·
                  refine ⟨119766738204545565377327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277511874181819364024821 119766738204545565377327)
                  ·
                    rfl

theorem cell23_2099204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_2099204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099204 prefixEnd_2099204 := by exact prefixLift 2099204
  have htrace : WordTrace (prefixWord ++ tailWord_2099204) baseStart_2099204 baseEnd_2099204 := by
    simpa [prefixWord, tailWord_2099204, baseEnd_2099204] using wordTrace_append hprefix tailTrace_2099204
  have hstable : (prefixWord ++ tailWord_2099204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099204).length < 2 ^ (prefixWord ++ tailWord_2099204).sum := by decide
  have hdescent : baseEnd_2099204 < baseStart_2099204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099216 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_2099216 : Nat := 118140960795 + 2099216 * 2 ^ 59
def prefixEnd_2099216 : Nat := 4983230072969 + 3 ^ 40 * 2099216 * 2
def baseEnd_2099216 : Nat := 1077906805608764041445887

theorem tailTrace_2099216 : CollatzResearch.WordTrace tailWord_2099216 prefixEnd_2099216 1077906805608764041445887 := by
  unfold tailWord_2099216
  simp only [CollatzResearch.WordTrace]
  refine ⟨38282348781453212197434751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51043131708604282929913001 38282348781453212197434751)
  ·
    refine ⟨57423523172179818296152127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38282348781453212197434751 57423523172179818296152127)
    ·
      refine ⟨86135284758269727444228191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57423523172179818296152127 86135284758269727444228191)
      ·
        refine ⟨129202927137404591166342287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86135284758269727444228191 129202927137404591166342287)
        ·
          refine ⟨193804390706106886749513431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129202927137404591166342287 193804390706106886749513431)
          ·
            refine ⟨290706586059160330124270147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193804390706106886749513431 290706586059160330124270147)
            ·
              refine ⟨436059879088740495186405221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290706586059160330124270147 436059879088740495186405221)
              ·
                refine ⟨81761227329138842847450979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436059879088740495186405221 81761227329138842847450979)
                ·
                  refine ⟨122641840993708264271176469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81761227329138842847450979 122641840993708264271176469)
                  ·
                    refine ⟨5748836296580074887711397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122641840993708264271176469 5748836296580074887711397)
                    ·
                      refine ⟨1077906805608764041445887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5748836296580074887711397 1077906805608764041445887)
                      ·
                        rfl

theorem cell23_2099216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_2099216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099216 prefixEnd_2099216 := by exact prefixLift 2099216
  have htrace : WordTrace (prefixWord ++ tailWord_2099216) baseStart_2099216 baseEnd_2099216 := by
    simpa [prefixWord, tailWord_2099216, baseEnd_2099216] using wordTrace_append hprefix tailTrace_2099216
  have hstable : (prefixWord ++ tailWord_2099216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099216).length < 2 ^ (prefixWord ++ tailWord_2099216).sum := by decide
  have hdescent : baseEnd_2099216 < baseStart_2099216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099253 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2099253 : Nat := 118140960795 + 2099253 * 2 ^ 59
def prefixEnd_2099253 : Nat := 4983230072969 + 3 ^ 40 * 2099253 * 2
def baseEnd_2099253 : Nat := 1077925804392980396683217

theorem tailTrace_2099253 : CollatzResearch.WordTrace tailWord_2099253 prefixEnd_2099253 1077925804392980396683217 := by
  unfold tailWord_2099253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76566047063772379713966413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51044031375848253142644275 76566047063772379713966413)
  ·
    refine ⟨28712267648914642392737405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76566047063772379713966413 28712267648914642392737405)
    ·
      refine ⟨10767100368342990897276527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28712267648914642392737405 10767100368342990897276527)
      ·
        refine ⟨16150650552514486345914791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10767100368342990897276527 16150650552514486345914791)
        ·
          refine ⟨24225975828771729518872187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16150650552514486345914791 24225975828771729518872187)
          ·
            refine ⟨36338963743157594278308281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24225975828771729518872187 36338963743157594278308281)
            ·
              refine ⟨27254222807368195708731211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36338963743157594278308281 27254222807368195708731211)
              ·
                refine ⟨40881334211052293563096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27254222807368195708731211 40881334211052293563096817)
                ·
                  refine ⟨30661000658289220172322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40881334211052293563096817 30661000658289220172322613)
                  ·
                    refine ⟨2874468811714614391155245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30661000658289220172322613 2874468811714614391155245)
                    ·
                      refine ⟨1077925804392980396683217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874468811714614391155245 1077925804392980396683217)
                      ·
                        rfl

theorem cell23_2099253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2099253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099253 prefixEnd_2099253 := by exact prefixLift 2099253
  have htrace : WordTrace (prefixWord ++ tailWord_2099253) baseStart_2099253 baseEnd_2099253 := by
    simpa [prefixWord, tailWord_2099253, baseEnd_2099253] using wordTrace_append hprefix tailTrace_2099253
  have hstable : (prefixWord ++ tailWord_2099253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099253).length < 2 ^ (prefixWord ++ tailWord_2099253).sum := by decide
  have hdescent : baseEnd_2099253 < baseStart_2099253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099257 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2099257 : Nat := 118140960795 + 2099257 * 2 ^ 59
def prefixEnd_2099257 : Nat := 4983230072969 + 3 ^ 40 * 2099257 * 2
def baseEnd_2099257 : Nat := 1077927858315598381033199

theorem tailTrace_2099257 : CollatzResearch.WordTrace tailWord_2099257 prefixEnd_2099257 1077927858315598381033199 := by
  unfold tailWord_2099257
  simp only [CollatzResearch.WordTrace]
  refine ⟨76566192955757888397112025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51044128637171925598074683 76566192955757888397112025)
  ·
    refine ⟨57424644716818416297834019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76566192955757888397112025 57424644716818416297834019)
    ·
      refine ⟨86136967075227624446751029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57424644716818416297834019 86136967075227624446751029)
      ·
        refine ⟨8075340663302589791882909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86136967075227624446751029 8075340663302589791882909)
        ·
          refine ⟨3028252748738471171956091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8075340663302589791882909 3028252748738471171956091)
          ·
            refine ⟨4542379123107706757934137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028252748738471171956091 4542379123107706757934137)
            ·
              refine ⟨3406784342330780068450603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542379123107706757934137 3406784342330780068450603)
              ·
                refine ⟨5110176513496170102675905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406784342330780068450603 5110176513496170102675905)
                ·
                  refine ⟨3832632385122127577006929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110176513496170102675905 3832632385122127577006929)
                  ·
                    refine ⟨2874474288841595682755197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832632385122127577006929 2874474288841595682755197)
                    ·
                      refine ⟨1077927858315598381033199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874474288841595682755197 1077927858315598381033199)
                      ·
                        rfl

theorem cell23_2099257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2099257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099257 prefixEnd_2099257 := by exact prefixLift 2099257
  have htrace : WordTrace (prefixWord ++ tailWord_2099257) baseStart_2099257 baseEnd_2099257 := by
    simpa [prefixWord, tailWord_2099257, baseEnd_2099257] using wordTrace_append hprefix tailTrace_2099257
  have hstable : (prefixWord ++ tailWord_2099257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099257).length < 2 ^ (prefixWord ++ tailWord_2099257).sum := by decide
  have hdescent : baseEnd_2099257 < baseStart_2099257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099310 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2099310 : Nat := 118140960795 + 2099310 * 2 ^ 59
def prefixEnd_2099310 : Nat := 4983230072969 + 3 ^ 40 * 2099310 * 2
def baseEnd_2099310 : Nat := 1077955072790286673670455

theorem tailTrace_2099310 : CollatzResearch.WordTrace tailWord_2099310 prefixEnd_2099310 1077955072790286673670455 := by
  unfold tailWord_2099310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571015753070734806098923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51045417349710585632527589 9571015753070734806098923)
  ·
    refine ⟨14356523629606102209148385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571015753070734806098923 14356523629606102209148385)
    ·
      refine ⟨10767392722204576656861289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14356523629606102209148385 10767392722204576656861289)
      ·
        refine ⟨8075544541653432492645967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10767392722204576656861289 8075544541653432492645967)
        ·
          refine ⟨12113316812480148738968951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075544541653432492645967 12113316812480148738968951)
          ·
            refine ⟨18169975218720223108453427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12113316812480148738968951 18169975218720223108453427)
            ·
              refine ⟨27254962828080334662680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18169975218720223108453427 27254962828080334662680141)
              ·
                refine ⟨10220611060530125498505053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27254962828080334662680141 10220611060530125498505053)
                ·
                  refine ⟨3832729147698797061939395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10220611060530125498505053 3832729147698797061939395)
                  ·
                    refine ⟨5749093721548195592909093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832729147698797061939395 5749093721548195592909093)
                    ·
                      refine ⟨1077955072790286673670455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5749093721548195592909093 1077955072790286673670455)
                      ·
                        rfl

theorem cell23_2099310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2099310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099310 prefixEnd_2099310 := by exact prefixLift 2099310
  have htrace : WordTrace (prefixWord ++ tailWord_2099310) baseStart_2099310 baseEnd_2099310 := by
    simpa [prefixWord, tailWord_2099310, baseEnd_2099310] using wordTrace_append hprefix tailTrace_2099310
  have hstable : (prefixWord ++ tailWord_2099310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099310).length < 2 ^ (prefixWord ++ tailWord_2099310).sum := by decide
  have hdescent : baseEnd_2099310 < baseStart_2099310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099314 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2099314 : Nat := 118140960795 + 2099314 * 2 ^ 59
def prefixEnd_2099314 : Nat := 4983230072969 + 3 ^ 40 * 2099314 * 2
def baseEnd_2099314 : Nat := 1077957126712904658020437

theorem tailTrace_2099314 : CollatzResearch.WordTrace tailWord_2099314 prefixEnd_2099314 1077957126712904658020437 := by
  unfold tailWord_2099314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142067979137846782984249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51045514611034258087957997 19142067979137846782984249)
  ·
    refine ⟨14356550984353385087238187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19142067979137846782984249 14356550984353385087238187)
    ·
      refine ⟨21534826476530077630857281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14356550984353385087238187 21534826476530077630857281)
      ·
        refine ⟨16151119857397558223142961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21534826476530077630857281 16151119857397558223142961)
        ·
          refine ⟨12113339893048168667357221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16151119857397558223142961 12113339893048168667357221)
          ·
            refine ⟨2271251229946531625129479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12113339893048168667357221 2271251229946531625129479)
            ·
              refine ⟨3406876844919797437694219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271251229946531625129479 3406876844919797437694219)
              ·
                refine ⟨5110315267379696156541329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406876844919797437694219 5110315267379696156541329)
                ·
                  refine ⟨3832736450534772117405997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110315267379696156541329 3832736450534772117405997)
                  ·
                    refine ⟨1437276168950539544027249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3832736450534772117405997 1437276168950539544027249)
                    ·
                      refine ⟨1077957126712904658020437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437276168950539544027249 1077957126712904658020437)
                      ·
                        rfl

theorem cell23_2099314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2099314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099314 prefixEnd_2099314 := by exact prefixLift 2099314
  have htrace : WordTrace (prefixWord ++ tailWord_2099314) baseStart_2099314 baseEnd_2099314 := by
    simpa [prefixWord, tailWord_2099314, baseEnd_2099314] using wordTrace_append hprefix tailTrace_2099314
  have hstable : (prefixWord ++ tailWord_2099314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099314).length < 2 ^ (prefixWord ++ tailWord_2099314).sum := by decide
  have hdescent : baseEnd_2099314 < baseStart_2099314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099333 : List Nat := [1, 3, 1, 1, 5, 2, 10]
def baseStart_2099333 : Nat := 118140960795 + 2099333 * 2 ^ 59
def prefixEnd_2099333 : Nat := 4983230072969 + 3 ^ 40 * 2099333 * 2
def baseEnd_2099333 : Nat := 13308233121547408440529

theorem tailTrace_2099333 : CollatzResearch.WordTrace tailWord_2099333 prefixEnd_2099333 13308233121547408440529 := by
  unfold tailWord_2099333
  simp only [CollatzResearch.WordTrace]
  refine ⟨76568964903482553376878653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51045976602321702251252435 76568964903482553376878653)
  ·
    refine ⟨28713361838805957516329495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76568964903482553376878653 28713361838805957516329495)
    ·
      refine ⟨43070042758208936274494243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28713361838805957516329495 43070042758208936274494243)
      ·
        refine ⟨64605064137313404411741365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43070042758208936274494243 64605064137313404411741365)
        ·
          refine ⟨6056724762873131663600753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64605064137313404411741365 6056724762873131663600753)
          ·
            refine ⟨4542543572154848747700565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6056724762873131663600753 4542543572154848747700565)
            ·
              refine ⟨13308233121547408440529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4542543572154848747700565 13308233121547408440529)
              ·
                rfl

theorem cell23_2099333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 10].length) (baseStart_2099333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099333 prefixEnd_2099333 := by exact prefixLift 2099333
  have htrace : WordTrace (prefixWord ++ tailWord_2099333) baseStart_2099333 baseEnd_2099333 := by
    simpa [prefixWord, tailWord_2099333, baseEnd_2099333] using wordTrace_append hprefix tailTrace_2099333
  have hstable : (prefixWord ++ tailWord_2099333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099333).length < 2 ^ (prefixWord ++ tailWord_2099333).sum := by decide
  have hdescent : baseEnd_2099333 < baseStart_2099333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099344 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 1, 2, 2]
def baseStart_2099344 : Nat := 118140960795 + 2099344 * 2 ^ 59
def prefixEnd_2099344 : Nat := 4983230072969 + 3 ^ 40 * 2099344 * 2
def baseEnd_2099344 : Nat := 1077972531132539540645299

theorem tailTrace_2099344 : CollatzResearch.WordTrace tailWord_2099344 prefixEnd_2099344 1077972531132539540645299 := by
  unfold tailWord_2099344
  simp only [CollatzResearch.WordTrace]
  refine ⟨38284683053221351127764543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51046244070961801503686057 38284683053221351127764543)
  ·
    refine ⟨57427024579832026691646815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38284683053221351127764543 57427024579832026691646815)
    ·
      refine ⟨86140536869748040037470223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57427024579832026691646815 86140536869748040037470223)
      ·
        refine ⟨129210805304622060056205335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86140536869748040037470223 129210805304622060056205335)
        ·
          refine ⟨193816207956933090084308003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129210805304622060056205335 193816207956933090084308003)
          ·
            refine ⟨290724311935399635126462005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193816207956933090084308003 290724311935399635126462005)
            ·
              refine ⟨27255404243943715793105813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290724311935399635126462005 27255404243943715793105813)
              ·
                refine ⟨1277597073934861677801835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27255404243943715793105813 1277597073934861677801835)
                ·
                  refine ⟨1916395610902292516702753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277597073934861677801835 1916395610902292516702753)
                  ·
                    refine ⟨1437296708176719387527065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916395610902292516702753 1437296708176719387527065)
                    ·
                      refine ⟨1077972531132539540645299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437296708176719387527065 1077972531132539540645299)
                      ·
                        rfl

theorem cell23_2099344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 2, 2].length) (baseStart_2099344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099344 prefixEnd_2099344 := by exact prefixLift 2099344
  have htrace : WordTrace (prefixWord ++ tailWord_2099344) baseStart_2099344 baseEnd_2099344 := by
    simpa [prefixWord, tailWord_2099344, baseEnd_2099344] using wordTrace_append hprefix tailTrace_2099344
  have hstable : (prefixWord ++ tailWord_2099344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099344).length < 2 ^ (prefixWord ++ tailWord_2099344).sum := by decide
  have hdescent : baseEnd_2099344 < baseStart_2099344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099354 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_2099354 : Nat := 118140960795 + 2099354 * 2 ^ 59
def prefixEnd_2099354 : Nat := 4983230072969 + 3 ^ 40 * 2099354 * 2
def baseEnd_2099354 : Nat := 359325888646361500506751

theorem tailTrace_2099354 : CollatzResearch.WordTrace tailWord_2099354 prefixEnd_2099354 359325888646361500506751 := by
  unfold tailWord_2099354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142432709101618490848279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51046487224270982642262077 19142432709101618490848279)
  ·
    refine ⟨28713649063652427736272419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19142432709101618490848279 28713649063652427736272419)
    ·
      refine ⟨43070473595478641604408629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28713649063652427736272419 43070473595478641604408629)
      ·
        refine ⟨4037856899576122650413309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43070473595478641604408629 4037856899576122650413309)
        ·
          refine ⟨1514196337341045993904991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4037856899576122650413309 1514196337341045993904991)
          ·
            refine ⟨2271294506011568990857487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514196337341045993904991 2271294506011568990857487)
            ·
              refine ⟨3406941759017353486286231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271294506011568990857487 3406941759017353486286231)
              ·
                refine ⟨5110412638526030229429347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406941759017353486286231 5110412638526030229429347)
                ·
                  refine ⟨7665618957789045344144021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110412638526030229429347 7665618957789045344144021)
                  ·
                    refine ⟨359325888646361500506751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7665618957789045344144021 359325888646361500506751)
                    ·
                      rfl

theorem cell23_2099354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_2099354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099354 prefixEnd_2099354 := by exact prefixLift 2099354
  have htrace : WordTrace (prefixWord ++ tailWord_2099354) baseStart_2099354 baseEnd_2099354 := by
    simpa [prefixWord, tailWord_2099354, baseEnd_2099354] using wordTrace_append hprefix tailTrace_2099354
  have hstable : (prefixWord ++ tailWord_2099354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099354).length < 2 ^ (prefixWord ++ tailWord_2099354).sum := by decide
  have hdescent : baseEnd_2099354 < baseStart_2099354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099357 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2099357 : Nat := 118140960795 + 2099357 * 2 ^ 59
def prefixEnd_2099357 : Nat := 4983230072969 + 3 ^ 40 * 2099357 * 2
def baseEnd_2099357 : Nat := 1077979206381047989782739

theorem tailTrace_2099357 : CollatzResearch.WordTrace tailWord_2099357 prefixEnd_2099357 1077979206381047989782739 := by
  unfold tailWord_2099357
  simp only [CollatzResearch.WordTrace]
  refine ⟨76569840255395605475752325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51046560170263736983834883 76569840255395605475752325)
  ·
    refine ⟨14356845047886676026703561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76569840255395605475752325 14356845047886676026703561)
    ·
      refine ⟨10767633785915007020027671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14356845047886676026703561 10767633785915007020027671)
      ·
        refine ⟨16151450678872510530041507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10767633785915007020027671 16151450678872510530041507)
        ·
          refine ⟨24227176018308765795062261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16151450678872510530041507 24227176018308765795062261)
          ·
            refine ⟨2271297751716446793287087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24227176018308765795062261 2271297751716446793287087)
            ·
              refine ⟨3406946627574670189930631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271297751716446793287087 3406946627574670189930631)
              ·
                refine ⟨5110419941362005284895947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406946627574670189930631 5110419941362005284895947)
                ·
                  refine ⟨7665629912043007927343921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110419941362005284895947 7665629912043007927343921)
                  ·
                    refine ⟨5749222434032255945507941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7665629912043007927343921 5749222434032255945507941)
                    ·
                      refine ⟨1077979206381047989782739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5749222434032255945507941 1077979206381047989782739)
                      ·
                        rfl

theorem cell23_2099357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2099357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099357 prefixEnd_2099357 := by exact prefixLift 2099357
  have htrace : WordTrace (prefixWord ++ tailWord_2099357) baseStart_2099357 baseEnd_2099357 := by
    simpa [prefixWord, tailWord_2099357, baseEnd_2099357] using wordTrace_append hprefix tailTrace_2099357
  have hstable : (prefixWord ++ tailWord_2099357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099357).length < 2 ^ (prefixWord ++ tailWord_2099357).sum := by decide
  have hdescent : baseEnd_2099357 < baseStart_2099357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099364 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_2099364 : Nat := 118140960795 + 2099364 * 2 ^ 59
def prefixEnd_2099364 : Nat := 4983230072969 + 3 ^ 40 * 2099364 * 2
def baseEnd_2099364 : Nat := 1077982800745629462395207

theorem tailTrace_2099364 : CollatzResearch.WordTrace tailWord_2099364 prefixEnd_2099364 1077982800745629462395207 := by
  unfold tailWord_2099364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38285047783185122835628573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51046730377580163780838097 38285047783185122835628573)
  ·
    refine ⟨14356892918694421063360715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38285047783185122835628573 14356892918694421063360715)
    ·
      refine ⟨21535339378041631595041073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14356892918694421063360715 21535339378041631595041073)
      ·
        refine ⟨16151504533531223696280805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21535339378041631595041073 16151504533531223696280805)
        ·
          refine ⟨3028407100037104443052651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16151504533531223696280805 3028407100037104443052651)
          ·
            refine ⟨4542610650055656664578977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028407100037104443052651 4542610650055656664578977)
            ·
              refine ⟨3406957987541742498434233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542610650055656664578977 3406957987541742498434233)
              ·
                refine ⟨2555218490656306873825675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406957987541742498434233 2555218490656306873825675)
                ·
                  refine ⟨3832827735984460310738513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555218490656306873825675 3832827735984460310738513)
                  ·
                    refine ⟨2874620801988345233053885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832827735984460310738513 2874620801988345233053885)
                    ·
                      refine ⟨1077982800745629462395207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2874620801988345233053885 1077982800745629462395207)
                      ·
                        rfl

theorem cell23_2099364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_2099364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099364 prefixEnd_2099364 := by exact prefixLift 2099364
  have htrace : WordTrace (prefixWord ++ tailWord_2099364) baseStart_2099364 baseEnd_2099364 := by
    simpa [prefixWord, tailWord_2099364, baseEnd_2099364] using wordTrace_append hprefix tailTrace_2099364
  have hstable : (prefixWord ++ tailWord_2099364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099364).length < 2 ^ (prefixWord ++ tailWord_2099364).sum := by decide
  have hdescent : baseEnd_2099364 < baseStart_2099364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099387 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 1, 3, 2]
def baseStart_2099387 : Nat := 118140960795 + 2099387 * 2 ^ 59
def prefixEnd_2099387 : Nat := 4983230072969 + 3 ^ 40 * 2099387 * 2
def baseEnd_2099387 : Nat := 1077994610800682872407601

theorem tailTrace_2099387 : CollatzResearch.WordTrace tailWord_2099387 prefixEnd_2099387 1077994610800682872407601 := by
  unfold tailWord_2099387
  simp only [CollatzResearch.WordTrace]
  refine ⟨76570934445286920599344415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51047289630191280399562943 76570934445286920599344415)
  ·
    refine ⟨114856401667930380899016623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76570934445286920599344415 114856401667930380899016623)
    ·
      refine ⟨172284602501895571348524935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114856401667930380899016623 172284602501895571348524935)
      ·
        refine ⟨258426903752843357022787403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172284602501895571348524935 258426903752843357022787403)
        ·
          refine ⟨387640355629265035534181105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258426903752843357022787403 387640355629265035534181105)
          ·
            refine ⟨290730266721948776650635829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387640355629265035534181105 290730266721948776650635829)
            ·
              refine ⟨27255962505182697810997109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290730266721948776650635829 27255962505182697810997109)
              ·
                refine ⟨2555246484860877919780979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27255962505182697810997109 2555246484860877919780979)
                ·
                  refine ⟨3832869727291316879671469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555246484860877919780979 3832869727291316879671469)
                  ·
                    refine ⟨1437326147734243829876801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3832869727291316879671469 1437326147734243829876801)
                    ·
                      refine ⟨1077994610800682872407601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437326147734243829876801 1077994610800682872407601)
                      ·
                        rfl

theorem cell23_2099387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3, 2].length) (baseStart_2099387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099387 prefixEnd_2099387 := by exact prefixLift 2099387
  have htrace : WordTrace (prefixWord ++ tailWord_2099387) baseStart_2099387 baseEnd_2099387 := by
    simpa [prefixWord, tailWord_2099387, baseEnd_2099387] using wordTrace_append hprefix tailTrace_2099387
  have hstable : (prefixWord ++ tailWord_2099387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099387).length < 2 ^ (prefixWord ++ tailWord_2099387).sum := by decide
  have hdescent : baseEnd_2099387 < baseStart_2099387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099403 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_2099403 : Nat := 118140960795 + 2099403 * 2 ^ 59
def prefixEnd_2099403 : Nat := 4983230072969 + 3 ^ 40 * 2099403 * 2
def baseEnd_2099403 : Nat := 1078002826491154809807527

theorem tailTrace_2099403 : CollatzResearch.WordTrace tailWord_2099403 prefixEnd_2099403 1078002826491154809807527 := by
  unfold tailWord_2099403
  simp only [CollatzResearch.WordTrace]
  refine ⟨76571518013228955331926863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51047678675485970221284575 76571518013228955331926863)
  ·
    refine ⟨114857277019843432997890295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76571518013228955331926863 114857277019843432997890295)
    ·
      refine ⟨172285915529765149496835443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114857277019843432997890295 172285915529765149496835443)
      ·
        refine ⟨258428873294647724245253165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172285915529765149496835443 258428873294647724245253165)
        ·
          refine ⟨96910827485492896591969937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258428873294647724245253165 96910827485492896591969937)
          ·
            refine ⟨72683120614119672443977453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96910827485492896591969937 72683120614119672443977453)
            ·
              refine ⟨27256170230294877166491545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72683120614119672443977453 27256170230294877166491545)
              ·
                refine ⟨20442127672721157874868659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27256170230294877166491545 20442127672721157874868659)
                ·
                  refine ⟨30663191509081736812302989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20442127672721157874868659 30663191509081736812302989)
                  ·
                    refine ⟨11498696815905651304613621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30663191509081736812302989 11498696815905651304613621)
                    ·
                      refine ⟨1078002826491154809807527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11498696815905651304613621 1078002826491154809807527)
                      ·
                        rfl

theorem cell23_2099403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_2099403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099403 prefixEnd_2099403 := by exact prefixLift 2099403
  have htrace : WordTrace (prefixWord ++ tailWord_2099403) baseStart_2099403 baseEnd_2099403 := by
    simpa [prefixWord, tailWord_2099403, baseEnd_2099403] using wordTrace_append hprefix tailTrace_2099403
  have hstable : (prefixWord ++ tailWord_2099403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099403).length < 2 ^ (prefixWord ++ tailWord_2099403).sum := by decide
  have hdescent : baseEnd_2099403 < baseStart_2099403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099421 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2099421 : Nat := 118140960795 + 2099421 * 2 ^ 59
def prefixEnd_2099421 : Nat := 4983230072969 + 3 ^ 40 * 2099421 * 2
def baseEnd_2099421 : Nat := 1078012069142935739382445

theorem tailTrace_2099421 : CollatzResearch.WordTrace tailWord_2099421 prefixEnd_2099421 1078012069142935739382445 := by
  unfold tailWord_2099421
  simp only [CollatzResearch.WordTrace]
  refine ⟨76572174527163744406082117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51048116351442496270721411 76572174527163744406082117)
  ·
    refine ⟨14357282723843202076140397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76572174527163744406082117 14357282723843202076140397)
    ·
      refine ⟨5383981021441200778552649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14357282723843202076140397 5383981021441200778552649)
      ·
        refine ⟨4037985766080900583914487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5383981021441200778552649 4037985766080900583914487)
        ·
          refine ⟨6056978649121350875871731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4037985766080900583914487 6056978649121350875871731)
          ·
            refine ⟨9085467973682026313807597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056978649121350875871731 9085467973682026313807597)
            ·
              refine ⟨3407050490130759867677849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9085467973682026313807597 3407050490130759867677849)
              ·
                refine ⟨2555287867598069900758387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407050490130759867677849 2555287867598069900758387)
                ·
                  refine ⟨3832931801397104851137581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555287867598069900758387 3832931801397104851137581)
                  ·
                    refine ⟨1437349425523914319176593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3832931801397104851137581 1437349425523914319176593)
                    ·
                      refine ⟨1078012069142935739382445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437349425523914319176593 1078012069142935739382445)
                      ·
                        rfl

theorem cell23_2099421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2099421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099421 prefixEnd_2099421 := by exact prefixLift 2099421
  have htrace : WordTrace (prefixWord ++ tailWord_2099421) baseStart_2099421 baseEnd_2099421 := by
    simpa [prefixWord, tailWord_2099421, baseEnd_2099421] using wordTrace_append hprefix tailTrace_2099421
  have hstable : (prefixWord ++ tailWord_2099421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099421).length < 2 ^ (prefixWord ++ tailWord_2099421).sum := by decide
  have hdescent : baseEnd_2099421 < baseStart_2099421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099423 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 9]
def baseStart_2099423 : Nat := 118140960795 + 2099423 * 2 ^ 59
def prefixEnd_2099423 : Nat := 4983230072969 + 3 ^ 40 * 2099423 * 2
def baseEnd_2099423 : Nat := 119779232900471636839715

theorem tailTrace_2099423 : CollatzResearch.WordTrace tailWord_2099423 prefixEnd_2099423 119779232900471636839715 := by
  unfold tailWord_2099423
  simp only [CollatzResearch.WordTrace]
  refine ⟨76572247473156498747654923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51048164982104332498436615 76572247473156498747654923)
  ·
    refine ⟨114858371209734748121482385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76572247473156498747654923 114858371209734748121482385)
    ·
      refine ⟨86143778407301061091111789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114858371209734748121482385 86143778407301061091111789)
      ·
        refine ⟨32303916902737897909166921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86143778407301061091111789 32303916902737897909166921)
        ·
          refine ⟨24227937677053423431875191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32303916902737897909166921 24227937677053423431875191)
          ·
            refine ⟨36341906515580135147812787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24227937677053423431875191 36341906515580135147812787)
            ·
              refine ⟨54512859773370202721719181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36341906515580135147812787 54512859773370202721719181)
              ·
                refine ⟨20442322415013826020644693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54512859773370202721719181 20442322415013826020644693)
                ·
                  refine ⟨119779232900471636839715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20442322415013826020644693 119779232900471636839715)
                  ·
                    rfl

theorem cell23_2099423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 9].length) (baseStart_2099423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099423 prefixEnd_2099423 := by exact prefixLift 2099423
  have htrace : WordTrace (prefixWord ++ tailWord_2099423) baseStart_2099423 baseEnd_2099423 := by
    simpa [prefixWord, tailWord_2099423, baseEnd_2099423] using wordTrace_append hprefix tailTrace_2099423
  have hstable : (prefixWord ++ tailWord_2099423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099423).length < 2 ^ (prefixWord ++ tailWord_2099423).sum := by decide
  have hdescent : baseEnd_2099423 < baseStart_2099423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099457 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 5]
def baseStart_2099457 : Nat := 118140960795 + 2099457 * 2 ^ 59
def prefixEnd_2099457 : Nat := 4983230072969 + 3 ^ 40 * 2099457 * 2
def baseEnd_2099457 : Nat := 119781172716277510948031

theorem tailTrace_2099457 : CollatzResearch.WordTrace tailWord_2099457 prefixEnd_2099457 119781172716277510948031 := by
  unfold tailWord_2099457
  simp only [CollatzResearch.WordTrace]
  refine ⟨76573487555033322554392625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51048991703355548369595083 76573487555033322554392625)
  ·
    refine ⟨57430115666274991915794469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76573487555033322554392625 57430115666274991915794469)
    ·
      refine ⟨10768146687426560984211463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57430115666274991915794469 10768146687426560984211463)
      ·
        refine ⟨16152220031139841476317195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10768146687426560984211463 16152220031139841476317195)
        ·
          refine ⟨24228330046709762214475793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16152220031139841476317195 24228330046709762214475793)
          ·
            refine ⟨18171247535032321660856845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24228330046709762214475793 18171247535032321660856845)
            ·
              refine ⟨6814217825637120622821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18171247535032321660856845 6814217825637120622821317)
              ·
                refine ⟨1277665842306960116778997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6814217825637120622821317 1277665842306960116778997)
                ·
                  refine ⟨119781172716277510948031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277665842306960116778997 119781172716277510948031)
                  ·
                    rfl

theorem cell23_2099457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 5].length) (baseStart_2099457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099457 prefixEnd_2099457 := by exact prefixLift 2099457
  have htrace : WordTrace (prefixWord ++ tailWord_2099457) baseStart_2099457 baseEnd_2099457 := by
    simpa [prefixWord, tailWord_2099457, baseEnd_2099457] using wordTrace_append hprefix tailTrace_2099457
  have hstable : (prefixWord ++ tailWord_2099457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099457).length < 2 ^ (prefixWord ++ tailWord_2099457).sum := by decide
  have hdescent : baseEnd_2099457 < baseStart_2099457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099470 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2099470 : Nat := 118140960795 + 2099470 * 2 ^ 59
def prefixEnd_2099470 : Nat := 4983230072969 + 3 ^ 40 * 2099470 * 2
def baseEnd_2099470 : Nat := 359345743231668682556573

theorem tailTrace_2099470 : CollatzResearch.WordTrace tailWord_2099470 prefixEnd_2099470 359345743231668682556573 := by
  unfold tailWord_2099470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571745212998278221826983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51049307802657483849743909 9571745212998278221826983)
  ·
    refine ⟨14357617819497417332740475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571745212998278221826983 14357617819497417332740475)
    ·
      refine ⟨21536426729246125999110713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14357617819497417332740475 21536426729246125999110713)
      ·
        refine ⟨16152320046934594499333035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21536426729246125999110713 16152320046934594499333035)
        ·
          refine ⟨24228480070401891748999553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16152320046934594499333035 24228480070401891748999553)
          ·
            refine ⟨18171360052801418811749665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24228480070401891748999553 18171360052801418811749665)
            ·
              refine ⟨13628520039601064108812249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18171360052801418811749665 13628520039601064108812249)
              ·
                refine ⟨10221390029700798081609187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13628520039601064108812249 10221390029700798081609187)
                ·
                  refine ⟨15332085044551197122413781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10221390029700798081609187 15332085044551197122413781)
                  ·
                    refine ⟨359345743231668682556573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15332085044551197122413781 359345743231668682556573)
                    ·
                      rfl

theorem cell23_2099470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2099470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099470 prefixEnd_2099470 := by exact prefixLift 2099470
  have htrace : WordTrace (prefixWord ++ tailWord_2099470) baseStart_2099470 baseEnd_2099470 := by
    simpa [prefixWord, tailWord_2099470, baseEnd_2099470] using wordTrace_append hprefix tailTrace_2099470
  have hstable : (prefixWord ++ tailWord_2099470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099470).length < 2 ^ (prefixWord ++ tailWord_2099470).sum := by decide
  have hdescent : baseEnd_2099470 < baseStart_2099470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099487 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 2, 5]
def baseStart_2099487 : Nat := 118140960795 + 2099487 * 2 ^ 59
def prefixEnd_2099487 : Nat := 4983230072969 + 3 ^ 40 * 2099487 * 2
def baseEnd_2099487 : Nat := 359348652955377493719047

theorem tailTrace_2099487 : CollatzResearch.WordTrace tailWord_2099487 prefixEnd_2099487 359348652955377493719047 := by
  unfold tailWord_2099487
  simp only [CollatzResearch.WordTrace]
  refine ⟨76574581744924637677984715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51049721163283091785323143 76574581744924637677984715)
  ·
    refine ⟨114861872617386956516977073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76574581744924637677984715 114861872617386956516977073)
    ·
      refine ⟨86146404463040217387732805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114861872617386956516977073 86146404463040217387732805)
      ·
        refine ⟨16152450836820040760199901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86146404463040217387732805 16152450836820040760199901)
        ·
          refine ⟨6057169063807515285074963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16152450836820040760199901 6057169063807515285074963)
          ·
            refine ⟨9085753595711272927612445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057169063807515285074963 9085753595711272927612445)
            ·
              refine ⟨3407157598391727347854667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9085753595711272927612445 3407157598391727347854667)
              ·
                refine ⟨5110736397587591021782001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407157598391727347854667 5110736397587591021782001)
                ·
                  refine ⟨3833052298190693266336501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110736397587591021782001 3833052298190693266336501)
                  ·
                    refine ⟨359348652955377493719047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3833052298190693266336501 359348652955377493719047)
                    ·
                      rfl

theorem cell23_2099487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_2099487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099487 prefixEnd_2099487 := by exact prefixLift 2099487
  have htrace : WordTrace (prefixWord ++ tailWord_2099487) baseStart_2099487 baseEnd_2099487 := by
    simpa [prefixWord, tailWord_2099487, baseEnd_2099487] using wordTrace_append hprefix tailTrace_2099487
  have hstable : (prefixWord ++ tailWord_2099487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099487).length < 2 ^ (prefixWord ++ tailWord_2099487).sum := by decide
  have hdescent : baseEnd_2099487 < baseStart_2099487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099502 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2099502 : Nat := 118140960795 + 2099502 * 2 ^ 59
def prefixEnd_2099502 : Nat := 4983230072969 + 3 ^ 40 * 2099502 * 2
def baseEnd_2099502 : Nat := 1078053661075949922469573

theorem tailTrace_2099502 : CollatzResearch.WordTrace tailWord_2099502 prefixEnd_2099502 1078053661075949922469573 := by
  unfold tailWord_2099502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571891104983786904972595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51050085893246863493187173 9571891104983786904972595)
  ·
    refine ⟨14357836657475680357458893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571891104983786904972595 14357836657475680357458893)
    ·
      refine ⟨5384188746553380134047085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14357836657475680357458893 5384188746553380134047085)
      ·
        refine ⟨2019070779957517550267657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5384188746553380134047085 2019070779957517550267657)
        ·
          refine ⟨1514303084968138162700743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019070779957517550267657 1514303084968138162700743)
          ·
            refine ⟨2271454627452207244051115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514303084968138162700743 2271454627452207244051115)
            ·
              refine ⟨3407181941178310866076673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271454627452207244051115 3407181941178310866076673)
              ·
                refine ⟨2555386455883733149557505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407181941178310866076673 2555386455883733149557505)
                ·
                  refine ⟨1916539841912799862168129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555386455883733149557505 1916539841912799862168129)
                  ·
                    refine ⟨1437404881434599896626097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916539841912799862168129 1437404881434599896626097)
                    ·
                      refine ⟨1078053661075949922469573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437404881434599896626097 1078053661075949922469573)
                      ·
                        rfl

theorem cell23_2099502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2099502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099502 prefixEnd_2099502 := by exact prefixLift 2099502
  have htrace : WordTrace (prefixWord ++ tailWord_2099502) baseStart_2099502 baseEnd_2099502 := by
    simpa [prefixWord, tailWord_2099502, baseEnd_2099502] using wordTrace_append hprefix tailTrace_2099502
  have hstable : (prefixWord ++ tailWord_2099502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099502).length < 2 ^ (prefixWord ++ tailWord_2099502).sum := by decide
  have hdescent : baseEnd_2099502 < baseStart_2099502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099507 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 4, 2]
def baseStart_2099507 : Nat := 118140960795 + 2099507 * 2 ^ 59
def prefixEnd_2099507 : Nat := 4983230072969 + 3 ^ 40 * 2099507 * 2
def baseEnd_2099507 : Nat := 1078056228479222402907049

theorem tailTrace_2099507 : CollatzResearch.WordTrace tailWord_2099507 prefixEnd_2099507 1078056228479222402907049 := by
  unfold tailWord_2099507
  simp only [CollatzResearch.WordTrace]
  refine ⟨76575311204852181093712775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51050207469901454062475183 76575311204852181093712775)
  ·
    refine ⟨114862966807278271640569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76575311204852181093712775 114862966807278271640569163)
    ·
      refine ⟨172294450210917407460853745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114862966807278271640569163 172294450210917407460853745)
      ·
        refine ⟨129220837658188055595640309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172294450210917407460853745 129220837658188055595640309)
        ·
          refine ⟨12114453530455130212091279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129220837658188055595640309 12114453530455130212091279)
          ·
            refine ⟨18171680295682695318136919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12114453530455130212091279 18171680295682695318136919)
            ·
              refine ⟨27257520443524042977205379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18171680295682695318136919 27257520443524042977205379)
              ·
                refine ⟨40886280665286064465808069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27257520443524042977205379 40886280665286064465808069)
                ·
                  refine ⟨7666177624741137087339013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40886280665286064465808069 7666177624741137087339013)
                  ·
                    refine ⟨1437408304638963203876065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7666177624741137087339013 1437408304638963203876065)
                    ·
                      refine ⟨1078056228479222402907049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437408304638963203876065 1078056228479222402907049)
                      ·
                        rfl

theorem cell23_2099507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4, 2].length) (baseStart_2099507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099507 prefixEnd_2099507 := by exact prefixLift 2099507
  have htrace : WordTrace (prefixWord ++ tailWord_2099507) baseStart_2099507 baseEnd_2099507 := by
    simpa [prefixWord, tailWord_2099507, baseEnd_2099507] using wordTrace_append hprefix tailTrace_2099507
  have hstable : (prefixWord ++ tailWord_2099507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099507).length < 2 ^ (prefixWord ++ tailWord_2099507).sum := by decide
  have hdescent : baseEnd_2099507 < baseStart_2099507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099567 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 5, 2]
def baseStart_2099567 : Nat := 118140960795 + 2099567 * 2 ^ 59
def prefixEnd_2099567 : Nat := 4983230072969 + 3 ^ 40 * 2099567 * 2
def baseEnd_2099567 : Nat := 1078087037318492168156773

theorem tailTrace_2099567 : CollatzResearch.WordTrace tailWord_2099567 prefixEnd_2099567 1078087037318492168156773 := by
  unfold tailWord_2099567
  simp only [CollatzResearch.WordTrace]
  refine ⟨76577499584634811340896955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51051666389756540893931303 76577499584634811340896955)
  ·
    refine ⟨114866249376952217011345433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76577499584634811340896955 114866249376952217011345433)
    ·
      refine ⟨86149687032714162758509075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114866249376952217011345433 86149687032714162758509075)
      ·
        refine ⟨129224530549071244137763613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86149687032714162758509075 129224530549071244137763613)
        ·
          refine ⟨48459198955901716551661355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129224530549071244137763613 48459198955901716551661355)
          ·
            refine ⟨72688798433852574827492033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48459198955901716551661355 72688798433852574827492033)
            ·
              refine ⟨54516598825389431120619025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72688798433852574827492033 54516598825389431120619025)
              ·
                refine ⟨40887449119042073340464269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54516598825389431120619025 40887449119042073340464269)
                ·
                  refine ⟨15332793419640777502674101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40887449119042073340464269 15332793419640777502674101)
                  ·
                    refine ⟨1437449383091322890875697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15332793419640777502674101 1437449383091322890875697)
                    ·
                      refine ⟨1078087037318492168156773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437449383091322890875697 1078087037318492168156773)
                      ·
                        rfl

theorem cell23_2099567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5, 2].length) (baseStart_2099567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099567 prefixEnd_2099567 := by exact prefixLift 2099567
  have htrace : WordTrace (prefixWord ++ tailWord_2099567) baseStart_2099567 baseEnd_2099567 := by
    simpa [prefixWord, tailWord_2099567, baseEnd_2099567] using wordTrace_append hprefix tailTrace_2099567
  have hstable : (prefixWord ++ tailWord_2099567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099567).length < 2 ^ (prefixWord ++ tailWord_2099567).sum := by decide
  have hdescent : baseEnd_2099567 < baseStart_2099567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099607 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 6, 4]
def baseStart_2099607 : Nat := 118140960795 + 2099607 * 2 ^ 59
def prefixEnd_2099607 : Nat := 4983230072969 + 3 ^ 40 * 2099607 * 2
def baseEnd_2099607 : Nat := 359369192181557337218863

theorem tailTrace_2099607 : CollatzResearch.WordTrace tailWord_2099607 prefixEnd_2099607 359369192181557337218863 := by
  unfold tailWord_2099607
  simp only [CollatzResearch.WordTrace]
  refine ⟨76578958504489898172353075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51052639002993265448235383 76578958504489898172353075)
  ·
    refine ⟨114868437756734847258529613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76578958504489898172353075 114868437756734847258529613)
    ·
      refine ⟨43075664158775567721948605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114868437756734847258529613 43075664158775567721948605)
      ·
        refine ⟨16153374059540837895730727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43075664158775567721948605 16153374059540837895730727)
        ·
          refine ⟨24230061089311256843596091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16153374059540837895730727 24230061089311256843596091)
          ·
            refine ⟨36345091633966885265394137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24230061089311256843596091 36345091633966885265394137)
            ·
              refine ⟨27258818725475163949045603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36345091633966885265394137 27258818725475163949045603)
              ·
                refine ⟨40888228088212745923568405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27258818725475163949045603 40888228088212745923568405)
                ·
                  refine ⟨1916635691634972465167269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40888228088212745923568405 1916635691634972465167269)
                  ·
                    refine ⟨359369192181557337218863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916635691634972465167269 359369192181557337218863)
                    ·
                      rfl

theorem cell23_2099607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_2099607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099607 prefixEnd_2099607 := by exact prefixLift 2099607
  have htrace : WordTrace (prefixWord ++ tailWord_2099607) baseStart_2099607 baseEnd_2099607 := by
    simpa [prefixWord, tailWord_2099607, baseEnd_2099607] using wordTrace_append hprefix tailTrace_2099607
  have hstable : (prefixWord ++ tailWord_2099607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099607).length < 2 ^ (prefixWord ++ tailWord_2099607).sum := by decide
  have hdescent : baseEnd_2099607 < baseStart_2099607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099644 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2099644 : Nat := 118140960795 + 2099644 * 2 ^ 59
def prefixEnd_2099644 : Nat := 4983230072969 + 3 ^ 40 * 2099644 * 2
def baseEnd_2099644 : Nat := 1078126575328888366893919

theorem tailTrace_2099644 : CollatzResearch.WordTrace tailWord_2099644 prefixEnd_2099644 1078126575328888366893919 := by
  unfold tailWord_2099644
  simp only [CollatzResearch.WordTrace]
  refine ⟨38290154002677926745724993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51053538670237235660966657 38290154002677926745724993)
  ·
    refine ⟨28717615502008445059293745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38290154002677926745724993 28717615502008445059293745)
    ·
      refine ⟨21538211626506333794470309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28717615502008445059293745 21538211626506333794470309)
      ·
        refine ⟨4038414679969937586463183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21538211626506333794470309 4038414679969937586463183)
        ·
          refine ⟨6057622019954906379694775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038414679969937586463183 6057622019954906379694775)
          ·
            refine ⟨9086433029932359569542163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057622019954906379694775 9086433029932359569542163)
            ·
              refine ⟨13629649544898539354313245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9086433029932359569542163 13629649544898539354313245)
              ·
                refine ⟨5111118579336952257867467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13629649544898539354313245 5111118579336952257867467)
                ·
                  refine ⟨7666677869005428386801201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5111118579336952257867467 7666677869005428386801201)
                  ·
                    refine ⟨5750008401754071290100901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7666677869005428386801201 5750008401754071290100901)
                    ·
                      refine ⟨1078126575328888366893919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5750008401754071290100901 1078126575328888366893919)
                      ·
                        rfl

theorem cell23_2099644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2099644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099644 prefixEnd_2099644 := by exact prefixLift 2099644
  have htrace : WordTrace (prefixWord ++ tailWord_2099644) baseStart_2099644 baseEnd_2099644 := by
    simpa [prefixWord, tailWord_2099644, baseEnd_2099644] using wordTrace_append hprefix tailTrace_2099644
  have hstable : (prefixWord ++ tailWord_2099644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099644).length < 2 ^ (prefixWord ++ tailWord_2099644).sum := by decide
  have hdescent : baseEnd_2099644 < baseStart_2099644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099668 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2099668 : Nat := 118140960795 + 2099668 * 2 ^ 59
def prefixEnd_2099668 : Nat := 4983230072969 + 3 ^ 40 * 2099668 * 2
def baseEnd_2099668 : Nat := 1078138898864596272993809

theorem tailTrace_2099668 : CollatzResearch.WordTrace tailWord_2099668 prefixEnd_2099668 1078138898864596272993809 := by
  unfold tailWord_2099668
  simp only [CollatzResearch.WordTrace]
  refine ⟨38290591678634452795161829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51054122238179270393549105 38290591678634452795161829)
  ·
    refine ⟨7179485939743959899092843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38290591678634452795161829 7179485939743959899092843)
    ·
      refine ⟨10769228909615939848639265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7179485939743959899092843 10769228909615939848639265)
      ·
        refine ⟨8076921682211954886479449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10769228909615939848639265 8076921682211954886479449)
        ·
          refine ⟨6057691261658966164859587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8076921682211954886479449 6057691261658966164859587)
          ·
            refine ⟨9086536892488449247289381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057691261658966164859587 9086536892488449247289381)
            ·
              refine ⟨1703725667341584233866759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9086536892488449247289381 1703725667341584233866759)
              ·
                refine ⟨2555588501012376350800139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703725667341584233866759 2555588501012376350800139)
                ·
                  refine ⟨3833382751518564526200209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555588501012376350800139 3833382751518564526200209)
                  ·
                    refine ⟨2875037063638923394650157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833382751518564526200209 2875037063638923394650157)
                    ·
                      refine ⟨1078138898864596272993809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875037063638923394650157 1078138898864596272993809)
                      ·
                        rfl

theorem cell23_2099668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2099668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099668 prefixEnd_2099668 := by exact prefixLift 2099668
  have htrace : WordTrace (prefixWord ++ tailWord_2099668) baseStart_2099668 baseEnd_2099668 := by
    simpa [prefixWord, tailWord_2099668, baseEnd_2099668] using wordTrace_append hprefix tailTrace_2099668
  have hstable : (prefixWord ++ tailWord_2099668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099668).length < 2 ^ (prefixWord ++ tailWord_2099668).sum := by decide
  have hdescent : baseEnd_2099668 < baseStart_2099668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099682 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2099682 : Nat := 118140960795 + 2099682 * 2 ^ 59
def prefixEnd_2099682 : Nat := 4983230072969 + 3 ^ 40 * 2099682 * 2
def baseEnd_2099682 : Nat := 1078146087593759218218745

theorem tailTrace_2099682 : CollatzResearch.WordTrace tailWord_2099682 prefixEnd_2099682 1078146087593759218218745 := by
  unfold tailWord_2099682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19145423494804546495333325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51054462652812123987555533 19145423494804546495333325)
  ·
    refine ⟨7179533810551704935749997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19145423494804546495333325 7179533810551704935749997)
    ·
      refine ⟨2692325178956889350906249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7179533810551704935749997 2692325178956889350906249)
      ·
        refine ⟨2019243884217667013179687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2692325178956889350906249 2019243884217667013179687)
        ·
          refine ⟨3028865826326500519769531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019243884217667013179687 3028865826326500519769531)
          ·
            refine ⟨4543298739489750779654297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028865826326500519769531 4543298739489750779654297)
            ·
              refine ⟨3407474054617313084740723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4543298739489750779654297 3407474054617313084740723)
              ·
                refine ⟨5111211081925969627111085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407474054617313084740723 5111211081925969627111085)
                ·
                  refine ⟨1916704155722238610166657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5111211081925969627111085 1916704155722238610166657)
                  ·
                    refine ⟨1437528116791678957624993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916704155722238610166657 1437528116791678957624993)
                    ·
                      refine ⟨1078146087593759218218745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437528116791678957624993 1078146087593759218218745)
                      ·
                        rfl

theorem cell23_2099682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2099682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099682 prefixEnd_2099682 := by exact prefixLift 2099682
  have htrace : WordTrace (prefixWord ++ tailWord_2099682) baseStart_2099682 baseEnd_2099682 := by
    simpa [prefixWord, tailWord_2099682, baseEnd_2099682] using wordTrace_append hprefix tailTrace_2099682
  have hstable : (prefixWord ++ tailWord_2099682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099682).length < 2 ^ (prefixWord ++ tailWord_2099682).sum := by decide
  have hdescent : baseEnd_2099682 < baseStart_2099682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099697 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2099697 : Nat := 118140960795 + 2099697 * 2 ^ 59
def prefixEnd_2099697 : Nat := 4983230072969 + 3 ^ 40 * 2099697 * 2
def baseEnd_2099697 : Nat := 359384596601192219843725

theorem tailTrace_2099697 : CollatzResearch.WordTrace tailWord_2099697 prefixEnd_2099697 359384596601192219843725 := by
  unfold tailWord_2099697
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582241074163843543129345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51054827382775895695419563 76582241074163843543129345)
  ·
    refine ⟨57436680805622882657347009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76582241074163843543129345 57436680805622882657347009)
    ·
      refine ⟨43077510604217161993010257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57436680805622882657347009 43077510604217161993010257)
      ·
        refine ⟨32308132953162871494757693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43077510604217161993010257 32308132953162871494757693)
        ·
          refine ⟨12115549857436076810534135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32308132953162871494757693 12115549857436076810534135)
          ·
            refine ⟨18173324786154115215801203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12115549857436076810534135 18173324786154115215801203)
            ·
              refine ⟨27259987179231172823701805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18173324786154115215801203 27259987179231172823701805)
              ·
                refine ⟨10222495192211689808888177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27259987179231172823701805 10222495192211689808888177)
                ·
                  refine ⟨7666871394158767356666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10222495192211689808888177 7666871394158767356666133)
                  ·
                    refine ⟨359384596601192219843725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7666871394158767356666133 359384596601192219843725)
                    ·
                      rfl

theorem cell23_2099697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2099697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099697 prefixEnd_2099697 := by exact prefixLift 2099697
  have htrace : WordTrace (prefixWord ++ tailWord_2099697) baseStart_2099697 baseEnd_2099697 := by
    simpa [prefixWord, tailWord_2099697, baseEnd_2099697] using wordTrace_append hprefix tailTrace_2099697
  have hstable : (prefixWord ++ tailWord_2099697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099697).length < 2 ^ (prefixWord ++ tailWord_2099697).sum := by decide
  have hdescent : baseEnd_2099697 < baseStart_2099697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099698 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2099698 : Nat := 118140960795 + 2099698 * 2 ^ 59
def prefixEnd_2099698 : Nat := 4983230072969 + 3 ^ 40 * 2099698 * 2
def baseEnd_2099698 : Nat := 1078154303284231155618671

theorem tailTrace_2099698 : CollatzResearch.WordTrace tailWord_2099698 prefixEnd_2099698 1078154303284231155618671 := by
  unfold tailWord_2099698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19145569386790055178478937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51054851698106813809277165 19145569386790055178478937)
  ·
    refine ⟨14359177040092541383859203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19145569386790055178478937 14359177040092541383859203)
    ·
      refine ⟨21538765560138812075788805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14359177040092541383859203 21538765560138812075788805)
      ·
        refine ⟨4038518542526027264210401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21538765560138812075788805 4038518542526027264210401)
        ·
          refine ⟨3028888906894520448157801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4038518542526027264210401 3028888906894520448157801)
          ·
            refine ⟨2271666680170890336118351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3028888906894520448157801 2271666680170890336118351)
            ·
              refine ⟨3407500020256335504177527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271666680170890336118351 3407500020256335504177527)
              ·
                refine ⟨5111250030384503256266291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407500020256335504177527 5111250030384503256266291)
                ·
                  refine ⟨7666875045576754884399437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5111250030384503256266291 7666875045576754884399437)
                  ·
                    refine ⟨2875078142091283081649789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7666875045576754884399437 2875078142091283081649789)
                    ·
                      refine ⟨1078154303284231155618671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875078142091283081649789 1078154303284231155618671)
                      ·
                        rfl

theorem cell23_2099698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2099698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099698 prefixEnd_2099698 := by exact prefixLift 2099698
  have htrace : WordTrace (prefixWord ++ tailWord_2099698) baseStart_2099698 baseEnd_2099698 := by
    simpa [prefixWord, tailWord_2099698, baseEnd_2099698] using wordTrace_append hprefix tailTrace_2099698
  have hstable : (prefixWord ++ tailWord_2099698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099698).length < 2 ^ (prefixWord ++ tailWord_2099698).sum := by decide
  have hdescent : baseEnd_2099698 < baseStart_2099698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099717 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_2099717 : Nat := 118140960795 + 2099717 * 2 ^ 59
def prefixEnd_2099717 : Nat := 4983230072969 + 3 ^ 40 * 2099717 * 2
def baseEnd_2099717 : Nat := 1078164059416666581281083

theorem tailTrace_2099717 : CollatzResearch.WordTrace tailWord_2099717 prefixEnd_2099717 1078164059416666581281083 := by
  unfold tailWord_2099717
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582970534091386958857405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51055313689394257972571603 76582970534091386958857405)
  ·
    refine ⟨28718613950284270109571527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76582970534091386958857405 28718613950284270109571527)
    ·
      refine ⟨43077920925426405164357291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28718613950284270109571527 43077920925426405164357291)
      ·
        refine ⟨64616881388139607746535937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43077920925426405164357291 64616881388139607746535937)
        ·
          refine ⟨48462661041104705809901953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64616881388139607746535937 48462661041104705809901953)
          ·
            refine ⟨36346995780828529357426465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48462661041104705809901953 36346995780828529357426465)
            ·
              refine ⟨27260246835621397018069849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36346995780828529357426465 27260246835621397018069849)
              ·
                refine ⟨20445185126716047763552387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27260246835621397018069849 20445185126716047763552387)
                ·
                  refine ⟨30667777690074071645328581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20445185126716047763552387 30667777690074071645328581)
                  ·
                    refine ⟨5750208316888888433499109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30667777690074071645328581 5750208316888888433499109)
                    ·
                      refine ⟨1078164059416666581281083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5750208316888888433499109 1078164059416666581281083)
                      ·
                        rfl

theorem cell23_2099717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_2099717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099717 prefixEnd_2099717 := by exact prefixLift 2099717
  have htrace : WordTrace (prefixWord ++ tailWord_2099717) baseStart_2099717 baseEnd_2099717 := by
    simpa [prefixWord, tailWord_2099717, baseEnd_2099717] using wordTrace_append hprefix tailTrace_2099717
  have hstable : (prefixWord ++ tailWord_2099717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099717).length < 2 ^ (prefixWord ++ tailWord_2099717).sum := by decide
  have hdescent : baseEnd_2099717 < baseStart_2099717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099724 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2099724 : Nat := 118140960795 + 2099724 * 2 ^ 59
def prefixEnd_2099724 : Nat := 4983230072969 + 3 ^ 40 * 2099724 * 2
def baseEnd_2099724 : Nat := 1078167653781248053893551

theorem tailTrace_2099724 : CollatzResearch.WordTrace tailWord_2099724 prefixEnd_2099724 1078167653781248053893551 := by
  unfold tailWord_2099724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38291612922533013577181113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51055483896710684769574817 38291612922533013577181113)
  ·
    refine ⟨28718709691899760182885835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38291612922533013577181113 28718709691899760182885835)
    ·
      refine ⟨43078064537849640274328753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28718709691899760182885835 43078064537849640274328753)
      ·
        refine ⟨32308548403387230205746565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43078064537849640274328753 32308548403387230205746565)
        ·
          refine ⟨6057852825635105663577481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32308548403387230205746565 6057852825635105663577481)
          ·
            refine ⟨4543389619226329247683111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6057852825635105663577481 4543389619226329247683111)
            ·
              refine ⟨6815084428839493871524667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543389619226329247683111 6815084428839493871524667)
              ·
                refine ⟨10222626643259240807287001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6815084428839493871524667 10222626643259240807287001)
                ·
                  refine ⟨7666969982444430605465251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10222626643259240807287001 7666969982444430605465251)
                  ·
                    refine ⟨11500454973666645908197877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7666969982444430605465251 11500454973666645908197877)
                    ·
                      refine ⟨1078167653781248053893551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11500454973666645908197877 1078167653781248053893551)
                      ·
                        rfl

theorem cell23_2099724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2099724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099724 prefixEnd_2099724 := by exact prefixLift 2099724
  have htrace : WordTrace (prefixWord ++ tailWord_2099724) baseStart_2099724 baseEnd_2099724 := by
    simpa [prefixWord, tailWord_2099724, baseEnd_2099724] using wordTrace_append hprefix tailTrace_2099724
  have hstable : (prefixWord ++ tailWord_2099724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099724).length < 2 ^ (prefixWord ++ tailWord_2099724).sum := by decide
  have hdescent : baseEnd_2099724 < baseStart_2099724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099767 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2099767 : Nat := 118140960795 + 2099767 * 2 ^ 59
def prefixEnd_2099767 : Nat := 4983230072969 + 3 ^ 40 * 2099767 * 2
def baseEnd_2099767 : Nat := 1078189733449391385655853

theorem tailTrace_2099767 : CollatzResearch.WordTrace tailWord_2099767 prefixEnd_2099767 1078189733449391385655853 := by
  unfold tailWord_2099767
  simp only [CollatzResearch.WordTrace]
  refine ⟨76584794183910245498177555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51056529455940163665451703 76584794183910245498177555)
  ·
    refine ⟨114877191275865368247266333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76584794183910245498177555 114877191275865368247266333)
    ·
      refine ⟨43078946728449513092724875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114877191275865368247266333 43078946728449513092724875)
      ·
        refine ⟨64618420092674269639087313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43078946728449513092724875 64618420092674269639087313)
        ·
          refine ⟨48463815069505702229315485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64618420092674269639087313 48463815069505702229315485)
          ·
            refine ⟨18173930651064638335993307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48463815069505702229315485 18173930651064638335993307)
            ·
              refine ⟨27260895976596957503989961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18173930651064638335993307 27260895976596957503989961)
              ·
                refine ⟨20445671982447718127992471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27260895976596957503989961 20445671982447718127992471)
                ·
                  refine ⟨30668507973671577191988707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20445671982447718127992471 30668507973671577191988707)
                  ·
                    refine ⟨46002761960507365787983061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30668507973671577191988707 46002761960507365787983061)
                    ·
                      refine ⟨1078189733449391385655853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46002761960507365787983061 1078189733449391385655853)
                      ·
                        rfl

theorem cell23_2099767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2099767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099767 prefixEnd_2099767 := by exact prefixLift 2099767
  have htrace : WordTrace (prefixWord ++ tailWord_2099767) baseStart_2099767 baseEnd_2099767 := by
    simpa [prefixWord, tailWord_2099767, baseEnd_2099767] using wordTrace_append hprefix tailTrace_2099767
  have hstable : (prefixWord ++ tailWord_2099767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099767).length < 2 ^ (prefixWord ++ tailWord_2099767).sum := by decide
  have hdescent : baseEnd_2099767 < baseStart_2099767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099811 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 4, 2]
def baseStart_2099811 : Nat := 118140960795 + 2099811 * 2 ^ 59
def prefixEnd_2099811 : Nat := 4983230072969 + 3 ^ 40 * 2099811 * 2
def baseEnd_2099811 : Nat := 1078212326598189213505651

theorem tailTrace_2099811 : CollatzResearch.WordTrace tailWord_2099811 prefixEnd_2099811 1078212326598189213505651 := by
  unfold tailWord_2099811
  simp only [CollatzResearch.WordTrace]
  refine ⟨76586398995750841012779287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51057599330500560675186191 76586398995750841012779287)
  ·
    refine ⟨114879598493626261519168931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76586398995750841012779287 114879598493626261519168931)
    ·
      refine ⟨172319397740439392278753397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114879598493626261519168931 172319397740439392278753397)
      ·
        refine ⟨16154943538166193026133131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172319397740439392278753397 16154943538166193026133131)
        ·
          refine ⟨24232415307249289539199697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16154943538166193026133131 24232415307249289539199697)
          ·
            refine ⟨18174311480436967154399773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24232415307249289539199697 18174311480436967154399773)
            ·
              refine ⟨6815366805163862682899915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18174311480436967154399773 6815366805163862682899915)
              ·
                refine ⟨10223050207745794024349873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6815366805163862682899915 10223050207745794024349873)
                ·
                  refine ⟨7667287655809345518262405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10223050207745794024349873 7667287655809345518262405)
                  ·
                    refine ⟨1437616435464252284674201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7667287655809345518262405 1437616435464252284674201)
                    ·
                      refine ⟨1078212326598189213505651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437616435464252284674201 1078212326598189213505651)
                      ·
                        rfl

theorem cell23_2099811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_2099811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099811 prefixEnd_2099811 := by exact prefixLift 2099811
  have htrace : WordTrace (prefixWord ++ tailWord_2099811) baseStart_2099811 baseEnd_2099811 := by
    simpa [prefixWord, tailWord_2099811, baseEnd_2099811] using wordTrace_append hprefix tailTrace_2099811
  have hstable : (prefixWord ++ tailWord_2099811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099811).length < 2 ^ (prefixWord ++ tailWord_2099811).sum := by decide
  have hdescent : baseEnd_2099811 < baseStart_2099811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099817 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 10]
def baseStart_2099817 : Nat := 118140960795 + 2099817 * 2 ^ 59
def prefixEnd_2099817 : Nat := 4983230072969 + 3 ^ 40 * 2099817 * 2
def baseEnd_2099817 : Nat := 119801711942457354447847

theorem tailTrace_2099817 : CollatzResearch.WordTrace tailWord_2099817 prefixEnd_2099817 119801711942457354447847 := by
  unfold tailWord_2099817
  simp only [CollatzResearch.WordTrace]
  refine ⟨76586617833729104037497705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51057745222486069358331803 76586617833729104037497705)
  ·
    refine ⟨57439963375296828028123279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76586617833729104037497705 57439963375296828028123279)
    ·
      refine ⟨86159945062945242042184919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57439963375296828028123279 86159945062945242042184919)
      ·
        refine ⟨129239917594417863063277379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86159945062945242042184919 129239917594417863063277379)
        ·
          refine ⟨193859876391626794594916069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129239917594417863063277379 193859876391626794594916069)
          ·
            refine ⟨36348726823430023986546763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193859876391626794594916069 36348726823430023986546763)
            ·
              refine ⟨54523090235145035979820145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36348726823430023986546763 54523090235145035979820145)
              ·
                refine ⟨40892317676358776984865109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54523090235145035979820145 40892317676358776984865109)
                ·
                  refine ⟨119801711942457354447847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40892317676358776984865109 119801711942457354447847)
                  ·
                    rfl

theorem cell23_2099817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_2099817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099817 prefixEnd_2099817 := by exact prefixLift 2099817
  have htrace : WordTrace (prefixWord ++ tailWord_2099817) baseStart_2099817 baseEnd_2099817 := by
    simpa [prefixWord, tailWord_2099817, baseEnd_2099817] using wordTrace_append hprefix tailTrace_2099817
  have hstable : (prefixWord ++ tailWord_2099817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099817).length < 2 ^ (prefixWord ++ tailWord_2099817).sum := by decide
  have hdescent : baseEnd_2099817 < baseStart_2099817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099821 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2099821 : Nat := 118140960795 + 2099821 * 2 ^ 59
def prefixEnd_2099821 : Nat := 4983230072969 + 3 ^ 40 * 2099821 * 2
def baseEnd_2099821 : Nat := 359405820468244724793535

theorem tailTrace_2099821 : CollatzResearch.WordTrace tailWord_2099821 prefixEnd_2099821 359405820468244724793535 := by
  unfold tailWord_2099821
  simp only [CollatzResearch.WordTrace]
  refine ⟨76586763725714612720643317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51057842483809741813762211 76586763725714612720643317)
  ·
    refine ⟨7180009099285744942560311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76586763725714612720643317 7180009099285744942560311)
    ·
      refine ⟨10770013648928617413840467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7180009099285744942560311 10770013648928617413840467)
      ·
        refine ⟨16155020473392926120760701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10770013648928617413840467 16155020473392926120760701)
        ·
          refine ⟨6058132677522347295285263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16155020473392926120760701 6058132677522347295285263)
          ·
            refine ⟨9087199016283520942927895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058132677522347295285263 9087199016283520942927895)
            ·
              refine ⟨13630798524425281414391843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9087199016283520942927895 13630798524425281414391843)
              ·
                refine ⟨20446197786637922121587765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13630798524425281414391843 20446197786637922121587765)
                ·
                  refine ⟨1916831042497305198898853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20446197786637922121587765 1916831042497305198898853)
                  ·
                    refine ⟨359405820468244724793535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916831042497305198898853 359405820468244724793535)
                    ·
                      rfl

theorem cell23_2099821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2099821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099821 prefixEnd_2099821 := by exact prefixLift 2099821
  have htrace : WordTrace (prefixWord ++ tailWord_2099821) baseStart_2099821 baseEnd_2099821 := by
    simpa [prefixWord, tailWord_2099821, baseEnd_2099821] using wordTrace_append hprefix tailTrace_2099821
  have hstable : (prefixWord ++ tailWord_2099821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099821).length < 2 ^ (prefixWord ++ tailWord_2099821).sum := by decide
  have hdescent : baseEnd_2099821 < baseStart_2099821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099831 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_2099831 : Nat := 118140960795 + 2099831 * 2 ^ 59
def prefixEnd_2099831 : Nat := 4983230072969 + 3 ^ 40 * 2099831 * 2
def baseEnd_2099831 : Nat := 1078222596211279135255559

theorem tailTrace_2099831 : CollatzResearch.WordTrace tailWord_2099831 prefixEnd_2099831 1078222596211279135255559 := by
  unfold tailWord_2099831
  simp only [CollatzResearch.WordTrace]
  refine ⟨76587128455678384428507347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51058085637118922952338231 76587128455678384428507347)
  ·
    refine ⟨114880692683517576642761021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76587128455678384428507347 114880692683517576642761021)
    ·
      refine ⟨43080259756319091241035383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114880692683517576642761021 43080259756319091241035383)
      ·
        refine ⟨64620389634478636861553075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43080259756319091241035383 64620389634478636861553075)
        ·
          refine ⟨96930584451717955292329613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64620389634478636861553075 96930584451717955292329613)
          ·
            refine ⟨36348969169394233234623605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96930584451717955292329613 36348969169394233234623605)
            ·
              refine ⟨3407715859630709365745963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36348969169394233234623605 3407715859630709365745963)
              ·
                refine ⟨5111573789446064048618945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407715859630709365745963 5111573789446064048618945)
                ·
                  refine ⟨3833680342084548036464209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5111573789446064048618945 3833680342084548036464209)
                  ·
                    refine ⟨2875260256563411027348157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833680342084548036464209 2875260256563411027348157)
                    ·
                      refine ⟨1078222596211279135255559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875260256563411027348157 1078222596211279135255559)
                      ·
                        rfl

theorem cell23_2099831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_2099831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099831 prefixEnd_2099831 := by exact prefixLift 2099831
  have htrace : WordTrace (prefixWord ++ tailWord_2099831) baseStart_2099831 baseEnd_2099831 := by
    simpa [prefixWord, tailWord_2099831, baseEnd_2099831] using wordTrace_append hprefix tailTrace_2099831
  have hstable : (prefixWord ++ tailWord_2099831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099831).length < 2 ^ (prefixWord ++ tailWord_2099831).sum := by decide
  have hdescent : baseEnd_2099831 < baseStart_2099831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099854 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2099854 : Nat := 118140960795 + 2099854 * 2 ^ 59
def prefixEnd_2099854 : Nat := 4983230072969 + 3 ^ 40 * 2099854 * 2
def baseEnd_2099854 : Nat := 1078234406266332545267953

theorem tailTrace_2099854 : CollatzResearch.WordTrace tailWord_2099854 prefixEnd_2099854 1078234406266332545267953 := by
  unfold tailWord_2099854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9573495916824382419574327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51058644889730039571063077 9573495916824382419574327)
  ·
    refine ⟨14360243875236573629361491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9573495916824382419574327 14360243875236573629361491)
    ·
      refine ⟨21540365812854860444042237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14360243875236573629361491 21540365812854860444042237)
      ·
        refine ⟨8077637179820572666515839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21540365812854860444042237 8077637179820572666515839)
        ·
          refine ⟨12116455769730858999773759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8077637179820572666515839 12116455769730858999773759)
          ·
            refine ⟨18174683654596288499660639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12116455769730858999773759 18174683654596288499660639)
            ·
              refine ⟨27262025481894432749490959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18174683654596288499660639 27262025481894432749490959)
              ·
                refine ⟨40893038222841649124236439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27262025481894432749490959 40893038222841649124236439)
                ·
                  refine ⟨61339557334262473686354659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40893038222841649124236439 61339557334262473686354659)
                  ·
                    refine ⟨92009336001393710529531989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61339557334262473686354659 92009336001393710529531989)
                    ·
                      refine ⟨1078234406266332545267953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92009336001393710529531989 1078234406266332545267953)
                      ·
                        rfl

theorem cell23_2099854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2099854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099854 prefixEnd_2099854 := by exact prefixLift 2099854
  have htrace : WordTrace (prefixWord ++ tailWord_2099854) baseStart_2099854 baseEnd_2099854 := by
    simpa [prefixWord, tailWord_2099854, baseEnd_2099854] using wordTrace_append hprefix tailTrace_2099854
  have hstable : (prefixWord ++ tailWord_2099854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099854).length < 2 ^ (prefixWord ++ tailWord_2099854).sum := by decide
  have hdescent : baseEnd_2099854 < baseStart_2099854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099868 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 6]
def baseStart_2099868 : Nat := 118140960795 + 2099868 * 2 ^ 59
def prefixEnd_2099868 : Nat := 4983230072969 + 3 ^ 40 * 2099868 * 2
def baseEnd_2099868 : Nat := 119804621666166165610321

theorem tailTrace_2099868 : CollatzResearch.WordTrace tailWord_2099868 prefixEnd_2099868 119804621666166165610321 := by
  unfold tailWord_2099868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38294238978272169873802129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51058985304362893165069505 38294238978272169873802129)
  ·
    refine ⟨28720679233704127405351597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38294238978272169873802129 28720679233704127405351597)
    ·
      refine ⟨10770254712639047777006849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28720679233704127405351597 10770254712639047777006849)
      ·
        refine ⟨8077691034479285832755137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10770254712639047777006849 8077691034479285832755137)
        ·
          refine ⟨6058268275859464374566353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8077691034479285832755137 6058268275859464374566353)
          ·
            refine ⟨4543701206894598280924765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6058268275859464374566353 4543701206894598280924765)
            ·
              refine ⟨1703887952585474355346787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4543701206894598280924765 1703887952585474355346787)
              ·
                refine ⟨2555831928878211533020181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703887952585474355346787 2555831928878211533020181)
                ·
                  refine ⟨119804621666166165610321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2555831928878211533020181 119804621666166165610321)
                  ·
                    rfl

theorem cell23_2099868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_2099868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099868 prefixEnd_2099868 := by exact prefixLift 2099868
  have htrace : WordTrace (prefixWord ++ tailWord_2099868) baseStart_2099868 baseEnd_2099868 := by
    simpa [prefixWord, tailWord_2099868, baseEnd_2099868] using wordTrace_append hprefix tailTrace_2099868
  have hstable : (prefixWord ++ tailWord_2099868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099868).length < 2 ^ (prefixWord ++ tailWord_2099868).sum := by decide
  have hdescent : baseEnd_2099868 < baseStart_2099868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099889 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 1, 4]
def baseStart_2099889 : Nat := 118140960795 + 2099889 * 2 ^ 59
def prefixEnd_2099889 : Nat := 4983230072969 + 3 ^ 40 * 2099889 * 2
def baseEnd_2099889 : Nat := 359417459363079969443431

theorem tailTrace_2099889 : CollatzResearch.WordTrace tailWord_2099889 prefixEnd_2099889 359417459363079969443431 := by
  unfold tailWord_2099889
  simp only [CollatzResearch.WordTrace]
  refine ⟨76589243889468260334118721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51059495926312173556079147 76589243889468260334118721)
  ·
    refine ⟨57441932917101195250589041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76589243889468260334118721 57441932917101195250589041)
    ·
      refine ⟨43081449687825896437941781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57441932917101195250589041 43081449687825896437941781)
      ·
        refine ⟨2019442954116838895528521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43081449687825896437941781 2019442954116838895528521)
        ·
          refine ⟨1514582215587629171646391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019442954116838895528521 1514582215587629171646391)
          ·
            refine ⟨2271873323381443757469587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514582215587629171646391 2271873323381443757469587)
            ·
              refine ⟨3407809985072165636204381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271873323381443757469587 3407809985072165636204381)
              ·
                refine ⟨1277928744402062113576643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3407809985072165636204381 1277928744402062113576643)
                ·
                  refine ⟨1916893116603093170364965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277928744402062113576643 1916893116603093170364965)
                  ·
                    refine ⟨359417459363079969443431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916893116603093170364965 359417459363079969443431)
                    ·
                      rfl

theorem cell23_2099889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_2099889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099889 prefixEnd_2099889 := by exact prefixLift 2099889
  have htrace : WordTrace (prefixWord ++ tailWord_2099889) baseStart_2099889 baseEnd_2099889 := by
    simpa [prefixWord, tailWord_2099889, baseEnd_2099889] using wordTrace_append hprefix tailTrace_2099889
  have hstable : (prefixWord ++ tailWord_2099889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099889).length < 2 ^ (prefixWord ++ tailWord_2099889).sum := by decide
  have hdescent : baseEnd_2099889 < baseStart_2099889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099912 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_2099912 : Nat := 118140960795 + 2099912 * 2 ^ 59
def prefixEnd_2099912 : Nat := 4983230072969 + 3 ^ 40 * 2099912 * 2
def baseEnd_2099912 : Nat := 1078264188144293318342687

theorem tailTrace_2099912 : CollatzResearch.WordTrace tailWord_2099912 prefixEnd_2099912 1078264188144293318342687 := by
  unfold tailWord_2099912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38295041384192467631102995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51060055178923290174803993 38295041384192467631102995)
  ·
    refine ⟨57442562076288701446654493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38295041384192467631102995 57442562076288701446654493)
    ·
      refine ⟨21540960778608263042495435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57442562076288701446654493 21540960778608263042495435)
      ·
        refine ⟨32311441167912394563743153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21540960778608263042495435 32311441167912394563743153)
        ·
          refine ⟨24233580875934295922807365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32311441167912394563743153 24233580875934295922807365)
          ·
            refine ⟨4543796414237680485526381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24233580875934295922807365 4543796414237680485526381)
            ·
              refine ⟨1703923655339130182072393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4543796414237680485526381 1703923655339130182072393)
              ·
                refine ⟨1277942741504347636554295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703923655339130182072393 1277942741504347636554295)
                ·
                  refine ⟨1916914112256521454831443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277942741504347636554295 1916914112256521454831443)
                  ·
                    refine ⟨2875371168384782182247165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1916914112256521454831443 2875371168384782182247165)
                    ·
                      refine ⟨1078264188144293318342687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875371168384782182247165 1078264188144293318342687)
                      ·
                        rfl

theorem cell23_2099912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_2099912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099912 prefixEnd_2099912 := by exact prefixLift 2099912
  have htrace : WordTrace (prefixWord ++ tailWord_2099912) baseStart_2099912 baseEnd_2099912 := by
    simpa [prefixWord, tailWord_2099912, baseEnd_2099912] using wordTrace_append hprefix tailTrace_2099912
  have hstable : (prefixWord ++ tailWord_2099912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099912).length < 2 ^ (prefixWord ++ tailWord_2099912).sum := by decide
  have hdescent : baseEnd_2099912 < baseStart_2099912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099921 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_2099921 : Nat := 118140960795 + 2099921 * 2 ^ 59
def prefixEnd_2099921 : Nat := 4983230072969 + 3 ^ 40 * 2099921 * 2
def baseEnd_2099921 : Nat := 1078268809470183783130145

theorem tailTrace_2099921 : CollatzResearch.WordTrace tailWord_2099921 prefixEnd_2099921 1078268809470183783130145 := by
  unfold tailWord_2099921
  simp only [CollatzResearch.WordTrace]
  refine ⟨76590411025352329799283617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51060274016901553199522411 76590411025352329799283617)
  ·
    refine ⟨57442808269014247349462713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76590411025352329799283617 57442808269014247349462713)
    ·
      refine ⟨43082106201760685512097035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57442808269014247349462713 43082106201760685512097035)
      ·
        refine ⟨64623159302641028268145553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43082106201760685512097035 64623159302641028268145553)
        ·
          refine ⟨48467369476980771201109165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64623159302641028268145553 48467369476980771201109165)
          ·
            refine ⟨18175263553867789200415937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48467369476980771201109165 18175263553867789200415937)
            ·
              refine ⟨13631447665400841900311953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18175263553867789200415937 13631447665400841900311953)
              ·
                refine ⟨10223585749050631425233965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13631447665400841900311953 10223585749050631425233965)
                ·
                  refine ⟨3833844655893986784462737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10223585749050631425233965 3833844655893986784462737)
                  ·
                    refine ⟨2875383491920490088347053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833844655893986784462737 2875383491920490088347053)
                    ·
                      refine ⟨1078268809470183783130145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875383491920490088347053 1078268809470183783130145)
                      ·
                        rfl

theorem cell23_2099921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_2099921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099921 prefixEnd_2099921 := by exact prefixLift 2099921
  have htrace : WordTrace (prefixWord ++ tailWord_2099921) baseStart_2099921 baseEnd_2099921 := by
    simpa [prefixWord, tailWord_2099921, baseEnd_2099921] using wordTrace_append hprefix tailTrace_2099921
  have hstable : (prefixWord ++ tailWord_2099921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099921).length < 2 ^ (prefixWord ++ tailWord_2099921).sum := by decide
  have hdescent : baseEnd_2099921 < baseStart_2099921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099928 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_2099928 : Nat := 118140960795 + 2099928 * 2 ^ 59
def prefixEnd_2099928 : Nat := 4983230072969 + 3 ^ 40 * 2099928 * 2
def baseEnd_2099928 : Nat := 359424134611588418580871

theorem tailTrace_2099928 : CollatzResearch.WordTrace tailWord_2099928 prefixEnd_2099928 359424134611588418580871 := by
  unfold tailWord_2099928
  simp only [CollatzResearch.WordTrace]
  refine ⟨38295333168163484997394219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51060444224217979996525625 38295333168163484997394219)
  ·
    refine ⟨57442999752245227496091329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38295333168163484997394219 57442999752245227496091329)
    ·
      refine ⟨43082249814183920622068497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57442999752245227496091329 43082249814183920622068497)
      ·
        refine ⟨32311687360637940466551373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43082249814183920622068497 32311687360637940466551373)
        ·
          refine ⟨12116882760239227674956765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32311687360637940466551373 12116882760239227674956765)
          ·
            refine ⟨4543831035089710378108787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12116882760239227674956765 4543831035089710378108787)
            ·
              refine ⟨6815746552634565567163181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543831035089710378108787 6815746552634565567163181)
              ·
                refine ⟨2555904957237962087686193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6815746552634565567163181 2555904957237962087686193)
                ·
                  refine ⟨1916928717928471565764645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555904957237962087686193 1916928717928471565764645)
                  ·
                    refine ⟨359424134611588418580871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916928717928471565764645 359424134611588418580871)
                    ·
                      rfl

theorem cell23_2099928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_2099928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099928 prefixEnd_2099928 := by exact prefixLift 2099928
  have htrace : WordTrace (prefixWord ++ tailWord_2099928) baseStart_2099928 baseEnd_2099928 := by
    simpa [prefixWord, tailWord_2099928, baseEnd_2099928] using wordTrace_append hprefix tailTrace_2099928
  have hstable : (prefixWord ++ tailWord_2099928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099928).length < 2 ^ (prefixWord ++ tailWord_2099928).sum := by decide
  have hdescent : baseEnd_2099928 < baseStart_2099928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099951 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_2099951 : Nat := 118140960795 + 2099951 * 2 ^ 59
def prefixEnd_2099951 : Nat := 4983230072969 + 3 ^ 40 * 2099951 * 2
def baseEnd_2099951 : Nat := 1078284213889818665755007

theorem tailTrace_2099951 : CollatzResearch.WordTrace tailWord_2099951 prefixEnd_2099951 1078284213889818665755007 := by
  unfold tailWord_2099951
  simp only [CollatzResearch.WordTrace]
  refine ⟨76591505215243644922875707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51061003476829096615250471 76591505215243644922875707)
  ·
    refine ⟨114887257822865467384313561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76591505215243644922875707 114887257822865467384313561)
    ·
      refine ⟨86165443367149100538235171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114887257822865467384313561 86165443367149100538235171)
      ·
        refine ⟨129248165050723650807352757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86165443367149100538235171 129248165050723650807352757)
        ·
          refine ⟨12117015473505342263189321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129248165050723650807352757 12117015473505342263189321)
          ·
            refine ⟨9087761605129006697391991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12117015473505342263189321 9087761605129006697391991)
            ·
              refine ⟨13631642407693510046087987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9087761605129006697391991 13631642407693510046087987)
              ·
                refine ⟨20447463611540265069131981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13631642407693510046087987 20447463611540265069131981)
                ·
                  refine ⟨7667798854327599400924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20447463611540265069131981 7667798854327599400924493)
                  ·
                    refine ⟨2875424570372849775346685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7667798854327599400924493 2875424570372849775346685)
                    ·
                      refine ⟨1078284213889818665755007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875424570372849775346685 1078284213889818665755007)
                      ·
                        rfl

theorem cell23_2099951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_2099951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099951 prefixEnd_2099951 := by exact prefixLift 2099951
  have htrace : WordTrace (prefixWord ++ tailWord_2099951) baseStart_2099951 baseEnd_2099951 := by
    simpa [prefixWord, tailWord_2099951, baseEnd_2099951] using wordTrace_append hprefix tailTrace_2099951
  have hstable : (prefixWord ++ tailWord_2099951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099951).length < 2 ^ (prefixWord ++ tailWord_2099951).sum := by decide
  have hdescent : baseEnd_2099951 < baseStart_2099951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099978 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_2099978 : Nat := 118140960795 + 2099978 * 2 ^ 59
def prefixEnd_2099978 : Nat := 4983230072969 + 3 ^ 40 * 2099978 * 2
def baseEnd_2099978 : Nat := 1078298077867490060117383

theorem tailTrace_2099978 : CollatzResearch.WordTrace tailWord_2099978 prefixEnd_2099978 1078298077867490060117383 := by
  unfold tailWord_2099978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19148122496536457133527147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51061659990763885689405725 19148122496536457133527147)
  ·
    refine ⟨28722183744804685700290721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19148122496536457133527147 28722183744804685700290721)
    ·
      refine ⟨21541637808603514275218041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28722183744804685700290721 21541637808603514275218041)
      ·
        refine ⟨16156228356452635706413531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21541637808603514275218041 16156228356452635706413531)
        ·
          refine ⟨24234342534678953559620297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16156228356452635706413531 24234342534678953559620297)
          ·
            refine ⟨18175756901009215169715223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24234342534678953559620297 18175756901009215169715223)
            ·
              refine ⟨27263635351513822754572835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18175756901009215169715223 27263635351513822754572835)
              ·
                refine ⟨40895453027270734131859253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27263635351513822754572835 40895453027270734131859253)
                ·
                  refine ⟨3833948721306631324861805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40895453027270734131859253 3833948721306631324861805)
                  ·
                    refine ⟨1437730770489986746823177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3833948721306631324861805 1437730770489986746823177)
                    ·
                      refine ⟨1078298077867490060117383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437730770489986746823177 1078298077867490060117383)
                      ·
                        rfl

theorem cell23_2099978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_2099978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099978 prefixEnd_2099978 := by exact prefixLift 2099978
  have htrace : WordTrace (prefixWord ++ tailWord_2099978) baseStart_2099978 baseEnd_2099978 := by
    simpa [prefixWord, tailWord_2099978, baseEnd_2099978] using wordTrace_append hprefix tailTrace_2099978
  have hstable : (prefixWord ++ tailWord_2099978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099978).length < 2 ^ (prefixWord ++ tailWord_2099978).sum := by decide
  have hdescent : baseEnd_2099978 < baseStart_2099978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100031 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 7]
def baseStart_2100031 : Nat := 118140960795 + 2100031 * 2 ^ 59
def prefixEnd_2100031 : Nat := 4983230072969 + 3 ^ 40 * 2100031 * 2
def baseEnd_2100031 : Nat := 119813921371353150306071

theorem tailTrace_2100031 : CollatzResearch.WordTrace tailWord_2100031 prefixEnd_2100031 119813921371353150306071 := by
  unfold tailWord_2100031
  simp only [CollatzResearch.WordTrace]
  refine ⟨76594423054953818585787947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51062948703302545723858631 76594423054953818585787947)
  ·
    refine ⟨114891634582430727878681921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76594423054953818585787947 114891634582430727878681921)
    ·
      refine ⟨86168725936823045909011441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114891634582430727878681921 86168725936823045909011441)
      ·
        refine ⟨64626544452617284431758581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86168725936823045909011441 64626544452617284431758581)
        ·
          refine ⟨6058738542432870415477367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64626544452617284431758581 6058738542432870415477367)
          ·
            refine ⟨9088107813649305623216051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058738542432870415477367 9088107813649305623216051)
            ·
              refine ⟨13632161720473958434824077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9088107813649305623216051 13632161720473958434824077)
              ·
                refine ⟨5112060645177734413059029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13632161720473958434824077 5112060645177734413059029)
                ·
                  refine ⟨119813921371353150306071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5112060645177734413059029 119813921371353150306071)
                  ·
                    rfl

theorem cell23_2100031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 7].length) (baseStart_2100031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100031 prefixEnd_2100031 := by exact prefixLift 2100031
  have htrace : WordTrace (prefixWord ++ tailWord_2100031) baseStart_2100031 baseEnd_2100031 := by
    simpa [prefixWord, tailWord_2100031, baseEnd_2100031] using wordTrace_append hprefix tailTrace_2100031
  have hstable : (prefixWord ++ tailWord_2100031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100031).length < 2 ^ (prefixWord ++ tailWord_2100031).sum := by decide
  have hdescent : baseEnd_2100031 < baseStart_2100031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100036 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2100036 : Nat := 118140960795 + 2100036 * 2 ^ 59
def prefixEnd_2100036 : Nat := 4983230072969 + 3 ^ 40 * 2100036 * 2
def baseEnd_2100036 : Nat := 1078327859745450833192117

theorem tailTrace_2100036 : CollatzResearch.WordTrace tailWord_2100036 prefixEnd_2100036 1078327859745450833192117 := by
  unfold tailWord_2100036
  simp only [CollatzResearch.WordTrace]
  refine ⟨38297302709967852219859981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51063070279957136293146641 38297302709967852219859981)
  ·
    refine ⟨14361488516237944582447493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38297302709967852219859981 14361488516237944582447493)
    ·
      refine ⟨2692779096794614609208905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14361488516237944582447493 2692779096794614609208905)
      ·
        refine ⟨2019584322595960956906679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2692779096794614609208905 2019584322595960956906679)
        ·
          refine ⟨3029376483893941435360019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019584322595960956906679 3029376483893941435360019)
          ·
            refine ⟨4544064725840912153040029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029376483893941435360019 4544064725840912153040029)
            ·
              refine ⟨1704024272190342057390011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4544064725840912153040029 1704024272190342057390011)
              ·
                refine ⟨2556036408285513086085017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704024272190342057390011 2556036408285513086085017)
                ·
                  refine ⟨1917027306214134814563763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556036408285513086085017 1917027306214134814563763)
                  ·
                    refine ⟨2875540959321202221845645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917027306214134814563763 2875540959321202221845645)
                    ·
                      refine ⟨1078327859745450833192117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875540959321202221845645 1078327859745450833192117)
                      ·
                        rfl

theorem cell23_2100036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2100036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100036 prefixEnd_2100036 := by exact prefixLift 2100036
  have htrace : WordTrace (prefixWord ++ tailWord_2100036) baseStart_2100036 baseEnd_2100036 := by
    simpa [prefixWord, tailWord_2100036, baseEnd_2100036] using wordTrace_append hprefix tailTrace_2100036
  have hstable : (prefixWord ++ tailWord_2100036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100036).length < 2 ^ (prefixWord ++ tailWord_2100036).sum := by decide
  have hdescent : baseEnd_2100036 < baseStart_2100036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
