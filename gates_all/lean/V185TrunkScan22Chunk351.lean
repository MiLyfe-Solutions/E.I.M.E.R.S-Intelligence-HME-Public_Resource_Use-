import V185TrunkScan22Chunk350

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3130889 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 4]
def baseStart_3130889 : Nat := 118140960795 + 3130889 * 2 ^ 59
def prefixEnd_3130889 : Nat := 4983230072969 + 3 ^ 40 * 3130889 * 2
def baseEnd_3130889 : Nat := 357255762861045803575291

theorem tailTrace_3130889 : CollatzResearch.WordTrace tailWord_3130889 prefixEnd_3130889 357255762861045803575291 := by
  unfold tailWord_3130889
  simp only [CollatzResearch.WordTrace]
  refine ⟨114192903154331341115611721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76128602102887560743741147 114192903154331341115611721)
  ·
    refine ⟨85644677365748505836708791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114192903154331341115611721 85644677365748505836708791)
    ·
      refine ⟨128467016048622758755063187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85644677365748505836708791 128467016048622758755063187)
      ·
        refine ⟨192700524072934138132594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128467016048622758755063187 192700524072934138132594781)
        ·
          refine ⟨72262696527350301799723043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192700524072934138132594781 72262696527350301799723043)
          ·
            refine ⟨108394044791025452699584565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72262696527350301799723043 108394044791025452699584565)
            ·
              refine ⟨10161941699158636190586053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108394044791025452699584565 10161941699158636190586053)
              ·
                refine ⟨1905364068592244285734885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10161941699158636190586053 1905364068592244285734885)
                ·
                  refine ⟨357255762861045803575291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905364068592244285734885 357255762861045803575291)
                  ·
                    rfl

theorem cell22_3130889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_3130889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130889 prefixEnd_3130889 := by exact prefixLift 3130889
  have htrace : WordTrace (prefixWord ++ tailWord_3130889) baseStart_3130889 baseEnd_3130889 := by
    simpa [prefixWord, tailWord_3130889, baseEnd_3130889] using wordTrace_append hprefix tailTrace_3130889
  have hstable : (prefixWord ++ tailWord_3130889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130889).length < 2 ^ (prefixWord ++ tailWord_3130889).sum := by decide
  have hdescent : baseEnd_3130889 < baseStart_3130889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130893 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3130893 : Nat := 118140960795 + 3130893 * 2 ^ 59
def prefixEnd_3130893 : Nat := 4983230072969 + 3 ^ 40 * 3130893 * 2
def baseEnd_3130893 : Nat := 1071768657864882733625861

theorem tailTrace_3130893 : CollatzResearch.WordTrace tailWord_3130893 prefixEnd_3130893 1071768657864882733625861 := by
  unfold tailWord_3130893
  simp only [CollatzResearch.WordTrace]
  refine ⟨114193049046316849798757333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76128699364211233199171555 114193049046316849798757333)
  ·
    refine ⟨2676399587023051167158375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114193049046316849798757333 2676399587023051167158375)
    ·
      refine ⟨4014599380534576750737563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676399587023051167158375 4014599380534576750737563)
      ·
        refine ⟨6021899070801865126106345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014599380534576750737563 6021899070801865126106345)
        ·
          refine ⟨4516424303101398844579759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021899070801865126106345 4516424303101398844579759)
          ·
            refine ⟨6774636454652098266869639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516424303101398844579759 6774636454652098266869639)
            ·
              refine ⟨10161954681978147400304459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774636454652098266869639 10161954681978147400304459)
              ·
                refine ⟨15242932022967221100456689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161954681978147400304459 15242932022967221100456689)
                ·
                  refine ⟨11432199017225415825342517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15242932022967221100456689 11432199017225415825342517)
                  ·
                    refine ⟨1071768657864882733625861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11432199017225415825342517 1071768657864882733625861)
                    ·
                      rfl

theorem cell22_3130893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3130893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130893 prefixEnd_3130893 := by exact prefixLift 3130893
  have htrace : WordTrace (prefixWord ++ tailWord_3130893) baseStart_3130893 baseEnd_3130893 := by
    simpa [prefixWord, tailWord_3130893, baseEnd_3130893] using wordTrace_append hprefix tailTrace_3130893
  have hstable : (prefixWord ++ tailWord_3130893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130893).length < 2 ^ (prefixWord ++ tailWord_3130893).sum := by decide
  have hdescent : baseEnd_3130893 < baseStart_3130893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130983 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3130983 : Nat := 118140960795 + 3130983 * 2 ^ 59
def prefixEnd_3130983 : Nat := 4983230072969 + 3 ^ 40 * 3130983 * 2
def baseEnd_3130983 : Nat := 1071799466704152498875585

theorem tailTrace_3130983 : CollatzResearch.WordTrace tailWord_3130983 prefixEnd_3130983 1071799466704152498875585 := by
  unfold tailWord_3130983
  simp only [CollatzResearch.WordTrace]
  refine ⟨114196331615990795169533603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76130887743993863446355735 114196331615990795169533603)
  ·
    refine ⟨171294497423986192754300405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114196331615990795169533603 171294497423986192754300405)
    ·
      refine ⟨16058859133498705570715663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171294497423986192754300405 16058859133498705570715663)
      ·
        refine ⟨24088288700248058356073495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16058859133498705570715663 24088288700248058356073495)
        ·
          refine ⟨36132433050372087534110243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24088288700248058356073495 36132433050372087534110243)
          ·
            refine ⟨54198649575558131301165365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36132433050372087534110243 54198649575558131301165365)
            ·
              refine ⟨5081123397708574809484253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54198649575558131301165365 5081123397708574809484253)
              ·
                refine ⟨1905421274140715553556595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5081123397708574809484253 1905421274140715553556595)
                ·
                  refine ⟨2858131911211073330334893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905421274140715553556595 2858131911211073330334893)
                  ·
                    refine ⟨1071799466704152498875585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858131911211073330334893 1071799466704152498875585)
                    ·
                      rfl

theorem cell22_3130983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3130983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130983 prefixEnd_3130983 := by exact prefixLift 3130983
  have htrace : WordTrace (prefixWord ++ tailWord_3130983) baseStart_3130983 baseEnd_3130983 := by
    simpa [prefixWord, tailWord_3130983, baseEnd_3130983] using wordTrace_append hprefix tailTrace_3130983
  have hstable : (prefixWord ++ tailWord_3130983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130983).length < 2 ^ (prefixWord ++ tailWord_3130983).sum := by decide
  have hdescent : baseEnd_3130983 < baseStart_3130983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131056 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_3131056 : Nat := 118140960795 + 3131056 * 2 ^ 59
def prefixEnd_3131056 : Nat := 4983230072969 + 3 ^ 40 * 3131056 * 2
def baseEnd_3131056 : Nat := 1071824456096004641800361

theorem tailTrace_3131056 : CollatzResearch.WordTrace tailWord_3131056 prefixEnd_3131056 1071824456096004641800361 := by
  unfold tailWord_3131056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57099497072363164318470511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76132662763150885757960681 57099497072363164318470511)
  ·
    refine ⟨85649245608544746477705767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57099497072363164318470511 85649245608544746477705767)
    ·
      refine ⟨128473868412817119716558651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85649245608544746477705767 128473868412817119716558651)
      ·
        refine ⟨192710802619225679574837977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128473868412817119716558651 192710802619225679574837977)
        ·
          refine ⟨144533101964419259681128483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192710802619225679574837977 144533101964419259681128483)
          ·
            refine ⟨216799652946628889521692725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144533101964419259681128483 216799652946628889521692725)
            ·
              refine ⟨20324967463746458392658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216799652946628889521692725 20324967463746458392658693)
              ·
                refine ⟨3810931399452460948623505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20324967463746458392658693 3810931399452460948623505)
                ·
                  refine ⟨2858198549589345711467629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810931399452460948623505 2858198549589345711467629)
                  ·
                    refine ⟨1071824456096004641800361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858198549589345711467629 1071824456096004641800361)
                    ·
                      rfl

theorem cell22_3131056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_3131056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131056 prefixEnd_3131056 := by exact prefixLift 3131056
  have htrace : WordTrace (prefixWord ++ tailWord_3131056) baseStart_3131056 baseEnd_3131056 := by
    simpa [prefixWord, tailWord_3131056, baseEnd_3131056] using wordTrace_append hprefix tailTrace_3131056
  have hstable : (prefixWord ++ tailWord_3131056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131056).length < 2 ^ (prefixWord ++ tailWord_3131056).sum := by decide
  have hdescent : baseEnd_3131056 < baseStart_3131056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131058 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_3131058 : Nat := 118140960795 + 3131058 * 2 ^ 59
def prefixEnd_3131058 : Nat := 4983230072969 + 3 ^ 40 * 3131058 * 2
def baseEnd_3131058 : Nat := 357275046912292434416785

theorem tailTrace_3131058 : CollatzResearch.WordTrace tailWord_3131058 prefixEnd_3131058 357275046912292434416785 := by
  unfold tailWord_3131058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28549766772679770744628457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76132711393812721985675885 28549766772679770744628457)
  ·
    refine ⟨21412325079509828058471343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28549766772679770744628457 21412325079509828058471343)
    ·
      refine ⟨32118487619264742087707015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21412325079509828058471343 32118487619264742087707015)
      ·
        refine ⟨48177731428897113131560523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32118487619264742087707015 48177731428897113131560523)
        ·
          refine ⟨72266597143345669697340785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48177731428897113131560523 72266597143345669697340785)
          ·
            refine ⟨54199947857509252273005589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72266597143345669697340785 54199947857509252273005589)
            ·
              refine ⟨2540622555820746200297137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54199947857509252273005589 2540622555820746200297137)
              ·
                refine ⟨1905466916865559650222853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540622555820746200297137 1905466916865559650222853)
                ·
                  refine ⟨357275046912292434416785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905466916865559650222853 357275046912292434416785)
                  ·
                    rfl

theorem cell22_3131058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_3131058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131058 prefixEnd_3131058 := by exact prefixLift 3131058
  have htrace : WordTrace (prefixWord ++ tailWord_3131058) baseStart_3131058 baseEnd_3131058 := by
    simpa [prefixWord, tailWord_3131058, baseEnd_3131058] using wordTrace_append hprefix tailTrace_3131058
  have hstable : (prefixWord ++ tailWord_3131058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131058).length < 2 ^ (prefixWord ++ tailWord_3131058).sum := by decide
  have hdescent : baseEnd_3131058 < baseStart_3131058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131086 : List Nat := [4, 1, 1, 1, 3, 1, 5, 6]
def baseStart_3131086 : Nat := 118140960795 + 3131086 * 2 ^ 59
def prefixEnd_3131086 : Nat := 4983230072969 + 3 ^ 40 * 3131086 * 2
def baseEnd_3131086 : Nat := 119092747301010507061141

theorem tailTrace_3131086 : CollatzResearch.WordTrace tailWord_3131086 prefixEnd_3131086 119092747301010507061141 := by
  unfold tailWord_3131086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275011041827205470066639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76133392223078429173688741 14275011041827205470066639)
  ·
    refine ⟨21412516562740808205099959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14275011041827205470066639 21412516562740808205099959)
    ·
      refine ⟨32118774844111212307649939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21412516562740808205099959 32118774844111212307649939)
      ·
        refine ⟨48178162266166818461474909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32118774844111212307649939 48178162266166818461474909)
        ·
          refine ⟨18066810849812556923053091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48178162266166818461474909 18066810849812556923053091)
          ·
            refine ⟨27100216274718835384579637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18066810849812556923053091 27100216274718835384579637)
            ·
              refine ⟨2540645275754890817304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27100216274718835384579637 2540645275754890817304341)
              ·
                refine ⟨119092747301010507061141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2540645275754890817304341 119092747301010507061141)
                ·
                  rfl

theorem cell22_3131086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_3131086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131086 prefixEnd_3131086 := by exact prefixLift 3131086
  have htrace : WordTrace (prefixWord ++ tailWord_3131086) baseStart_3131086 baseEnd_3131086 := by
    simpa [prefixWord, tailWord_3131086, baseEnd_3131086] using wordTrace_append hprefix tailTrace_3131086
  have hstable : (prefixWord ++ tailWord_3131086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131086).length < 2 ^ (prefixWord ++ tailWord_3131086).sum := by decide
  have hdescent : baseEnd_3131086 < baseStart_3131086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131094 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3131094 : Nat := 118140960795 + 3131094 * 2 ^ 59
def prefixEnd_3131094 : Nat := 4983230072969 + 3 ^ 40 * 3131094 * 2
def baseEnd_3131094 : Nat := 1071837464272585209350245

theorem tailTrace_3131094 : CollatzResearch.WordTrace tailWord_3131094 prefixEnd_3131094 1071837464272585209350245 := by
  unfold tailWord_3131094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137523757411791320426521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76133586745725774084549557 7137523757411791320426521)
  ·
    refine ⟨5353142818058843490319891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7137523757411791320426521 5353142818058843490319891)
    ·
      refine ⟨8029714227088265235479837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353142818058843490319891 8029714227088265235479837)
      ·
        refine ⟨3011142835158099463304939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8029714227088265235479837 3011142835158099463304939)
        ·
          refine ⟨4516714252737149194957409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011142835158099463304939 4516714252737149194957409)
          ·
            refine ⟨3387535689552861896218057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4516714252737149194957409 3387535689552861896218057)
            ·
              refine ⟨2540651767164646422163543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387535689552861896218057 2540651767164646422163543)
              ·
                refine ⟨3810977650746969633245315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540651767164646422163543 3810977650746969633245315)
                ·
                  refine ⟨5716466476120454449867973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810977650746969633245315 5716466476120454449867973)
                  ·
                    refine ⟨1071837464272585209350245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716466476120454449867973 1071837464272585209350245)
                    ·
                      rfl

theorem cell22_3131094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3131094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131094 prefixEnd_3131094 := by exact prefixLift 3131094
  have htrace : WordTrace (prefixWord ++ tailWord_3131094) baseStart_3131094 baseEnd_3131094 := by
    simpa [prefixWord, tailWord_3131094, baseEnd_3131094] using wordTrace_append hprefix tailTrace_3131094
  have hstable : (prefixWord ++ tailWord_3131094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131094).length < 2 ^ (prefixWord ++ tailWord_3131094).sum := by decide
  have hdescent : baseEnd_3131094 < baseStart_3131094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131107 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 2, 3]
def baseStart_3131107 : Nat := 118140960795 + 3131107 * 2 ^ 59
def prefixEnd_3131107 : Nat := 4983230072969 + 3 ^ 40 * 3131107 * 2
def baseEnd_3131107 : Nat := 1071841914438257508775205

theorem tailTrace_3131107 : CollatzResearch.WordTrace tailWord_3131107 prefixEnd_3131107 1071841914438257508775205 := by
  unfold tailWord_3131107
  simp only [CollatzResearch.WordTrace]
  refine ⟨114200854267541564347047575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76133902845027709564698383 114200854267541564347047575)
  ·
    refine ⟨171301281401312346520571363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114200854267541564347047575 171301281401312346520571363)
    ·
      refine ⟨256951922101968519780857045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171301281401312346520571363 256951922101968519780857045)
      ·
        refine ⟨6022310674264887182363837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 256951922101968519780857045 6022310674264887182363837)
        ·
          refine ⟨2258366502849332693386439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6022310674264887182363837 2258366502849332693386439)
          ·
            refine ⟨3387549754273999040079659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258366502849332693386439 3387549754273999040079659)
            ·
              refine ⟨5081324631410998560119489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387549754273999040079659 5081324631410998560119489)
              ·
                refine ⟨3810993473558248920089617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081324631410998560119489 3810993473558248920089617)
                ·
                  refine ⟨2858245105168686690067213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810993473558248920089617 2858245105168686690067213)
                  ·
                    refine ⟨1071841914438257508775205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858245105168686690067213 1071841914438257508775205)
                    ·
                      rfl

theorem cell22_3131107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 3].length) (baseStart_3131107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131107 prefixEnd_3131107 := by exact prefixLift 3131107
  have htrace : WordTrace (prefixWord ++ tailWord_3131107) baseStart_3131107 baseEnd_3131107 := by
    simpa [prefixWord, tailWord_3131107, baseEnd_3131107] using wordTrace_append hprefix tailTrace_3131107
  have hstable : (prefixWord ++ tailWord_3131107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131107).length < 2 ^ (prefixWord ++ tailWord_3131107).sum := by decide
  have hdescent : baseEnd_3131107 < baseStart_3131107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131118 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3131118 : Nat := 118140960795 + 3131118 * 2 ^ 59
def prefixEnd_3131118 : Nat := 4983230072969 + 3 ^ 40 * 3131118 * 2
def baseEnd_3131118 : Nat := 1071845679963057146750171

theorem tailTrace_3131118 : CollatzResearch.WordTrace tailWord_3131118 prefixEnd_3131118 1071845679963057146750171 := by
  unfold tailWord_3131118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275156933812714153212251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76134170313667808817132005 14275156933812714153212251)
  ·
    refine ⟨21412735400719071229818377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14275156933812714153212251 21412735400719071229818377)
    ·
      refine ⟨16059551550539303422363783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21412735400719071229818377 16059551550539303422363783)
      ·
        refine ⟨24089327325808955133545675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059551550539303422363783 24089327325808955133545675)
        ·
          refine ⟨36133990988713432700318513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24089327325808955133545675 36133990988713432700318513)
          ·
            refine ⟨27100493241535074525238885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36133990988713432700318513 27100493241535074525238885)
            ·
              refine ⟨5081342482787826473482291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27100493241535074525238885 5081342482787826473482291)
              ·
                refine ⟨7622013724181739710223437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081342482787826473482291 7622013724181739710223437)
                ·
                  refine ⟨2858255146568152391333789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7622013724181739710223437 2858255146568152391333789)
                  ·
                    refine ⟨1071845679963057146750171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858255146568152391333789 1071845679963057146750171)
                    ·
                      rfl

theorem cell22_3131118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3131118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131118 prefixEnd_3131118 := by exact prefixLift 3131118
  have htrace : WordTrace (prefixWord ++ tailWord_3131118) baseStart_3131118 baseEnd_3131118 := by
    simpa [prefixWord, tailWord_3131118, baseEnd_3131118] using wordTrace_append hprefix tailTrace_3131118
  have hstable : (prefixWord ++ tailWord_3131118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131118).length < 2 ^ (prefixWord ++ tailWord_3131118).sum := by decide
  have hdescent : baseEnd_3131118 < baseStart_3131118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131124 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3131124 : Nat := 118140960795 + 3131124 * 2 ^ 59
def prefixEnd_3131124 : Nat := 4983230072969 + 3 ^ 40 * 3131124 * 2
def baseEnd_3131124 : Nat := 1071847733885675131100153

theorem tailTrace_3131124 : CollatzResearch.WordTrace tailWord_3131124 prefixEnd_3131124 1071847733885675131100153 := by
  unfold tailWord_3131124
  simp only [CollatzResearch.WordTrace]
  refine ⟨57100737154239988125208213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76134316205653317500277617 57100737154239988125208213)
  ·
    refine ⟨2676597054104999443369135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57100737154239988125208213 2676597054104999443369135)
    ·
      refine ⟨4014895581157499165053703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676597054104999443369135 4014895581157499165053703)
      ·
        refine ⟨6022343371736248747580555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014895581157499165053703 6022343371736248747580555)
        ·
          refine ⟨9033515057604373121370833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022343371736248747580555 9033515057604373121370833)
          ·
            refine ⟨6775136293203279841028125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033515057604373121370833 6775136293203279841028125)
            ·
              refine ⟨2540676109951229940385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6775136293203279841028125 2540676109951229940385547)
              ·
                refine ⟨3811014164926844910578321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540676109951229940385547 3811014164926844910578321)
                ·
                  refine ⟨2858260623695133682933741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3811014164926844910578321 2858260623695133682933741)
                  ·
                    refine ⟨1071847733885675131100153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858260623695133682933741 1071847733885675131100153)
                    ·
                      rfl

theorem cell22_3131124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3131124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131124 prefixEnd_3131124 := by exact prefixLift 3131124
  have htrace : WordTrace (prefixWord ++ tailWord_3131124) baseStart_3131124 baseEnd_3131124 := by
    simpa [prefixWord, tailWord_3131124, baseEnd_3131124] using wordTrace_append hprefix tailTrace_3131124
  have hstable : (prefixWord ++ tailWord_3131124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131124).length < 2 ^ (prefixWord ++ tailWord_3131124).sum := by decide
  have hdescent : baseEnd_3131124 < baseStart_3131124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131182 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3131182 : Nat := 118140960795 + 3131182 * 2 ^ 59
def prefixEnd_3131182 : Nat := 4983230072969 + 3 ^ 40 * 3131182 * 2
def baseEnd_3131182 : Nat := 357289196156994104383325

theorem tailTrace_3131182 : CollatzResearch.WordTrace tailWord_3131182 prefixEnd_3131182 357289196156994104383325 := by
  unfold tailWord_3131182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275448717783731519503475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76135726494846568104018533 14275448717783731519503475)
  ·
    refine ⟨21413173076675597279255213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14275448717783731519503475 21413173076675597279255213)
    ·
      refine ⟨8029939903753348979720705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21413173076675597279255213 8029939903753348979720705)
      ·
        refine ⟨6022454927815011734790529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8029939903753348979720705 6022454927815011734790529)
        ·
          refine ⟨4516841195861258801092897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6022454927815011734790529 4516841195861258801092897)
          ·
            refine ⟨3387630896895944100819673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4516841195861258801092897 3387630896895944100819673)
            ·
              refine ⟨2540723172671958075614755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387630896895944100819673 2540723172671958075614755)
              ·
                refine ⟨3811084759007937113422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540723172671958075614755 3811084759007937113422133)
                ·
                  refine ⟨357289196156994104383325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811084759007937113422133 357289196156994104383325)
                  ·
                    rfl

theorem cell22_3131182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3131182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131182 prefixEnd_3131182 := by exact prefixLift 3131182
  have htrace : WordTrace (prefixWord ++ tailWord_3131182) baseStart_3131182 baseEnd_3131182 := by
    simpa [prefixWord, tailWord_3131182, baseEnd_3131182] using wordTrace_append hprefix tailTrace_3131182
  have hstable : (prefixWord ++ tailWord_3131182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131182).length < 2 ^ (prefixWord ++ tailWord_3131182).sum := by decide
  have hdescent : baseEnd_3131182 < baseStart_3131182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131191 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 6, 3]
def baseStart_3131191 : Nat := 118140960795 + 3131191 * 2 ^ 59
def prefixEnd_3131191 : Nat := 4983230072969 + 3 ^ 40 * 3131191 * 2
def baseEnd_3131191 : Nat := 1071870669354909289674947

theorem tailTrace_3131191 : CollatzResearch.WordTrace tailWord_3131191 prefixEnd_3131191 1071870669354909289674947 := by
  unfold tailWord_3131191
  simp only [CollatzResearch.WordTrace]
  refine ⟨114203917999237246693105427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76135945332824831128736951 114203917999237246693105427)
  ·
    refine ⟨171305876998855870039658141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114203917999237246693105427 171305876998855870039658141)
    ·
      refine ⟨64239703874570951264871803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171305876998855870039658141 64239703874570951264871803)
      ·
        refine ⟨96359555811856426897307705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64239703874570951264871803 96359555811856426897307705)
        ·
          refine ⟨72269666858892320172980779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96359555811856426897307705 72269666858892320172980779)
          ·
            refine ⟨108404500288338480259471169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72269666858892320172980779 108404500288338480259471169)
            ·
              refine ⟨81303375216253860194603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108404500288338480259471169 81303375216253860194603377)
              ·
                refine ⟨60977531412190395145952533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81303375216253860194603377 60977531412190395145952533)
                ·
                  refine ⟨2858321784946424772466525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60977531412190395145952533 2858321784946424772466525)
                  ·
                    refine ⟨1071870669354909289674947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858321784946424772466525 1071870669354909289674947)
                    ·
                      rfl

theorem cell22_3131191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_3131191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131191 prefixEnd_3131191 := by exact prefixLift 3131191
  have htrace : WordTrace (prefixWord ++ tailWord_3131191) baseStart_3131191 baseEnd_3131191 := by
    simpa [prefixWord, tailWord_3131191, baseEnd_3131191] using wordTrace_append hprefix tailTrace_3131191
  have hstable : (prefixWord ++ tailWord_3131191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131191).length < 2 ^ (prefixWord ++ tailWord_3131191).sum := by decide
  have hdescent : baseEnd_3131191 < baseStart_3131191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131281 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3131281 : Nat := 118140960795 + 3131281 * 2 ^ 59
def prefixEnd_3131281 : Nat := 4983230072969 + 3 ^ 40 * 3131281 * 2
def baseEnd_3131281 : Nat := 1071901478194179054924671

theorem tailTrace_3131281 : CollatzResearch.WordTrace tailWord_3131281 prefixEnd_3131281 1071901478194179054924671 := by
  unfold tailWord_3131281
  simp only [CollatzResearch.WordTrace]
  refine ⟨114207200568911192063881697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76138133712607461375921131 114207200568911192063881697)
  ·
    refine ⟨85655400426683394047911273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114207200568911192063881697 85655400426683394047911273)
    ·
      refine ⟨64241550320012545535933455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85655400426683394047911273 64241550320012545535933455)
      ·
        refine ⟨96362325480018818303900183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64241550320012545535933455 96362325480018818303900183)
        ·
          refine ⟨144543488220028227455850275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96362325480018818303900183 144543488220028227455850275)
          ·
            refine ⟨216815232330042341183775413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144543488220028227455850275 216815232330042341183775413)
            ·
              refine ⟨20326428030941469485978945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216815232330042341183775413 20326428030941469485978945)
              ·
                refine ⟨15244821023206102114484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20326428030941469485978945 15244821023206102114484209)
                ·
                  refine ⟨11433615767404576585863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15244821023206102114484209 11433615767404576585863157)
                  ·
                    refine ⟨1071901478194179054924671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11433615767404576585863157 1071901478194179054924671)
                    ·
                      rfl

theorem cell22_3131281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3131281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131281 prefixEnd_3131281 := by exact prefixLift 3131281
  have htrace : WordTrace (prefixWord ++ tailWord_3131281) baseStart_3131281 baseEnd_3131281 := by
    simpa [prefixWord, tailWord_3131281, baseEnd_3131281] using wordTrace_append hprefix tailTrace_3131281
  have hstable : (prefixWord ++ tailWord_3131281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131281).length < 2 ^ (prefixWord ++ tailWord_3131281).sum := by decide
  have hdescent : baseEnd_3131281 < baseStart_3131281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131300 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_3131300 : Nat := 118140960795 + 3131300 * 2 ^ 59
def prefixEnd_3131300 : Nat := 4983230072969 + 3 ^ 40 * 3131300 * 2
def baseEnd_3131300 : Nat := 357302660760823112899871

theorem tailTrace_3131300 : CollatzResearch.WordTrace tailWord_3131300 prefixEnd_3131300 357302660760823112899871 := by
  unfold tailWord_3131300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57103946777921179154411677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76138595703894905539215569 57103946777921179154411677)
  ·
    refine ⟨21413980041720442182904379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57103946777921179154411677 21413980041720442182904379)
    ·
      refine ⟨32120970062580663274356569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21413980041720442182904379 32120970062580663274356569)
      ·
        refine ⟨24090727546935497455767427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32120970062580663274356569 24090727546935497455767427)
        ·
          refine ⟨36136091320403246183651141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24090727546935497455767427 36136091320403246183651141)
          ·
            refine ⟨6775517122575608659434589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36136091320403246183651141 6775517122575608659434589)
            ·
              refine ⟨2540818920965853247287971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6775517122575608659434589 2540818920965853247287971)
              ·
                refine ⟨3811228381448779870931957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540818920965853247287971 3811228381448779870931957)
                ·
                  refine ⟨357302660760823112899871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811228381448779870931957 357302660760823112899871)
                  ·
                    rfl

theorem cell22_3131300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_3131300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131300 prefixEnd_3131300 := by exact prefixLift 3131300
  have htrace : WordTrace (prefixWord ++ tailWord_3131300) baseStart_3131300 baseEnd_3131300 := by
    simpa [prefixWord, tailWord_3131300, baseEnd_3131300] using wordTrace_append hprefix tailTrace_3131300
  have hstable : (prefixWord ++ tailWord_3131300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131300).length < 2 ^ (prefixWord ++ tailWord_3131300).sum := by decide
  have hdescent : baseEnd_3131300 < baseStart_3131300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131311 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 6]
def baseStart_3131311 : Nat := 118140960795 + 3131311 * 2 ^ 59
def prefixEnd_3131311 : Nat := 4983230072969 + 3 ^ 40 * 3131311 * 2
def baseEnd_3131311 : Nat := 357303915935756325558193

theorem tailTrace_3131311 : CollatzResearch.WordTrace tailWord_3131311 prefixEnd_3131311 357303915935756325558193 := by
  unfold tailWord_3131311
  simp only [CollatzResearch.WordTrace]
  refine ⟨114208294758802507187473787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76138863172535004791649191 114208294758802507187473787)
  ·
    refine ⟨171312442138203760781210681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114208294758802507187473787 171312442138203760781210681)
    ·
      refine ⟨128484331603652820585908011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171312442138203760781210681 128484331603652820585908011)
      ·
        refine ⟨192726497405479230878862017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128484331603652820585908011 192726497405479230878862017)
        ·
          refine ⟨144544873054109423159146513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192726497405479230878862017 144544873054109423159146513)
          ·
            refine ⟨108408654790582067369359885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144544873054109423159146513 108408654790582067369359885)
            ·
              refine ⟨40653245546468275263509957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108408654790582067369359885 40653245546468275263509957)
              ·
                refine ⟨7622483539962801611908117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40653245546468275263509957 7622483539962801611908117)
                ·
                  refine ⟨357303915935756325558193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7622483539962801611908117 357303915935756325558193)
                  ·
                    rfl

theorem cell22_3131311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_3131311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131311 prefixEnd_3131311 := by exact prefixLift 3131311
  have htrace : WordTrace (prefixWord ++ tailWord_3131311) baseStart_3131311 baseEnd_3131311 := by
    simpa [prefixWord, tailWord_3131311, baseEnd_3131311] using wordTrace_append hprefix tailTrace_3131311
  have hstable : (prefixWord ++ tailWord_3131311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131311).length < 2 ^ (prefixWord ++ tailWord_3131311).sum := by decide
  have hdescent : baseEnd_3131311 < baseStart_3131311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131343 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 4, 3]
def baseStart_3131343 : Nat := 118140960795 + 3131343 * 2 ^ 59
def prefixEnd_3131343 : Nat := 4983230072969 + 3 ^ 40 * 3131343 * 2
def baseEnd_3131343 : Nat := 1071922702061231559874481

theorem tailTrace_3131343 : CollatzResearch.WordTrace tailWord_3131343 prefixEnd_3131343 1071922702061231559874481 := by
  unfold tailWord_3131343
  simp only [CollatzResearch.WordTrace]
  refine ⟨114209461894686576652638683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76139641263124384435092455 114209461894686576652638683)
  ·
    refine ⟨171314192842029864978958025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114209461894686576652638683 171314192842029864978958025)
    ·
      refine ⟨128485644631522398734218519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171314192842029864978958025 128485644631522398734218519)
      ·
        refine ⟨192728466947283598101327779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128485644631522398734218519 192728466947283598101327779)
        ·
          refine ⟨289092700420925397151991669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192728466947283598101327779 289092700420925397151991669)
          ·
            refine ⟨27102440664461755982999219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289092700420925397151991669 27102440664461755982999219)
            ·
              refine ⟨40653660996692633974498829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27102440664461755982999219 40653660996692633974498829)
              ·
                refine ⟨15245122873759737740437061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40653660996692633974498829 15245122873759737740437061)
                ·
                  refine ⟨2858460538829950826331949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15245122873759737740437061 2858460538829950826331949)
                  ·
                    refine ⟨1071922702061231559874481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858460538829950826331949 1071922702061231559874481)
                    ·
                      rfl

theorem cell22_3131343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_3131343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131343 prefixEnd_3131343 := by exact prefixLift 3131343
  have htrace : WordTrace (prefixWord ++ tailWord_3131343) baseStart_3131343 baseEnd_3131343 := by
    simpa [prefixWord, tailWord_3131343, baseEnd_3131343] using wordTrace_append hprefix tailTrace_3131343
  have hstable : (prefixWord ++ tailWord_3131343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131343).length < 2 ^ (prefixWord ++ tailWord_3131343).sum := by decide
  have hdescent : baseEnd_3131343 < baseStart_3131343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131371 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_3131371 : Nat := 118140960795 + 3131371 * 2 ^ 59
def prefixEnd_3131371 : Nat := 4983230072969 + 3 ^ 40 * 3131371 * 2
def baseEnd_3131371 : Nat := 1071932287033448820174395

theorem tailTrace_3131371 : CollatzResearch.WordTrace tailWord_3131371 prefixEnd_3131371 1071932287033448820174395 := by
  unfold tailWord_3131371
  simp only [CollatzResearch.WordTrace]
  refine ⟨114210483138585137434657967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76140322092390091623105311 114210483138585137434657967)
  ·
    refine ⟨171315724707877706151986951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114210483138585137434657967 171315724707877706151986951)
    ·
      refine ⟨256973587061816559227980427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171315724707877706151986951 256973587061816559227980427)
      ·
        refine ⟨385460380592724838841970641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256973587061816559227980427 385460380592724838841970641)
        ·
          refine ⟨289095285444543629131477981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385460380592724838841970641 289095285444543629131477981)
          ·
            refine ⟨108410732041703860924304243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289095285444543629131477981 108410732041703860924304243)
            ·
              refine ⟨162616098062555791386456365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108410732041703860924304243 162616098062555791386456365)
              ·
                refine ⟨60981036773458421769921137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162616098062555791386456365 60981036773458421769921137)
                ·
                  refine ⟨45735777580093816327440853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60981036773458421769921137 45735777580093816327440853)
                  ·
                    refine ⟨1071932287033448820174395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45735777580093816327440853 1071932287033448820174395)
                    ·
                      rfl

theorem cell22_3131371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_3131371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131371 prefixEnd_3131371 := by exact prefixLift 3131371
  have htrace : WordTrace (prefixWord ++ tailWord_3131371) baseStart_3131371 baseEnd_3131371 := by
    simpa [prefixWord, tailWord_3131371, baseEnd_3131371] using wordTrace_append hprefix tailTrace_3131371
  have hstable : (prefixWord ++ tailWord_3131371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131371).length < 2 ^ (prefixWord ++ tailWord_3131371).sum := by decide
  have hdescent : baseEnd_3131371 < baseStart_3131371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131396 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_3131396 : Nat := 118140960795 + 3131396 * 2 ^ 59
def prefixEnd_3131396 : Nat := 4983230072969 + 3 ^ 40 * 3131396 * 2
def baseEnd_3131396 : Nat := 357313615014785696099773

theorem tailTrace_3131396 : CollatzResearch.WordTrace tailWord_3131396 prefixEnd_3131396 357313615014785696099773 := by
  unfold tailWord_3131396
  simp only [CollatzResearch.WordTrace]
  refine ⟨57105697481747283352159021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76140929975663044469545361 57105697481747283352159021)
  ·
    refine ⟨21414636555655231257059633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57105697481747283352159021 21414636555655231257059633)
    ·
      refine ⟨16060977416741423442794725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21414636555655231257059633 16060977416741423442794725)
      ·
        refine ⟨3011433265639016895524011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16060977416741423442794725 3011433265639016895524011)
        ·
          refine ⟨4517149898458525343286017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011433265639016895524011 4517149898458525343286017)
          ·
            refine ⟨3387862423843894007464513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517149898458525343286017 3387862423843894007464513)
            ·
              refine ⟨2540896817882920505598385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387862423843894007464513 2540896817882920505598385)
              ·
                refine ⟨1905672613412190379198789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540896817882920505598385 1905672613412190379198789)
                ·
                  refine ⟨357313615014785696099773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905672613412190379198789 357313615014785696099773)
                  ·
                    rfl

theorem cell22_3131396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_3131396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131396 prefixEnd_3131396 := by exact prefixLift 3131396
  have htrace : WordTrace (prefixWord ++ tailWord_3131396) baseStart_3131396 baseEnd_3131396 := by
    simpa [prefixWord, tailWord_3131396, baseEnd_3131396] using wordTrace_append hprefix tailTrace_3131396
  have hstable : (prefixWord ++ tailWord_3131396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131396).length < 2 ^ (prefixWord ++ tailWord_3131396).sum := by decide
  have hdescent : baseEnd_3131396 < baseStart_3131396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131495 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3131495 : Nat := 118140960795 + 3131495 * 2 ^ 59
def prefixEnd_3131495 : Nat := 4983230072969 + 3 ^ 40 * 3131495 * 2
def baseEnd_3131495 : Nat := 1071974734767553830074015

theorem tailTrace_3131495 : CollatzResearch.WordTrace tailWord_3131495 prefixEnd_3131495 1071974734767553830074015 := by
  unfold tailWord_3131495
  simp only [CollatzResearch.WordTrace]
  refine ⟨114215005790135906612171939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76143337193423937741447959 114215005790135906612171939)
  ·
    refine ⟨171322508685203859918257909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114215005790135906612171939 171322508685203859918257909)
    ·
      refine ⟨16061485189237861867336679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171322508685203859918257909 16061485189237861867336679)
      ·
        refine ⟨24092227783856792801005019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061485189237861867336679 24092227783856792801005019)
        ·
          refine ⟨36138341675785189201507529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24092227783856792801005019 36138341675785189201507529)
          ·
            refine ⟨27103756256838891901130647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36138341675785189201507529 27103756256838891901130647)
            ·
              refine ⟨40655634385258337851695971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27103756256838891901130647 40655634385258337851695971)
              ·
                refine ⟨60983451577887506777543957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40655634385258337851695971 60983451577887506777543957)
                ·
                  refine ⟨2858599292713476880197373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60983451577887506777543957 2858599292713476880197373)
                  ·
                    refine ⟨1071974734767553830074015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858599292713476880197373 1071974734767553830074015)
                    ·
                      rfl

theorem cell22_3131495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3131495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131495 prefixEnd_3131495 := by exact prefixLift 3131495
  have htrace : WordTrace (prefixWord ++ tailWord_3131495) baseStart_3131495 baseEnd_3131495 := by
    simpa [prefixWord, tailWord_3131495, baseEnd_3131495] using wordTrace_append hprefix tailTrace_3131495
  have hstable : (prefixWord ++ tailWord_3131495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131495).length < 2 ^ (prefixWord ++ tailWord_3131495).sum := by decide
  have hdescent : baseEnd_3131495 < baseStart_3131495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131525 : List Nat := [1, 3, 1, 1, 5, 2, 2, 7]
def baseStart_3131525 : Nat := 118140960795 + 3131525 * 2 ^ 59
def prefixEnd_3131525 : Nat := 4983230072969 + 3 ^ 40 * 3131525 * 2
def baseEnd_3131525 : Nat := 119109444931182639091547

theorem tailTrace_3131525 : CollatzResearch.WordTrace tailWord_3131525 prefixEnd_3131525 119109444931182639091547 := by
  unfold tailWord_3131525
  simp only [CollatzResearch.WordTrace]
  refine ⟨114216099980027221735764029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76144066653351481157176019 114216099980027221735764029)
  ·
    refine ⟨42831037492510208150911511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114216099980027221735764029 42831037492510208150911511)
    ·
      refine ⟨64246556238765312226367267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42831037492510208150911511 64246556238765312226367267)
      ·
        refine ⟨96369834358147968339550901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64246556238765312226367267 96369834358147968339550901)
        ·
          refine ⟨9034671971076372031832897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96369834358147968339550901 9034671971076372031832897)
          ·
            refine ⟨6776003978307279023874673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9034671971076372031832897 6776003978307279023874673)
            ·
              refine ⟨5082002983730459267906005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776003978307279023874673 5082002983730459267906005)
              ·
                refine ⟨119109444931182639091547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5082002983730459267906005 119109444931182639091547)
                ·
                  rfl

theorem cell22_3131525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 7].length) (baseStart_3131525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131525 prefixEnd_3131525 := by exact prefixLift 3131525
  have htrace : WordTrace (prefixWord ++ tailWord_3131525) baseStart_3131525 baseEnd_3131525 := by
    simpa [prefixWord, tailWord_3131525, baseEnd_3131525] using wordTrace_append hprefix tailTrace_3131525
  have hstable : (prefixWord ++ tailWord_3131525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131525).length < 2 ^ (prefixWord ++ tailWord_3131525).sum := by decide
  have hdescent : baseEnd_3131525 < baseStart_3131525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131617 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3131617 : Nat := 118140960795 + 3131617 * 2 ^ 59
def prefixEnd_3131617 : Nat := 4983230072969 + 3 ^ 40 * 3131617 * 2
def baseEnd_3131617 : Nat := 1072016497860786178523641

theorem tailTrace_3131617 : CollatzResearch.WordTrace tailWord_3131617 prefixEnd_3131617 1072016497860786178523641 := by
  unfold tailWord_3131617
  simp only [CollatzResearch.WordTrace]
  refine ⟨114219455495693921448113105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76146303663795947632075403 114219455495693921448113105)
  ·
    refine ⟨85664591621770441086084829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114219455495693921448113105 85664591621770441086084829)
    ·
      refine ⟨32124221858163915407281811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85664591621770441086084829 32124221858163915407281811)
      ·
        refine ⟨48186332787245873110922717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32124221858163915407281811 48186332787245873110922717)
        ·
          refine ⟨18069874795217202416596019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48186332787245873110922717 18069874795217202416596019)
          ·
            refine ⟨27104812192825803624894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069874795217202416596019 27104812192825803624894029)
            ·
              refine ⟨10164304572309676359335261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27104812192825803624894029 10164304572309676359335261)
              ·
                refine ⟨3811614214616128634750723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164304572309676359335261 3811614214616128634750723)
                ·
                  refine ⟨5717421321924192952126085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811614214616128634750723 5717421321924192952126085)
                  ·
                    refine ⟨1072016497860786178523641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717421321924192952126085 1072016497860786178523641)
                    ·
                      rfl

theorem cell22_3131617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3131617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131617 prefixEnd_3131617 := by exact prefixLift 3131617
  have htrace : WordTrace (prefixWord ++ tailWord_3131617) baseStart_3131617 baseEnd_3131617 := by
    simpa [prefixWord, tailWord_3131617, baseEnd_3131617] using wordTrace_append hprefix tailTrace_3131617
  have hstable : (prefixWord ++ tailWord_3131617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131617).length < 2 ^ (prefixWord ++ tailWord_3131617).sum := by decide
  have hdescent : baseEnd_3131617 < baseStart_3131617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131660 : List Nat := [2, 2, 1, 2, 2, 2, 3, 8]
def baseStart_3131660 : Nat := 118140960795 + 3131660 * 2 ^ 59
def prefixEnd_3131660 : Nat := 4983230072969 + 3 ^ 40 * 3131660 * 2
def baseEnd_3131660 : Nat := 119114579737727599966501

theorem tailTrace_3131660 : CollatzResearch.WordTrace tailWord_3131660 prefixEnd_3131660 119114579737727599966501 := by
  unfold tailWord_3131660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57110511917269069895964217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76147349223025426527952289 57110511917269069895964217)
  ·
    refine ⟨42832883937951802421973163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57110511917269069895964217 42832883937951802421973163)
    ·
      refine ⟨64249325906927703632959745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42832883937951802421973163 64249325906927703632959745)
      ·
        refine ⟨48186994430195777724719809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64249325906927703632959745 48186994430195777724719809)
        ·
          refine ⟨36140245822646833293539857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48186994430195777724719809 36140245822646833293539857)
          ·
            refine ⟨27105184366985124970154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36140245822646833293539857 27105184366985124970154893)
            ·
              refine ⟨10164444137619421863808085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27105184366985124970154893 10164444137619421863808085)
              ·
                refine ⟨119114579737727599966501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10164444137619421863808085 119114579737727599966501)
                ·
                  rfl

theorem cell22_3131660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_3131660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131660 prefixEnd_3131660 := by exact prefixLift 3131660
  have htrace : WordTrace (prefixWord ++ tailWord_3131660) baseStart_3131660 baseEnd_3131660 := by
    simpa [prefixWord, tailWord_3131660, baseEnd_3131660] using wordTrace_append hprefix tailTrace_3131660
  have hstable : (prefixWord ++ tailWord_3131660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131660).length < 2 ^ (prefixWord ++ tailWord_3131660).sum := by decide
  have hdescent : baseEnd_3131660 < baseStart_3131660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131662 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3131662 : Nat := 118140960795 + 3131662 * 2 ^ 59
def prefixEnd_3131662 : Nat := 4983230072969 + 3 ^ 40 * 3131662 * 2
def baseEnd_3131662 : Nat := 1072031902280421061148503

theorem tailTrace_3131662 : CollatzResearch.WordTrace tailWord_3131662 prefixEnd_3131662 1072031902280421061148503 := by
  unfold tailWord_3131662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277637097566361766687655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76147397853687262755667493 14277637097566361766687655)
  ·
    refine ⟨21416455646349542650031483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277637097566361766687655 21416455646349542650031483)
    ·
      refine ⟨32124683469524313975047225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21416455646349542650031483 32124683469524313975047225)
      ·
        refine ⟨24093512602143235481285419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32124683469524313975047225 24093512602143235481285419)
        ·
          refine ⟨36140268903214853221928129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24093512602143235481285419 36140268903214853221928129)
          ·
            refine ⟨27105201677411139916446097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36140268903214853221928129 27105201677411139916446097)
            ·
              refine ⟨20328901258058354937334573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27105201677411139916446097 20328901258058354937334573)
              ·
                refine ⟨7623337971771883101500465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20328901258058354937334573 7623337971771883101500465)
                ·
                  refine ⟨5717503478828912326125349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7623337971771883101500465 5717503478828912326125349)
                  ·
                    refine ⟨1072031902280421061148503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717503478828912326125349 1072031902280421061148503)
                    ·
                      rfl

theorem cell22_3131662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3131662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131662 prefixEnd_3131662 := by exact prefixLift 3131662
  have htrace : WordTrace (prefixWord ++ tailWord_3131662) baseStart_3131662 baseEnd_3131662 := by
    simpa [prefixWord, tailWord_3131662, baseEnd_3131662] using wordTrace_append hprefix tailTrace_3131662
  have hstable : (prefixWord ++ tailWord_3131662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131662).length < 2 ^ (prefixWord ++ tailWord_3131662).sum := by decide
  have hdescent : baseEnd_3131662 < baseStart_3131662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131698 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3131698 : Nat := 118140960795 + 3131698 * 2 ^ 59
def prefixEnd_3131698 : Nat := 4983230072969 + 3 ^ 40 * 3131698 * 2
def baseEnd_3131698 : Nat := 1072044225816128967248393

theorem tailTrace_3131698 : CollatzResearch.WordTrace tailWord_3131698 prefixEnd_3131698 1072044225816128967248393 := by
  unfold tailWord_3131698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555602452100118070452937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76148273205600314854541165 28555602452100118070452937)
  ·
    refine ⟨21416701839075088552839703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28555602452100118070452937 21416701839075088552839703)
    ·
      refine ⟨32125052758612632829259555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21416701839075088552839703 32125052758612632829259555)
      ·
        refine ⟨48187579137918949243889333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32125052758612632829259555 48187579137918949243889333)
        ·
          refine ⟨4517585544179901491614625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48187579137918949243889333 4517585544179901491614625)
          ·
            refine ⟨3388189158134926118710969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517585544179901491614625 3388189158134926118710969)
            ·
              refine ⟨2541141868601194589033227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388189158134926118710969 2541141868601194589033227)
              ·
                refine ⟨3811712802901791883549841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541141868601194589033227 3811712802901791883549841)
                ·
                  refine ⟨2858784602176343912662381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3811712802901791883549841 2858784602176343912662381)
                  ·
                    refine ⟨1072044225816128967248393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858784602176343912662381 1072044225816128967248393)
                    ·
                      rfl

theorem cell22_3131698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3131698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131698 prefixEnd_3131698 := by exact prefixLift 3131698
  have htrace : WordTrace (prefixWord ++ tailWord_3131698) baseStart_3131698 baseEnd_3131698 := by
    simpa [prefixWord, tailWord_3131698, baseEnd_3131698] using wordTrace_append hprefix tailTrace_3131698
  have hstable : (prefixWord ++ tailWord_3131698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131698).length < 2 ^ (prefixWord ++ tailWord_3131698).sum := by decide
  have hdescent : baseEnd_3131698 < baseStart_3131698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131754 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3131754 : Nat := 118140960795 + 3131754 * 2 ^ 59
def prefixEnd_3131754 : Nat := 4983230072969 + 3 ^ 40 * 3131754 * 2
def baseEnd_3131754 : Nat := 1072063395760563487848221

theorem tailTrace_3131754 : CollatzResearch.WordTrace tailWord_3131754 prefixEnd_3131754 1072063395760563487848221 := by
  unfold tailWord_3131754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28556113074049398461462579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76149634864131729230566877 28556113074049398461462579)
  ·
    refine ⟨42834169611074097692193869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28556113074049398461462579 42834169611074097692193869)
    ·
      refine ⟨16062813604152786634572701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42834169611074097692193869 16062813604152786634572701)
      ·
        refine ⟨6023555101557294987964763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16062813604152786634572701 6023555101557294987964763)
        ·
          refine ⟨9035332652335942481947145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023555101557294987964763 9035332652335942481947145)
          ·
            refine ⟨6776499489251956861460359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9035332652335942481947145 6776499489251956861460359)
            ·
              refine ⟨10164749233877935292190539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776499489251956861460359 10164749233877935292190539)
              ·
                refine ⟨15247123850816902938285809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164749233877935292190539 15247123850816902938285809)
                ·
                  refine ⟨11435342888112677203714357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15247123850816902938285809 11435342888112677203714357)
                  ·
                    refine ⟨1072063395760563487848221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11435342888112677203714357 1072063395760563487848221)
                    ·
                      rfl

theorem cell22_3131754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3131754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131754 prefixEnd_3131754 := by exact prefixLift 3131754
  have htrace : WordTrace (prefixWord ++ tailWord_3131754) baseStart_3131754 baseEnd_3131754 := by
    simpa [prefixWord, tailWord_3131754, baseEnd_3131754] using wordTrace_append hprefix tailTrace_3131754
  have hstable : (prefixWord ++ tailWord_3131754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131754).length < 2 ^ (prefixWord ++ tailWord_3131754).sum := by decide
  have hdescent : baseEnd_3131754 < baseStart_3131754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131797 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3131797 : Nat := 118140960795 + 3131797 * 2 ^ 59
def prefixEnd_3131797 : Nat := 4983230072969 + 3 ^ 40 * 3131797 * 2
def baseEnd_3131797 : Nat := 1072078115539325709023089

theorem tailTrace_3131797 : CollatzResearch.WordTrace tailWord_3131797 prefixEnd_3131797 1072078115539325709023089 := by
  unfold tailWord_3131797
  simp only [CollatzResearch.WordTrace]
  refine ⟨114226020635041812189665645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76150680423361208126443763 114226020635041812189665645)
  ·
    refine ⟨42834757738140679571124617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114226020635041812189665645 42834757738140679571124617)
    ·
      refine ⟨32126068303605509678343463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42834757738140679571124617 32126068303605509678343463)
      ·
        refine ⟨48189102455408264517515195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32126068303605509678343463 48189102455408264517515195)
        ·
          refine ⟨72283653683112396776272793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48189102455408264517515195 72283653683112396776272793)
          ·
            refine ⟨54212740262334297582204595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72283653683112396776272793 54212740262334297582204595)
            ·
              refine ⟨81319110393501446373306893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54212740262334297582204595 81319110393501446373306893)
              ·
                refine ⟨30494666397563042389990085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81319110393501446373306893 30494666397563042389990085)
                ·
                  refine ⟨5717749949543070448123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30494666397563042389990085 5717749949543070448123141)
                  ·
                    refine ⟨1072078115539325709023089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717749949543070448123141 1072078115539325709023089)
                    ·
                      rfl

theorem cell22_3131797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3131797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131797 prefixEnd_3131797 := by exact prefixLift 3131797
  have htrace : WordTrace (prefixWord ++ tailWord_3131797) baseStart_3131797 baseEnd_3131797 := by
    simpa [prefixWord, tailWord_3131797, baseEnd_3131797] using wordTrace_append hprefix tailTrace_3131797
  have hstable : (prefixWord ++ tailWord_3131797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131797).length < 2 ^ (prefixWord ++ tailWord_3131797).sum := by decide
  have hdescent : baseEnd_3131797 < baseStart_3131797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131816 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3131816 : Nat := 118140960795 + 3131816 * 2 ^ 59
def prefixEnd_3131816 : Nat := 4983230072969 + 3 ^ 40 * 3131816 * 2
def baseEnd_3131816 : Nat := 1072084619627615992798031

theorem tailTrace_3131816 : CollatzResearch.WordTrace tailWord_3131816 prefixEnd_3131816 1072084619627615992798031 := by
  unfold tailWord_3131816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57113356810986489217303651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76151142414648652289738201 57113356810986489217303651)
  ·
    refine ⟨85670035216479733825955477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57113356810986489217303651 85670035216479733825955477)
    ·
      refine ⟨4015782900772487523091663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85670035216479733825955477 4015782900772487523091663)
      ·
        refine ⟨6023674351158731284637495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015782900772487523091663 6023674351158731284637495)
        ·
          refine ⟨9035511526738096926956243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023674351158731284637495 9035511526738096926956243)
          ·
            refine ⟨13553267290107145390434365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035511526738096926956243 13553267290107145390434365)
            ·
              refine ⟨5082475233790179521412887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13553267290107145390434365 5082475233790179521412887)
              ·
                refine ⟨7623712850685269282119331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082475233790179521412887 7623712850685269282119331)
                ·
                  refine ⟨11435569276027903923178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623712850685269282119331 11435569276027903923178997)
                  ·
                    refine ⟨1072084619627615992798031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11435569276027903923178997 1072084619627615992798031)
                    ·
                      rfl

theorem cell22_3131816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3131816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131816 prefixEnd_3131816 := by exact prefixLift 3131816
  have htrace : WordTrace (prefixWord ++ tailWord_3131816) baseStart_3131816 baseEnd_3131816 := by
    simpa [prefixWord, tailWord_3131816, baseEnd_3131816] using wordTrace_append hprefix tailTrace_3131816
  have hstable : (prefixWord ++ tailWord_3131816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131816).length < 2 ^ (prefixWord ++ tailWord_3131816).sum := by decide
  have hdescent : baseEnd_3131816 < baseStart_3131816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131829 : List Nat := [1, 3, 3, 2, 3, 1, 1, 8]
def baseStart_3131829 : Nat := 118140960795 + 3131829 * 2 ^ 59
def prefixEnd_3131829 : Nat := 4983230072969 + 3 ^ 40 * 3131829 * 2
def baseEnd_3131829 : Nat := 119121007754809810246999

theorem tailTrace_3131829 : CollatzResearch.WordTrace tailWord_3131829 prefixEnd_3131829 119121007754809810246999 := by
  unfold tailWord_3131829
  simp only [CollatzResearch.WordTrace]
  refine ⟨114227187770925881654830541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76151458513950587769887027 114227187770925881654830541)
  ·
    refine ⟨42835195414097205620561453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114227187770925881654830541 42835195414097205620561453)
    ·
      refine ⟨16063198280286452107710545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42835195414097205620561453 16063198280286452107710545)
      ·
        refine ⟨12047398710214839080782909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16063198280286452107710545 12047398710214839080782909)
        ·
          refine ⟨4517774516330564655293591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12047398710214839080782909 4517774516330564655293591)
          ·
            refine ⟨6776661774495846982940387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517774516330564655293591 6776661774495846982940387)
            ·
              refine ⟨10164992661743770474410581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776661774495846982940387 10164992661743770474410581)
              ·
                refine ⟨119121007754809810246999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10164992661743770474410581 119121007754809810246999)
                ·
                  rfl

theorem cell22_3131829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 8].length) (baseStart_3131829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131829 prefixEnd_3131829 := by exact prefixLift 3131829
  have htrace : WordTrace (prefixWord ++ tailWord_3131829) baseStart_3131829 baseEnd_3131829 := by
    simpa [prefixWord, tailWord_3131829, baseEnd_3131829] using wordTrace_append hprefix tailTrace_3131829
  have hstable : (prefixWord ++ tailWord_3131829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131829).length < 2 ^ (prefixWord ++ tailWord_3131829).sum := by decide
  have hdescent : baseEnd_3131829 < baseStart_3131829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131861 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_3131861 : Nat := 118140960795 + 3131861 * 2 ^ 59
def prefixEnd_3131861 : Nat := 4983230072969 + 3 ^ 40 * 3131861 * 2
def baseEnd_3131861 : Nat := 1072100024047250875422893

theorem tailTrace_3131861 : CollatzResearch.WordTrace tailWord_3131861 prefixEnd_3131861 1072100024047250875422893 := by
  unfold tailWord_3131861
  simp only [CollatzResearch.WordTrace]
  refine ⟨114228354906809951119995437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76152236604539967413330291 114228354906809951119995437)
  ·
    refine ⟨42835633090053731669998289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114228354906809951119995437 42835633090053731669998289)
    ·
      refine ⟨32126724817540298752498717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42835633090053731669998289 32126724817540298752498717)
      ·
        refine ⟨12047521806577612032187019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32126724817540298752498717 12047521806577612032187019)
        ·
          refine ⟨18071282709866418048280529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12047521806577612032187019 18071282709866418048280529)
          ·
            refine ⟨13553462032399813536210397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18071282709866418048280529 13553462032399813536210397)
            ·
              refine ⟨5082548262149930076078899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13553462032399813536210397 5082548262149930076078899)
              ·
                refine ⟨7623822393224895114118349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082548262149930076078899 7623822393224895114118349)
                ·
                  refine ⟨2858933397459335667794381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7623822393224895114118349 2858933397459335667794381)
                  ·
                    refine ⟨1072100024047250875422893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858933397459335667794381 1072100024047250875422893)
                    ·
                      rfl

theorem cell22_3131861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_3131861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131861 prefixEnd_3131861 := by exact prefixLift 3131861
  have htrace : WordTrace (prefixWord ++ tailWord_3131861) baseStart_3131861 baseEnd_3131861 := by
    simpa [prefixWord, tailWord_3131861, baseEnd_3131861] using wordTrace_append hprefix tailTrace_3131861
  have hstable : (prefixWord ++ tailWord_3131861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131861).length < 2 ^ (prefixWord ++ tailWord_3131861).sum := by decide
  have hdescent : baseEnd_3131861 < baseStart_3131861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131872 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_3131872 : Nat := 118140960795 + 3131872 * 2 ^ 59
def prefixEnd_3131872 : Nat := 4983230072969 + 3 ^ 40 * 3131872 * 2
def baseEnd_3131872 : Nat := 1072103789572050513397859

theorem tailTrace_3131872 : CollatzResearch.WordTrace tailWord_3131872 prefixEnd_3131872 1072103789572050513397859 := by
  unfold tailWord_3131872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57114378054885049999322935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76152504073180066665763913 57114378054885049999322935)
  ·
    refine ⟨85671567082327574998984403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57114378054885049999322935 85671567082327574998984403)
    ·
      refine ⟨128507350623491362498476605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85671567082327574998984403 128507350623491362498476605)
      ·
        refine ⟨48190256483809260936928727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128507350623491362498476605 48190256483809260936928727)
        ·
          refine ⟨72285384725713891405393091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48190256483809260936928727 72285384725713891405393091)
          ·
            refine ⟨108428077088570837108089637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72285384725713891405393091 108428077088570837108089637)
            ·
              refine ⟨20330264454107031957766807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108428077088570837108089637 20330264454107031957766807)
              ·
                refine ⟨30495396681160547936650211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20330264454107031957766807 30495396681160547936650211)
                ·
                  refine ⟨45743095021740821904975317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30495396681160547936650211 45743095021740821904975317)
                  ·
                    refine ⟨1072103789572050513397859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45743095021740821904975317 1072103789572050513397859)
                    ·
                      rfl

theorem cell22_3131872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_3131872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131872 prefixEnd_3131872 := by exact prefixLift 3131872
  have htrace : WordTrace (prefixWord ++ tailWord_3131872) baseStart_3131872 baseEnd_3131872 := by
    simpa [prefixWord, tailWord_3131872, baseEnd_3131872] using wordTrace_append hprefix tailTrace_3131872
  have hstable : (prefixWord ++ tailWord_3131872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131872).length < 2 ^ (prefixWord ++ tailWord_3131872).sum := by decide
  have hdescent : baseEnd_3131872 < baseStart_3131872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131936 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_3131936 : Nat := 118140960795 + 3131936 * 2 ^ 59
def prefixEnd_3131936 : Nat := 4983230072969 + 3 ^ 40 * 3131936 * 2
def baseEnd_3131936 : Nat := 357375232693325226599221

theorem tailTrace_3131936 : CollatzResearch.WordTrace tailWord_3131936 prefixEnd_3131936 357375232693325226599221 := by
  unfold tailWord_3131936
  simp only [CollatzResearch.WordTrace]
  refine ⟨57115545190769119464487831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76154060254358825952650441 57115545190769119464487831)
  ·
    refine ⟨85673317786153679196731747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57115545190769119464487831 85673317786153679196731747)
    ·
      refine ⟨128509976679230518795097621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85673317786153679196731747 128509976679230518795097621)
      ·
        refine ⟨6023905156838930568520201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128509976679230518795097621 6023905156838930568520201)
        ·
          refine ⟨4517928867629197926390151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023905156838930568520201 4517928867629197926390151)
          ·
            refine ⟨6776893301443796889585227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517928867629197926390151 6776893301443796889585227)
            ·
              refine ⟨10165339952165695334377841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776893301443796889585227 10165339952165695334377841)
              ·
                refine ⟨7624004964124271500783381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165339952165695334377841 7624004964124271500783381)
                ·
                  refine ⟨357375232693325226599221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7624004964124271500783381 357375232693325226599221)
                  ·
                    rfl

theorem cell22_3131936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_3131936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131936 prefixEnd_3131936 := by exact prefixLift 3131936
  have htrace : WordTrace (prefixWord ++ tailWord_3131936) baseStart_3131936 baseEnd_3131936 := by
    simpa [prefixWord, tailWord_3131936, baseEnd_3131936] using wordTrace_append hprefix tailTrace_3131936
  have hstable : (prefixWord ++ tailWord_3131936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131936).length < 2 ^ (prefixWord ++ tailWord_3131936).sum := by decide
  have hdescent : baseEnd_3131936 < baseStart_3131936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131947 : List Nat := [1, 1, 1, 1, 2, 1, 3, 12]
def baseStart_3131947 : Nat := 118140960795 + 3131947 * 2 ^ 59
def prefixEnd_3131947 : Nat := 4983230072969 + 3 ^ 40 * 3131947 * 2
def baseEnd_3131947 : Nat := 119125495956086146419181

theorem tailTrace_3131947 : CollatzResearch.WordTrace tailWord_3131947 prefixEnd_3131947 119125495956086146419181 := by
  unfold tailWord_3131947
  simp only [CollatzResearch.WordTrace]
  refine ⟨114231491584498387807626095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76154327722998925205084063 114231491584498387807626095)
  ·
    refine ⟨171347237376747581711439143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114231491584498387807626095 171347237376747581711439143)
    ·
      refine ⟨257020856065121372567158715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171347237376747581711439143 257020856065121372567158715)
      ·
        refine ⟨385531284097682058850738073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257020856065121372567158715 385531284097682058850738073)
        ·
          refine ⟨289148463073261544138053555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385531284097682058850738073 289148463073261544138053555)
          ·
            refine ⟨433722694609892316207080333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289148463073261544138053555 433722694609892316207080333)
            ·
              refine ⟨162646010478709618577655125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433722694609892316207080333 162646010478709618577655125)
              ·
                refine ⟨119125495956086146419181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 162646010478709618577655125 119125495956086146419181)
                ·
                  rfl

theorem cell22_3131947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_3131947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131947 prefixEnd_3131947 := by exact prefixLift 3131947
  have htrace : WordTrace (prefixWord ++ tailWord_3131947) baseStart_3131947 baseEnd_3131947 := by
    simpa [prefixWord, tailWord_3131947, baseEnd_3131947] using wordTrace_append hprefix tailTrace_3131947
  have hstable : (prefixWord ++ tailWord_3131947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131947).length < 2 ^ (prefixWord ++ tailWord_3131947).sum := by decide
  have hdescent : baseEnd_3131947 < baseStart_3131947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131964 : List Nat := [2, 2, 2, 2, 3, 2, 9]
def baseStart_3131964 : Nat := 118140960795 + 3131964 * 2 ^ 59
def prefixEnd_3131964 : Nat := 4983230072969 + 3 ^ 40 * 3131964 * 2
def baseEnd_3131964 : Nat := 39708714187118257040651

theorem tailTrace_3131964 : CollatzResearch.WordTrace tailWord_3131964 prefixEnd_3131964 39708714187118257040651 := by
  unfold tailWord_3131964
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116055812718399855497473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76154741083624533140663297 57116055812718399855497473)
  ·
    refine ⟨42837041859538799891623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57116055812718399855497473 42837041859538799891623105)
    ·
      refine ⟨32127781394654099918717329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42837041859538799891623105 32127781394654099918717329)
      ·
        refine ⟨24095836045990574939037997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32127781394654099918717329 24095836045990574939037997)
        ·
          refine ⟨9035938517246465602139249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24095836045990574939037997 9035938517246465602139249)
          ·
            refine ⟨6776953887934849201604437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9035938517246465602139249 6776953887934849201604437)
            ·
              refine ⟨39708714187118257040651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6776953887934849201604437 39708714187118257040651)
              ·
                rfl

theorem cell22_3131964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 9].length) (baseStart_3131964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3131964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3131964 prefixEnd_3131964 := by exact prefixLift 3131964
  have htrace : WordTrace (prefixWord ++ tailWord_3131964) baseStart_3131964 baseEnd_3131964 := by
    simpa [prefixWord, tailWord_3131964, baseEnd_3131964] using wordTrace_append hprefix tailTrace_3131964
  have hstable : (prefixWord ++ tailWord_3131964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131964).length < 2 ^ (prefixWord ++ tailWord_3131964).sum := by decide
  have hdescent : baseEnd_3131964 < baseStart_3131964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132056 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3132056 : Nat := 118140960795 + 3132056 * 2 ^ 59
def prefixEnd_3132056 : Nat := 4983230072969 + 3 ^ 40 * 3132056 * 2
def baseEnd_3132056 : Nat := 1072166776532335366797295

theorem tailTrace_3132056 : CollatzResearch.WordTrace tailWord_3132056 prefixEnd_3132056 1072166776532335366797295 := by
  unfold tailWord_3132056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57117733570551749711672011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76156978094068999615562681 57117733570551749711672011)
  ·
    refine ⟨85676600355827624567508017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57117733570551749711672011 85676600355827624567508017)
    ·
      refine ⟨64257450266870718425631013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85676600355827624567508017 64257450266870718425631013)
      ·
        refine ⟨12048271925038259704805815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64257450266870718425631013 12048271925038259704805815)
        ·
          refine ⟨18072407887557389557208723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12048271925038259704805815 18072407887557389557208723)
          ·
            refine ⟨27108611831336084335813085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18072407887557389557208723 27108611831336084335813085)
            ·
              refine ⟨10165729436751031625929907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27108611831336084335813085 10165729436751031625929907)
              ·
                refine ⟨15248594155126547438894861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165729436751031625929907 15248594155126547438894861)
                ·
                  refine ⟨5718222808172455289585573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15248594155126547438894861 5718222808172455289585573)
                  ·
                    refine ⟨1072166776532335366797295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718222808172455289585573 1072166776532335366797295)
                    ·
                      rfl

theorem cell22_3132056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3132056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132056 prefixEnd_3132056 := by exact prefixLift 3132056
  have htrace : WordTrace (prefixWord ++ tailWord_3132056) baseStart_3132056 baseEnd_3132056 := by
    simpa [prefixWord, tailWord_3132056, baseEnd_3132056] using wordTrace_append hprefix tailTrace_3132056
  have hstable : (prefixWord ++ tailWord_3132056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132056).length < 2 ^ (prefixWord ++ tailWord_3132056).sum := by decide
  have hdescent : baseEnd_3132056 < baseStart_3132056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132081 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_3132081 : Nat := 118140960795 + 3132081 * 2 ^ 59
def prefixEnd_3132081 : Nat := 4983230072969 + 3 ^ 40 * 3132081 * 2
def baseEnd_3132081 : Nat := 1072175334543243634922219

theorem tailTrace_3132081 : CollatzResearch.WordTrace tailWord_3132081 prefixEnd_3132081 1072175334543243634922219 := by
  unfold tailWord_3132081
  simp only [CollatzResearch.WordTrace]
  refine ⟨114236378966012928693004097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76157585977341952462002731 114236378966012928693004097)
  ·
    refine ⟨85677284224509696519753073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114236378966012928693004097 85677284224509696519753073)
    ·
      refine ⟨64257963168382272389814805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85677284224509696519753073 64257963168382272389814805)
      ·
        refine ⟨3012092023517919018272569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64257963168382272389814805 3012092023517919018272569)
        ·
          refine ⟨2259069017638439263704427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012092023517919018272569 2259069017638439263704427)
          ·
            refine ⟨3388603526457658895556641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259069017638439263704427 3388603526457658895556641)
            ·
              refine ⟨2541452644843244171667481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388603526457658895556641 2541452644843244171667481)
              ·
                refine ⟨1906089483632433128750611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541452644843244171667481 1906089483632433128750611)
                ·
                  refine ⟨2859134225448649693125917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906089483632433128750611 2859134225448649693125917)
                  ·
                    refine ⟨1072175334543243634922219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859134225448649693125917 1072175334543243634922219)
                    ·
                      rfl

theorem cell22_3132081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_3132081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132081 prefixEnd_3132081 := by exact prefixLift 3132081
  have htrace : WordTrace (prefixWord ++ tailWord_3132081) baseStart_3132081 baseEnd_3132081 := by
    simpa [prefixWord, tailWord_3132081, baseEnd_3132081] using wordTrace_append hprefix tailTrace_3132081
  have hstable : (prefixWord ++ tailWord_3132081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132081).length < 2 ^ (prefixWord ++ tailWord_3132081).sum := by decide
  have hdescent : baseEnd_3132081 < baseStart_3132081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132238 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3132238 : Nat := 118140960795 + 3132238 * 2 ^ 59
def prefixEnd_3132238 : Nat := 4983230072969 + 3 ^ 40 * 3132238 * 2
def baseEnd_3132238 : Nat := 1072229078851747558746737

theorem tailTrace_3132238 : CollatzResearch.WordTrace tailWord_3132238 prefixEnd_3132238 1072229078851747558746737 := by
  unfold tailWord_3132238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280263153305518063308671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76161403484296096337646245 14280263153305518063308671)
  ·
    refine ⟨21420394729958277094963007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280263153305518063308671 21420394729958277094963007)
    ·
      refine ⟨32130592094937415642444511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21420394729958277094963007 32130592094937415642444511)
      ·
        refine ⟨48195888142406123463666767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32130592094937415642444511 48195888142406123463666767)
        ·
          refine ⟨72293832213609185195500151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48195888142406123463666767 72293832213609185195500151)
          ·
            refine ⟨108440748320413777793250227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72293832213609185195500151 108440748320413777793250227)
            ·
              refine ⟨162661122480620666689875341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108440748320413777793250227 162661122480620666689875341)
              ·
                refine ⟨60997920930232750008703253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162661122480620666689875341 60997920930232750008703253)
                ·
                  refine ⟨2859277543604660156657965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60997920930232750008703253 2859277543604660156657965)
                  ·
                    refine ⟨1072229078851747558746737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859277543604660156657965 1072229078851747558746737)
                    ·
                      rfl

theorem cell22_3132238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3132238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132238 prefixEnd_3132238 := by exact prefixLift 3132238
  have htrace : WordTrace (prefixWord ++ tailWord_3132238) baseStart_3132238 baseEnd_3132238 := by
    simpa [prefixWord, tailWord_3132238, baseEnd_3132238] using wordTrace_append hprefix tailTrace_3132238
  have hstable : (prefixWord ++ tailWord_3132238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132238).length < 2 ^ (prefixWord ++ tailWord_3132238).sum := by decide
  have hdescent : baseEnd_3132238 < baseStart_3132238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132255 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 2, 3]
def baseStart_3132255 : Nat := 118140960795 + 3132255 * 2 ^ 59
def prefixEnd_3132255 : Nat := 4983230072969 + 3 ^ 40 * 3132255 * 2
def baseEnd_3132255 : Nat := 1072234898299165181071685

theorem tailTrace_3132255 : CollatzResearch.WordTrace tailWord_3132255 prefixEnd_3132255 1072234898299165181071685 := by
  unfold tailWord_3132255
  simp only [CollatzResearch.WordTrace]
  refine ⟨114242725267382556409838219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76161816844921704273225479 114242725267382556409838219)
  ·
    refine ⟨171364087901073834614757329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114242725267382556409838219 171364087901073834614757329)
    ·
      refine ⟨128523065925805375961067997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171364087901073834614757329 128523065925805375961067997)
      ·
        refine ⟨48196149722177015985400499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128523065925805375961067997 48196149722177015985400499)
        ·
          refine ⟨72294224583265523978100749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48196149722177015985400499 72294224583265523978100749)
          ·
            refine ⟨27110334218724571491787781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72294224583265523978100749 27110334218724571491787781)
            ·
              refine ⟨5083187666010857154710209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27110334218724571491787781 5083187666010857154710209)
              ·
                refine ⟨3812390749508142866032657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083187666010857154710209 3812390749508142866032657)
                ·
                  refine ⟨2859293062131107149524493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812390749508142866032657 2859293062131107149524493)
                  ·
                    refine ⟨1072234898299165181071685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859293062131107149524493 1072234898299165181071685)
                    ·
                      rfl

theorem cell22_3132255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_3132255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132255 prefixEnd_3132255 := by exact prefixLift 3132255
  have htrace : WordTrace (prefixWord ++ tailWord_3132255) baseStart_3132255 baseEnd_3132255 := by
    simpa [prefixWord, tailWord_3132255, baseEnd_3132255] using wordTrace_append hprefix tailTrace_3132255
  have hstable : (prefixWord ++ tailWord_3132255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132255).length < 2 ^ (prefixWord ++ tailWord_3132255).sum := by decide
  have hdescent : baseEnd_3132255 < baseStart_3132255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132283 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 5, 3]
def baseStart_3132283 : Nat := 118140960795 + 3132283 * 2 ^ 59
def prefixEnd_3132283 : Nat := 4983230072969 + 3 ^ 40 * 3132283 * 2
def baseEnd_3132283 : Nat := 1072244483271382441371599

theorem tailTrace_3132283 : CollatzResearch.WordTrace tailWord_3132283 prefixEnd_3132283 1072244483271382441371599 := by
  unfold tailWord_3132283
  simp only [CollatzResearch.WordTrace]
  refine ⟨114243746511281117191857503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76162497674187411461238335 114243746511281117191857503)
  ·
    refine ⟨171365619766921675787786255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114243746511281117191857503 171365619766921675787786255)
    ·
      refine ⟨257048429650382513681679383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171365619766921675787786255 257048429650382513681679383)
      ·
        refine ⟨385572644475573770522519075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257048429650382513681679383 385572644475573770522519075)
        ·
          refine ⟨578358966713360655783778613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385572644475573770522519075 578358966713360655783778613)
          ·
            refine ⟨54221153129377561479729245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 578358966713360655783778613 54221153129377561479729245)
            ·
              refine ⟨20332932423516585554898467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54221153129377561479729245 20332932423516585554898467)
              ·
                refine ⟨30499398635274878332347701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20332932423516585554898467 30499398635274878332347701)
                ·
                  refine ⟨2859318622057019843657597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30499398635274878332347701 2859318622057019843657597)
                  ·
                    refine ⟨1072244483271382441371599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859318622057019843657597 1072244483271382441371599)
                    ·
                      rfl

theorem cell22_3132283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].length) (baseStart_3132283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132283 prefixEnd_3132283 := by exact prefixLift 3132283
  have htrace : WordTrace (prefixWord ++ tailWord_3132283) baseStart_3132283 baseEnd_3132283 := by
    simpa [prefixWord, tailWord_3132283, baseEnd_3132283] using wordTrace_append hprefix tailTrace_3132283
  have hstable : (prefixWord ++ tailWord_3132283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132283).length < 2 ^ (prefixWord ++ tailWord_3132283).sum := by decide
  have hdescent : baseEnd_3132283 < baseStart_3132283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132306 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3132306 : Nat := 118140960795 + 3132306 * 2 ^ 59
def prefixEnd_3132306 : Nat := 4983230072969 + 3 ^ 40 * 3132306 * 2
def baseEnd_3132306 : Nat := 1072252356641418048046529

theorem tailTrace_3132306 : CollatzResearch.WordTrace tailWord_3132306 prefixEnd_3132306 1072252356641418048046529 := by
  unfold tailWord_3132306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561146347549448029986193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76163056926798528079963181 28561146347549448029986193)
  ·
    refine ⟨21420859760662086022489645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28561146347549448029986193 21420859760662086022489645)
    ·
      refine ⟨8032822410248282258433617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21420859760662086022489645 8032822410248282258433617)
      ·
        refine ⟨6024616807686211693825213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8032822410248282258433617 6024616807686211693825213)
        ·
          refine ⟨2259231302882329385184455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6024616807686211693825213 2259231302882329385184455)
          ·
            refine ⟨3388846954323494077776683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259231302882329385184455 3388846954323494077776683)
            ·
              refine ⟨5083270431485241116665025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388846954323494077776683 5083270431485241116665025)
              ·
                refine ⟨3812452823613930837498769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083270431485241116665025 3812452823613930837498769)
                ·
                  refine ⟨2859339617710448128124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812452823613930837498769 2859339617710448128124077)
                  ·
                    refine ⟨1072252356641418048046529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859339617710448128124077 1072252356641418048046529)
                    ·
                      rfl

theorem cell22_3132306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3132306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132306 prefixEnd_3132306 := by exact prefixLift 3132306
  have htrace : WordTrace (prefixWord ++ tailWord_3132306) baseStart_3132306 baseEnd_3132306 := by
    simpa [prefixWord, tailWord_3132306, baseEnd_3132306] using wordTrace_append hprefix tailTrace_3132306
  have hstable : (prefixWord ++ tailWord_3132306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132306).length < 2 ^ (prefixWord ++ tailWord_3132306).sum := by decide
  have hdescent : baseEnd_3132306 < baseStart_3132306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132317 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3132317 : Nat := 118140960795 + 3132317 * 2 ^ 59
def prefixEnd_3132317 : Nat := 4983230072969 + 3 ^ 40 * 3132317 * 2
def baseEnd_3132317 : Nat := 1072256122166217686021495

theorem tailTrace_3132317 : CollatzResearch.WordTrace tailWord_3132317 prefixEnd_3132317 1072256122166217686021495 := by
  unfold tailWord_3132317
  simp only [CollatzResearch.WordTrace]
  refine ⟨114244986593157940998595205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76163324395438627332396803 114244986593157940998595205)
  ·
    refine ⟨21420934986217113937236601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114244986593157940998595205 21420934986217113937236601)
    ·
      refine ⟨16065701239662835452927451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21420934986217113937236601 16065701239662835452927451)
      ·
        refine ⟨24098551859494253179391177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065701239662835452927451 24098551859494253179391177)
        ·
          refine ⟨18073913894620689884543383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24098551859494253179391177 18073913894620689884543383)
          ·
            refine ⟨27110870841931034826815075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18073913894620689884543383 27110870841931034826815075)
            ·
              refine ⟨40666306262896552240222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27110870841931034826815075 40666306262896552240222613)
              ·
                refine ⟨1906233106073275886260435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40666306262896552240222613 1906233106073275886260435)
                ·
                  refine ⟨2859349659109913829390653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906233106073275886260435 2859349659109913829390653)
                  ·
                    refine ⟨1072256122166217686021495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859349659109913829390653 1072256122166217686021495)
                    ·
                      rfl

theorem cell22_3132317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3132317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132317 prefixEnd_3132317 := by exact prefixLift 3132317
  have htrace : WordTrace (prefixWord ++ tailWord_3132317) baseStart_3132317 baseEnd_3132317 := by
    simpa [prefixWord, tailWord_3132317, baseEnd_3132317] using wordTrace_append hprefix tailTrace_3132317
  have hstable : (prefixWord ++ tailWord_3132317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132317).length < 2 ^ (prefixWord ++ tailWord_3132317).sum := by decide
  have hdescent : baseEnd_3132317 < baseStart_3132317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132343 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3132343 : Nat := 118140960795 + 3132343 * 2 ^ 59
def prefixEnd_3132343 : Nat := 4983230072969 + 3 ^ 40 * 3132343 * 2
def baseEnd_3132343 : Nat := 1072265022497562284871415

theorem tailTrace_3132343 : CollatzResearch.WordTrace tailWord_3132343 prefixEnd_3132343 1072265022497562284871415 := by
  unfold tailWord_3132343
  simp only [CollatzResearch.WordTrace]
  refine ⟨114245934891063747439041683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76163956594042498292694455 114245934891063747439041683)
  ·
    refine ⟨171368902336595621158562525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114245934891063747439041683 171368902336595621158562525)
    ·
      refine ⟨64263338376223357934460947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171368902336595621158562525 64263338376223357934460947)
      ·
        refine ⟨96395007564335036901691421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64263338376223357934460947 96395007564335036901691421)
        ·
          refine ⟨36148127836625638838134283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96395007564335036901691421 36148127836625638838134283)
          ·
            refine ⟨54222191754938458257201425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36148127836625638838134283 54222191754938458257201425)
            ·
              refine ⟨40666643816203843692901069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54222191754938458257201425 40666643816203843692901069)
              ·
                refine ⟨15249991431076441384837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40666643816203843692901069 15249991431076441384837901)
                ·
                  refine ⟨5718746786653665519314213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15249991431076441384837901 5718746786653665519314213)
                  ·
                    refine ⟨1072265022497562284871415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718746786653665519314213 1072265022497562284871415)
                    ·
                      rfl

theorem cell22_3132343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3132343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132343 prefixEnd_3132343 := by exact prefixLift 3132343
  have htrace : WordTrace (prefixWord ++ tailWord_3132343) baseStart_3132343 baseEnd_3132343 := by
    simpa [prefixWord, tailWord_3132343, baseEnd_3132343] using wordTrace_append hprefix tailTrace_3132343
  have hstable : (prefixWord ++ tailWord_3132343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132343).length < 2 ^ (prefixWord ++ tailWord_3132343).sum := by decide
  have hdescent : baseEnd_3132343 < baseStart_3132343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132388 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3132388 : Nat := 118140960795 + 3132388 * 2 ^ 59
def prefixEnd_3132388 : Nat := 4983230072969 + 3 ^ 40 * 3132388 * 2
def baseEnd_3132388 : Nat := 1072280426917197167496277

theorem tailTrace_3132388 : CollatzResearch.WordTrace tailWord_3132388 prefixEnd_3132388 1072280426917197167496277 := by
  unfold tailWord_3132388
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123788087950360062214909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76165050783933813416286545 57123788087950360062214909)
  ·
    refine ⟨21421420532981385023330591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57123788087950360062214909 21421420532981385023330591)
    ·
      refine ⟨32132130799472077534995887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421420532981385023330591 32132130799472077534995887)
      ·
        refine ⟨48198196199208116302493831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32132130799472077534995887 48198196199208116302493831)
        ·
          refine ⟨72297294298812174453740747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48198196199208116302493831 72297294298812174453740747)
          ·
            refine ⟨108445941448218261680611121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72297294298812174453740747 108445941448218261680611121)
            ·
              refine ⟨81334456086163696260458341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108445941448218261680611121 81334456086163696260458341)
              ·
                refine ⟨15250210516155693048835939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81334456086163696260458341 15250210516155693048835939)
                ·
                  refine ⟨22875315774233539573253909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15250210516155693048835939 22875315774233539573253909)
                  ·
                    refine ⟨1072280426917197167496277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22875315774233539573253909 1072280426917197167496277)
                    ·
                      rfl

theorem cell22_3132388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3132388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132388 prefixEnd_3132388 := by exact prefixLift 3132388
  have htrace : WordTrace (prefixWord ++ tailWord_3132388) baseStart_3132388 baseEnd_3132388 := by
    simpa [prefixWord, tailWord_3132388, baseEnd_3132388] using wordTrace_append hprefix tailTrace_3132388
  have hstable : (prefixWord ++ tailWord_3132388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132388).length < 2 ^ (prefixWord ++ tailWord_3132388).sum := by decide
  have hdescent : baseEnd_3132388 < baseStart_3132388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132435 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 3, 3]
def baseStart_3132435 : Nat := 118140960795 + 3132435 * 2 ^ 59
def prefixEnd_3132435 : Nat := 4983230072969 + 3 ^ 40 * 3132435 * 2
def baseEnd_3132435 : Nat := 1072296515977704711571133

theorem tailTrace_3132435 : CollatzResearch.WordTrace tailWord_3132435 prefixEnd_3132435 1072296515977704711571133 := by
  unfold tailWord_3132435
  simp only [CollatzResearch.WordTrace]
  refine ⟨114249290406730447151390759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76166193604486964767593839 114249290406730447151390759)
  ·
    refine ⟨171373935610095670727086139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114249290406730447151390759 171373935610095670727086139)
    ·
      refine ⟨257060903415143506090629209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171373935610095670727086139 257060903415143506090629209)
      ·
        refine ⟨192795677561357629567971907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257060903415143506090629209 192795677561357629567971907)
        ·
          refine ⟨289193516342036444351957861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192795677561357629567971907 289193516342036444351957861)
          ·
            refine ⟨54223784314131833315992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289193516342036444351957861 54223784314131833315992099)
            ·
              refine ⟨81335676471197749973988149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54223784314131833315992099 81335676471197749973988149)
              ·
                refine ⟨7625219669174789060061389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81335676471197749973988149 7625219669174789060061389)
                ·
                  refine ⟨2859457375940545897523021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7625219669174789060061389 2859457375940545897523021)
                  ·
                    refine ⟨1072296515977704711571133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859457375940545897523021 1072296515977704711571133)
                    ·
                      rfl

theorem cell22_3132435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].length) (baseStart_3132435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132435 prefixEnd_3132435 := by exact prefixLift 3132435
  have htrace : WordTrace (prefixWord ++ tailWord_3132435) baseStart_3132435 baseEnd_3132435 := by
    simpa [prefixWord, tailWord_3132435, baseEnd_3132435] using wordTrace_append hprefix tailTrace_3132435
  have hstable : (prefixWord ++ tailWord_3132435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132435).length < 2 ^ (prefixWord ++ tailWord_3132435).sum := by decide
  have hdescent : baseEnd_3132435 < baseStart_3132435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132452 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_3132452 : Nat := 118140960795 + 3132452 * 2 ^ 59
def prefixEnd_3132452 : Nat := 4983230072969 + 3 ^ 40 * 3132452 * 2
def baseEnd_3132452 : Nat := 1072302335425122333896081

theorem tailTrace_3132452 : CollatzResearch.WordTrace tailWord_3132452 prefixEnd_3132452 1072302335425122333896081 := by
  unfold tailWord_3132452
  simp only [CollatzResearch.WordTrace]
  refine ⟨57124955223834429527379805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76166606965112572703173073 57124955223834429527379805)
  ·
    refine ⟨21421858208937911072767427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57124955223834429527379805 21421858208937911072767427)
    ·
      refine ⟨32132787313406866609151141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421858208937911072767427 32132787313406866609151141)
      ·
        refine ⟨6024897621263787489215839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32132787313406866609151141 6024897621263787489215839)
        ·
          refine ⟨9037346431895681233823759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024897621263787489215839 9037346431895681233823759)
          ·
            refine ⟨13556019647843521850735639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037346431895681233823759 13556019647843521850735639)
            ·
              refine ⟨20334029471765282776103459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556019647843521850735639 20334029471765282776103459)
              ·
                refine ⟨30501044207647924164155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20334029471765282776103459 30501044207647924164155189)
                ·
                  refine ⟨2859472894466992890389549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30501044207647924164155189 2859472894466992890389549)
                  ·
                    refine ⟨1072302335425122333896081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859472894466992890389549 1072302335425122333896081)
                    ·
                      rfl

theorem cell22_3132452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_3132452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132452 prefixEnd_3132452 := by exact prefixLift 3132452
  have htrace : WordTrace (prefixWord ++ tailWord_3132452) baseStart_3132452 baseEnd_3132452 := by
    simpa [prefixWord, tailWord_3132452, baseEnd_3132452] using wordTrace_append hprefix tailTrace_3132452
  have hstable : (prefixWord ++ tailWord_3132452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132452).length < 2 ^ (prefixWord ++ tailWord_3132452).sum := by decide
  have hdescent : baseEnd_3132452 < baseStart_3132452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132486 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3132486 : Nat := 118140960795 + 3132486 * 2 ^ 59
def prefixEnd_3132486 : Nat := 4983230072969 + 3 ^ 40 * 3132486 * 2
def baseEnd_3132486 : Nat := 1072313974319957578545977

theorem tailTrace_3132486 : CollatzResearch.WordTrace tailWord_3132486 prefixEnd_3132486 1072313974319957578545977 := by
  unfold tailWord_3132486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570348454048302589421791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76167433686363788574331541 3570348454048302589421791)
  ·
    refine ⟨5355522681072453884132687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570348454048302589421791 5355522681072453884132687)
    ·
      refine ⟨8033284021608680826199031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355522681072453884132687 8033284021608680826199031)
      ·
        refine ⟨12049926032413021239298547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033284021608680826199031 12049926032413021239298547)
        ·
          refine ⟨18074889048619531858947821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12049926032413021239298547 18074889048619531858947821)
          ·
            refine ⟨6778083393232324447105433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18074889048619531858947821 6778083393232324447105433)
            ·
              refine ⟨5083562544924243335329075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6778083393232324447105433 5083562544924243335329075)
              ·
                refine ⟨7625343817386365002993613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083562544924243335329075 7625343817386365002993613)
                ·
                  refine ⟨2859503931519886876122605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7625343817386365002993613 2859503931519886876122605)
                  ·
                    refine ⟨1072313974319957578545977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859503931519886876122605 1072313974319957578545977)
                    ·
                      rfl

theorem cell22_3132486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3132486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132486 prefixEnd_3132486 := by exact prefixLift 3132486
  have htrace : WordTrace (prefixWord ++ tailWord_3132486) baseStart_3132486 baseEnd_3132486 := by
    simpa [prefixWord, tailWord_3132486, baseEnd_3132486] using wordTrace_append hprefix tailTrace_3132486
  have hstable : (prefixWord ++ tailWord_3132486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132486).length < 2 ^ (prefixWord ++ tailWord_3132486).sum := by decide
  have hdescent : baseEnd_3132486 < baseStart_3132486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132512 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_3132512 : Nat := 118140960795 + 3132512 * 2 ^ 59
def prefixEnd_3132512 : Nat := 4983230072969 + 3 ^ 40 * 3132512 * 2
def baseEnd_3132512 : Nat := 1072322874651302177395897

theorem tailTrace_3132512 : CollatzResearch.WordTrace tailWord_3132512 prefixEnd_3132512 1072322874651302177395897 := by
  unfold tailWord_3132512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57126049413725744650971895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76168065884967659534629193 57126049413725744650971895)
  ·
    refine ⟨85689074120588616976457843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57126049413725744650971895 85689074120588616976457843)
    ·
      refine ⟨128533611180882925464686765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85689074120588616976457843 128533611180882925464686765)
      ·
        refine ⟨48200104192831097049257537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128533611180882925464686765 48200104192831097049257537)
        ·
          refine ⟨36150078144623322786943153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48200104192831097049257537 36150078144623322786943153)
          ·
            refine ⟨27112558608467492090207365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36150078144623322786943153 27112558608467492090207365)
            ·
              refine ⟨5083604739087654766913881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27112558608467492090207365 5083604739087654766913881)
              ·
                refine ⟨3812703554315741075185411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083604739087654766913881 3812703554315741075185411)
                ·
                  refine ⟨5719055331473611612778117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812703554315741075185411 5719055331473611612778117)
                  ·
                    refine ⟨1072322874651302177395897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719055331473611612778117 1072322874651302177395897)
                    ·
                      rfl

theorem cell22_3132512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_3132512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132512 prefixEnd_3132512 := by exact prefixLift 3132512
  have htrace : WordTrace (prefixWord ++ tailWord_3132512) baseStart_3132512 baseEnd_3132512 := by
    simpa [prefixWord, tailWord_3132512, baseEnd_3132512] using wordTrace_append hprefix tailTrace_3132512
  have hstable : (prefixWord ++ tailWord_3132512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132512).length < 2 ^ (prefixWord ++ tailWord_3132512).sum := by decide
  have hdescent : baseEnd_3132512 < baseStart_3132512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132520 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3132520 : Nat := 118140960795 + 3132520 * 2 ^ 59
def prefixEnd_3132520 : Nat := 4983230072969 + 3 ^ 40 * 3132520 * 2
def baseEnd_3132520 : Nat := 1072325613214792823195873

theorem tailTrace_3132520 : CollatzResearch.WordTrace tailWord_3132520 prefixEnd_3132520 1072325613214792823195873 := by
  unfold tailWord_3132520
  simp only [CollatzResearch.WordTrace]
  refine ⟨57126195305711253334117507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76168260407615004445490009 57126195305711253334117507)
  ·
    refine ⟨85689292958566880001176261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57126195305711253334117507 85689292958566880001176261)
    ·
      refine ⟨16066742429731290000220549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85689292958566880001176261 16066742429731290000220549)
      ·
        refine ⟨3012514205574616875041353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16066742429731290000220549 3012514205574616875041353)
        ·
          refine ⟨2259385654180962656281015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012514205574616875041353 2259385654180962656281015)
          ·
            refine ⟨3389078481271443984421523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259385654180962656281015 3389078481271443984421523)
            ·
              refine ⟨5083617721907165976632285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389078481271443984421523 5083617721907165976632285)
              ·
                refine ⟨1906356645715187241237107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083617721907165976632285 1906356645715187241237107)
                ·
                  refine ⟨2859534968572780861855661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906356645715187241237107 2859534968572780861855661)
                  ·
                    refine ⟨1072325613214792823195873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859534968572780861855661 1072325613214792823195873)
                    ·
                      rfl

theorem cell22_3132520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3132520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132520 prefixEnd_3132520 := by exact prefixLift 3132520
  have htrace : WordTrace (prefixWord ++ tailWord_3132520) baseStart_3132520 baseEnd_3132520 := by
    simpa [prefixWord, tailWord_3132520, baseEnd_3132520] using wordTrace_append hprefix tailTrace_3132520
  have hstable : (prefixWord ++ tailWord_3132520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132520).length < 2 ^ (prefixWord ++ tailWord_3132520).sum := by decide
  have hdescent : baseEnd_3132520 < baseStart_3132520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132574 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3132574 : Nat := 118140960795 + 3132574 * 2 ^ 59
def prefixEnd_3132574 : Nat := 4983230072969 + 3 ^ 40 * 3132574 * 2
def baseEnd_3132574 : Nat := 1072344098518354682345707

theorem tailTrace_3132574 : CollatzResearch.WordTrace tailWord_3132574 prefixEnd_3132574 1072344098518354682345707 := by
  unfold tailWord_3132574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281795019153359236337597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76169573435484582593800517 14281795019153359236337597)
  ·
    refine ⟨5355673132182509713626599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14281795019153359236337597 5355673132182509713626599)
    ·
      refine ⟨8033509698273764570439899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355673132182509713626599 8033509698273764570439899)
      ·
        refine ⟨12050264547410646855659849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033509698273764570439899 12050264547410646855659849)
        ·
          refine ⟨9037698410557985141744887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12050264547410646855659849 9037698410557985141744887)
          ·
            refine ⟨13556547615836977712617331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037698410557985141744887 13556547615836977712617331)
            ·
              refine ⟨20334821423755466568925997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556547615836977712617331 20334821423755466568925997)
              ·
                refine ⟨7625558033908299963347249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20334821423755466568925997 7625558033908299963347249)
                ·
                  refine ⟨5719168525431224972510437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625558033908299963347249 5719168525431224972510437)
                  ·
                    refine ⟨1072344098518354682345707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719168525431224972510437 1072344098518354682345707)
                    ·
                      rfl

theorem cell22_3132574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3132574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132574 prefixEnd_3132574 := by exact prefixLift 3132574
  have htrace : WordTrace (prefixWord ++ tailWord_3132574) baseStart_3132574 baseEnd_3132574 := by
    simpa [prefixWord, tailWord_3132574, baseEnd_3132574] using wordTrace_append hprefix tailTrace_3132574
  have hstable : (prefixWord ++ tailWord_3132574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132574).length < 2 ^ (prefixWord ++ tailWord_3132574).sum := by decide
  have hdescent : baseEnd_3132574 < baseStart_3132574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132696 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_3132696 : Nat := 118140960795 + 3132696 * 2 ^ 59
def prefixEnd_3132696 : Nat := 4983230072969 + 3 ^ 40 * 3132696 * 2
def baseEnd_3132696 : Nat := 357461953870529010265111

theorem tailTrace_3132696 : CollatzResearch.WordTrace tailWord_3132696 prefixEnd_3132696 357461953870529010265111 := by
  unfold tailWord_3132696
  simp only [CollatzResearch.WordTrace]
  refine ⟨57129404929392444363320971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76172539905856592484427961 57129404929392444363320971)
  ·
    refine ⟨85694107394088666544981457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57129404929392444363320971 85694107394088666544981457)
    ·
      refine ⟨64270580545566499908736093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85694107394088666544981457 64270580545566499908736093)
      ·
        refine ⟨24101467704587437465776035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64270580545566499908736093 24101467704587437465776035)
        ·
          refine ⟨36152201556881156198664053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24101467704587437465776035 36152201556881156198664053)
          ·
            refine ⟨3389268895957608393624755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36152201556881156198664053 3389268895957608393624755)
            ·
              refine ⟨5083903343936412590437133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389268895957608393624755 5083903343936412590437133)
              ·
                refine ⟨1906463753976154721413925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083903343936412590437133 1906463753976154721413925)
                ·
                  refine ⟨357461953870529010265111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906463753976154721413925 357461953870529010265111)
                  ·
                    rfl

theorem cell22_3132696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_3132696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132696 prefixEnd_3132696 := by exact prefixLift 3132696
  have htrace : WordTrace (prefixWord ++ tailWord_3132696) baseStart_3132696 baseEnd_3132696 := by
    simpa [prefixWord, tailWord_3132696, baseEnd_3132696] using wordTrace_append hprefix tailTrace_3132696
  have hstable : (prefixWord ++ tailWord_3132696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132696).length < 2 ^ (prefixWord ++ tailWord_3132696).sum := by decide
  have hdescent : baseEnd_3132696 < baseStart_3132696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132707 : List Nat := [1, 1, 1, 4, 2, 5, 8]
def baseStart_3132707 : Nat := 118140960795 + 3132707 * 2 ^ 59
def prefixEnd_3132707 : Nat := 4983230072969 + 3 ^ 40 * 3132707 * 2
def baseEnd_3132707 : Nat := 39718134338384691435937

theorem tailTrace_3132707 : CollatzResearch.WordTrace tailWord_3132707 prefixEnd_3132707 39718134338384691435937 := by
  unfold tailWord_3132707
  simp only [CollatzResearch.WordTrace]
  refine ⟨114259211061745037605292375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76172807374496691736861583 114259211061745037605292375)
  ·
    refine ⟨171388816592617556407938563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114259211061745037605292375 171388816592617556407938563)
    ·
      refine ⟨257083224888926334611907845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171388816592617556407938563 257083224888926334611907845)
      ·
        refine ⟨48203104666673687739732721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257083224888926334611907845 48203104666673687739732721)
        ·
          refine ⟨36152328500005265804799541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48203104666673687739732721 36152328500005265804799541)
          ·
            refine ⟨3389280796875493669199957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36152328500005265804799541 3389280796875493669199957)
            ·
              refine ⟨39718134338384691435937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3389280796875493669199957 39718134338384691435937)
              ·
                rfl

theorem cell22_3132707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 8].length) (baseStart_3132707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132707 prefixEnd_3132707 := by exact prefixLift 3132707
  have htrace : WordTrace (prefixWord ++ tailWord_3132707) baseStart_3132707 baseEnd_3132707 := by
    simpa [prefixWord, tailWord_3132707, baseEnd_3132707] using wordTrace_append hprefix tailTrace_3132707
  have hstable : (prefixWord ++ tailWord_3132707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132707).length < 2 ^ (prefixWord ++ tailWord_3132707).sum := by decide
  have hdescent : baseEnd_3132707 < baseStart_3132707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132709 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_3132709 : Nat := 118140960795 + 3132709 * 2 ^ 59
def prefixEnd_3132709 : Nat := 4983230072969 + 3 ^ 40 * 3132709 * 2
def baseEnd_3132709 : Nat := 1072390311777259330220293

theorem tailTrace_3132709 : CollatzResearch.WordTrace tailWord_3132709 prefixEnd_3132709 1072390311777259330220293 := by
  unfold tailWord_3132709
  simp only [CollatzResearch.WordTrace]
  refine ⟨114259284007737791946865181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76172856005158527964576787 114259284007737791946865181)
  ·
    refine ⟨42847231502901671980074443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114259284007737791946865181 42847231502901671980074443)
    ·
      refine ⟨64270847254352507970111665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42847231502901671980074443 64270847254352507970111665)
      ·
        refine ⟨48203135440764380977583749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64270847254352507970111665 48203135440764380977583749)
        ·
          refine ⟨9038087895143321433296953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48203135440764380977583749 9038087895143321433296953)
          ·
            refine ⟨6778565921357491074972715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9038087895143321433296953 6778565921357491074972715)
            ·
              refine ⟨10167848882036236612459073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778565921357491074972715 10167848882036236612459073)
              ·
                refine ⟨7625886661527177459344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167848882036236612459073 7625886661527177459344305)
                ·
                  refine ⟨5719414996145383094508229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625886661527177459344305 5719414996145383094508229)
                  ·
                    refine ⟨1072390311777259330220293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719414996145383094508229 1072390311777259330220293)
                    ·
                      rfl

theorem cell22_3132709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_3132709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132709 prefixEnd_3132709 := by exact prefixLift 3132709
  have htrace : WordTrace (prefixWord ++ tailWord_3132709) baseStart_3132709 baseEnd_3132709 := by
    simpa [prefixWord, tailWord_3132709, baseEnd_3132709] using wordTrace_append hprefix tailTrace_3132709
  have hstable : (prefixWord ++ tailWord_3132709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132709).length < 2 ^ (prefixWord ++ tailWord_3132709).sum := by decide
  have hdescent : baseEnd_3132709 < baseStart_3132709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132724 : List Nat := [2, 5, 1, 1, 1, 1, 4, 7]
def baseStart_3132724 : Nat := 118140960795 + 3132724 * 2 ^ 59
def prefixEnd_3132724 : Nat := 4983230072969 + 3 ^ 40 * 3132724 * 2
def baseEnd_3132724 : Nat := 119155049620422699010583

theorem tailTrace_3132724 : CollatzResearch.WordTrace tailWord_3132724 prefixEnd_3132724 119155049620422699010583 := by
  unfold tailWord_3132724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57129915551341724754330613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76173220735122299672440817 57129915551341724754330613)
  ·
    refine ⟨5355929582938286695718495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57129915551341724754330613 5355929582938286695718495)
    ·
      refine ⟨8033894374407430043577743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355929582938286695718495 8033894374407430043577743)
      ·
        refine ⟨12050841561611145065366615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033894374407430043577743 12050841561611145065366615)
        ·
          refine ⟨18076262342416717598049923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050841561611145065366615 18076262342416717598049923)
          ·
            refine ⟨27114393513625076397074885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18076262342416717598049923 27114393513625076397074885)
            ·
              refine ⟨5083948783804701824451541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27114393513625076397074885 5083948783804701824451541)
              ·
                refine ⟨119155049620422699010583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5083948783804701824451541 119155049620422699010583)
                ·
                  rfl

theorem cell22_3132724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_3132724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132724 prefixEnd_3132724 := by exact prefixLift 3132724
  have htrace : WordTrace (prefixWord ++ tailWord_3132724) baseStart_3132724 baseEnd_3132724 := by
    simpa [prefixWord, tailWord_3132724, baseEnd_3132724] using wordTrace_append hprefix tailTrace_3132724
  have hstable : (prefixWord ++ tailWord_3132724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132724).length < 2 ^ (prefixWord ++ tailWord_3132724).sum := by decide
  have hdescent : baseEnd_3132724 < baseStart_3132724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132758 : List Nat := [5, 2, 3, 1, 1, 10]
def baseStart_3132758 : Nat := 118140960795 + 3132758 * 2 ^ 59
def prefixEnd_3132758 : Nat := 4983230072969 + 3 ^ 40 * 3132758 * 2
def baseEnd_3132758 : Nat := 13239593647884438712903

theorem tailTrace_3132758 : CollatzResearch.WordTrace tailWord_3132758 prefixEnd_3132758 13239593647884438712903 := by
  unfold tailWord_3132758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7141316949035017082212433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76174047456373515543599285 7141316949035017082212433)
  ·
    refine ⟨5355987711776262811659325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7141316949035017082212433 5355987711776262811659325)
    ·
      refine ⟨2008495391916098554372247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5355987711776262811659325 2008495391916098554372247)
      ·
        refine ⟨3012743087874147831558371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008495391916098554372247 3012743087874147831558371)
        ·
          refine ⟨4519114631811221747337557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012743087874147831558371 4519114631811221747337557)
          ·
            refine ⟨13239593647884438712903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4519114631811221747337557 13239593647884438712903)
            ·
              rfl

theorem cell22_3132758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 10].length) (baseStart_3132758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132758 prefixEnd_3132758 := by exact prefixLift 3132758
  have htrace : WordTrace (prefixWord ++ tailWord_3132758) baseStart_3132758 baseEnd_3132758 := by
    simpa [prefixWord, tailWord_3132758, baseEnd_3132758] using wordTrace_append hprefix tailTrace_3132758
  have hstable : (prefixWord ++ tailWord_3132758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132758).length < 2 ^ (prefixWord ++ tailWord_3132758).sum := by decide
  have hdescent : baseEnd_3132758 < baseStart_3132758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132767 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3132767 : Nat := 118140960795 + 3132767 * 2 ^ 59
def prefixEnd_3132767 : Nat := 4983230072969 + 3 ^ 40 * 3132767 * 2
def baseEnd_3132767 : Nat := 1072410166362566512270115

theorem tailTrace_3132767 : CollatzResearch.WordTrace tailWord_3132767 prefixEnd_3132767 1072410166362566512270115 := by
  unfold tailWord_3132767
  simp only [CollatzResearch.WordTrace]
  refine ⟨114261399441527667852476555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76174266294351778568317703 114261399441527667852476555)
  ·
    refine ⟨171392099162291501778714833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114261399441527667852476555 171392099162291501778714833)
    ·
      refine ⟨128544074371718626334036125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171392099162291501778714833 128544074371718626334036125)
      ·
        refine ⟨48204027889394484875263547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128544074371718626334036125 48204027889394484875263547)
        ·
          refine ⟨72306041834091727312895321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48204027889394484875263547 72306041834091727312895321)
          ·
            refine ⟨54229531375568795484671491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72306041834091727312895321 54229531375568795484671491)
            ·
              refine ⟨81344297063353193227007237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54229531375568795484671491 81344297063353193227007237)
              ·
                refine ⟨15252055699378723730063857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81344297063353193227007237 15252055699378723730063857)
                ·
                  refine ⟨11439041774534042797547893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15252055699378723730063857 11439041774534042797547893)
                  ·
                    refine ⟨1072410166362566512270115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11439041774534042797547893 1072410166362566512270115)
                    ·
                      rfl

theorem cell22_3132767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3132767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132767 prefixEnd_3132767 := by exact prefixLift 3132767
  have htrace : WordTrace (prefixWord ++ tailWord_3132767) baseStart_3132767 baseEnd_3132767 := by
    simpa [prefixWord, tailWord_3132767, baseEnd_3132767] using wordTrace_append hprefix tailTrace_3132767
  have hstable : (prefixWord ++ tailWord_3132767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132767).length < 2 ^ (prefixWord ++ tailWord_3132767).sum := by decide
  have hdescent : baseEnd_3132767 < baseStart_3132767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132831 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 4]
def baseStart_3132831 : Nat := 118140960795 + 3132831 * 2 ^ 59
def prefixEnd_3132831 : Nat := 4983230072969 + 3 ^ 40 * 3132831 * 2
def baseEnd_3132831 : Nat := 357477358290163892889973

theorem tailTrace_3132831 : CollatzResearch.WordTrace tailWord_3132831 prefixEnd_3132831 357477358290163892889973 := by
  unfold tailWord_3132831
  simp only [CollatzResearch.WordTrace]
  refine ⟨114263733713295806782806347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76175822475530537855204231 114263733713295806782806347)
  ·
    refine ⟨171395600569943710174209521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114263733713295806782806347 171395600569943710174209521)
    ·
      refine ⟨128546700427457782630657141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171395600569943710174209521 128546700427457782630657141)
      ·
        refine ⟨12051253165074167121624107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128546700427457782630657141 12051253165074167121624107)
        ·
          refine ⟨18076879747611250682436161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051253165074167121624107 18076879747611250682436161)
          ·
            refine ⟨13557659810708438011827121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18076879747611250682436161 13557659810708438011827121)
            ·
              refine ⟨10168244858031328508870341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557659810708438011827121 10168244858031328508870341)
              ·
                refine ⟨1906545910880874095413189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10168244858031328508870341 1906545910880874095413189)
                ·
                  refine ⟨357477358290163892889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906545910880874095413189 357477358290163892889973)
                  ·
                    rfl

theorem cell22_3132831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 4].length) (baseStart_3132831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132831 prefixEnd_3132831 := by exact prefixLift 3132831
  have htrace : WordTrace (prefixWord ++ tailWord_3132831) baseStart_3132831 baseEnd_3132831 := by
    simpa [prefixWord, tailWord_3132831, baseEnd_3132831] using wordTrace_append hprefix tailTrace_3132831
  have hstable : (prefixWord ++ tailWord_3132831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132831).length < 2 ^ (prefixWord ++ tailWord_3132831).sum := by decide
  have hdescent : baseEnd_3132831 < baseStart_3132831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132981 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3132981 : Nat := 118140960795 + 3132981 * 2 ^ 59
def prefixEnd_3132981 : Nat := 4983230072969 + 3 ^ 40 * 3132981 * 2
def baseEnd_3132981 : Nat := 1072483422935941287419459

theorem tailTrace_3132981 : CollatzResearch.WordTrace tailWord_3132981 prefixEnd_3132981 1072483422935941287419459 := by
  unfold tailWord_3132981
  simp only [CollatzResearch.WordTrace]
  refine ⟨114269204662752382400766797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76179469775168254933844531 114269204662752382400766797)
  ·
    refine ⟨42850951748532143400287549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114269204662752382400766797 42850951748532143400287549)
    ·
      refine ⟨16069106905699553775107831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42850951748532143400287549 16069106905699553775107831)
      ·
        refine ⟨24103660358549330662661747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16069106905699553775107831 24103660358549330662661747)
        ·
          refine ⟨36155490537823995993992621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24103660358549330662661747 36155490537823995993992621)
          ·
            refine ⟨13558308951683998497747233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36155490537823995993992621 13558308951683998497747233)
            ·
              refine ⟨10168731713762998873310425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13558308951683998497747233 10168731713762998873310425)
              ·
                refine ⟨7626548785322249154982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10168731713762998873310425 7626548785322249154982819)
                ·
                  refine ⟨11439823177983373732474229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7626548785322249154982819 11439823177983373732474229)
                  ·
                    refine ⟨1072483422935941287419459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11439823177983373732474229 1072483422935941287419459)
                    ·
                      rfl

theorem cell22_3132981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3132981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132981 prefixEnd_3132981 := by exact prefixLift 3132981
  have htrace : WordTrace (prefixWord ++ tailWord_3132981) baseStart_3132981 baseEnd_3132981 := by
    simpa [prefixWord, tailWord_3132981, baseEnd_3132981] using wordTrace_append hprefix tailTrace_3132981
  have hstable : (prefixWord ++ tailWord_3132981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132981).length < 2 ^ (prefixWord ++ tailWord_3132981).sum := by decide
  have hdescent : baseEnd_3132981 < baseStart_3132981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132983 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 4]
def baseStart_3132983 : Nat := 118140960795 + 3132983 * 2 ^ 59
def prefixEnd_3132983 : Nat := 4983230072969 + 3 ^ 40 * 3132983 * 2
def baseEnd_3132983 : Nat := 357494702525604649623151

theorem tailTrace_3132983 : CollatzResearch.WordTrace tailWord_3132983 prefixEnd_3132983 357494702525604649623151 := by
  unfold tailWord_3132983
  simp only [CollatzResearch.WordTrace]
  refine ⟨114269277608745136742339603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76179518405830091161559735 114269277608745136742339603)
  ·
    refine ⟨171403916413117705113509405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114269277608745136742339603 171403916413117705113509405)
    ·
      refine ⟨64276468654919139417566027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171403916413117705113509405 64276468654919139417566027)
      ·
        refine ⟨96414702982378709126349041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64276468654919139417566027 96414702982378709126349041)
        ·
          refine ⟨72311027236784031844761781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96414702982378709126349041 72311027236784031844761781)
          ·
            refine ⟨6779158803448502985446417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72311027236784031844761781 6779158803448502985446417)
            ·
              refine ⟨5084369102586377239084813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6779158803448502985446417 5084369102586377239084813)
              ·
                refine ⟨1906638413469891464656805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5084369102586377239084813 1906638413469891464656805)
                ·
                  refine ⟨357494702525604649623151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906638413469891464656805 357494702525604649623151)
                  ·
                    rfl

theorem cell22_3132983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 4].length) (baseStart_3132983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132983 prefixEnd_3132983 := by exact prefixLift 3132983
  have htrace : WordTrace (prefixWord ++ tailWord_3132983) baseStart_3132983 baseEnd_3132983 := by
    simpa [prefixWord, tailWord_3132983, baseEnd_3132983] using wordTrace_append hprefix tailTrace_3132983
  have hstable : (prefixWord ++ tailWord_3132983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132983).length < 2 ^ (prefixWord ++ tailWord_3132983).sum := by decide
  have hdescent : baseEnd_3132983 < baseStart_3132983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132985 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_3132985 : Nat := 118140960795 + 3132985 * 2 ^ 59
def prefixEnd_3132985 : Nat := 4983230072969 + 3 ^ 40 * 3132985 * 2
def baseEnd_3132985 : Nat := 1072484792217686610319447

theorem tailTrace_3132985 : CollatzResearch.WordTrace tailWord_3132985 prefixEnd_3132985 1072484792217686610319447 := by
  unfold tailWord_3132985
  simp only [CollatzResearch.WordTrace]
  refine ⟨114269350554737891083912409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76179567036491927389274939 114269350554737891083912409)
  ·
    refine ⟨85702012916053418312934307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114269350554737891083912409 85702012916053418312934307)
    ·
      refine ⟨128553019374080127469401461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85702012916053418312934307 128553019374080127469401461)
      ·
        refine ⟨12051845566320011950256387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128553019374080127469401461 12051845566320011950256387)
        ·
          refine ⟨18077768349480017925384581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051845566320011950256387 18077768349480017925384581)
          ·
            refine ⟨3389581565527503361009609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18077768349480017925384581 3389581565527503361009609)
            ·
              refine ⟨2542186174145627520757207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389581565527503361009609 2542186174145627520757207)
              ·
                refine ⟨3813279261218441281135811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542186174145627520757207 3813279261218441281135811)
                ·
                  refine ⟨5719918891827661921703717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813279261218441281135811 5719918891827661921703717)
                  ·
                    refine ⟨1072484792217686610319447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719918891827661921703717 1072484792217686610319447)
                    ·
                      rfl

theorem cell22_3132985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_3132985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3132985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3132985 prefixEnd_3132985 := by exact prefixLift 3132985
  have htrace : WordTrace (prefixWord ++ tailWord_3132985) baseStart_3132985 baseEnd_3132985 := by
    simpa [prefixWord, tailWord_3132985, baseEnd_3132985] using wordTrace_append hprefix tailTrace_3132985
  have hstable : (prefixWord ++ tailWord_3132985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132985).length < 2 ^ (prefixWord ++ tailWord_3132985).sum := by decide
  have hdescent : baseEnd_3132985 < baseStart_3132985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133015 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 2, 3]
def baseStart_3133015 : Nat := 118140960795 + 3133015 * 2 ^ 59
def prefixEnd_3133015 : Nat := 4983230072969 + 3 ^ 40 * 3133015 * 2
def baseEnd_3133015 : Nat := 1072495061830776532069355

theorem tailTrace_3133015 : CollatzResearch.WordTrace tailWord_3133015 prefixEnd_3133015 1072495061830776532069355 := by
  unfold tailWord_3133015
  simp only [CollatzResearch.WordTrace]
  refine ⟨114270444744629206207504499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76180296496419470805002999 114270444744629206207504499)
  ·
    refine ⟨171405667116943809311256749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114270444744629206207504499 171405667116943809311256749)
    ·
      refine ⟨64277125168853928491721281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171405667116943809311256749 64277125168853928491721281)
      ·
        refine ⟨48207843876640446368790961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64277125168853928491721281 48207843876640446368790961)
        ·
          refine ⟨36155882907480334776593221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48207843876640446368790961 36155882907480334776593221)
          ·
            refine ⟨6779228045152562770611229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36155882907480334776593221 6779228045152562770611229)
            ·
              refine ⟨2542210516932211038979211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6779228045152562770611229 2542210516932211038979211)
              ·
                refine ⟨3813315775398316558468817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542210516932211038979211 3813315775398316558468817)
                ·
                  refine ⟨2859986831548737418851613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813315775398316558468817 2859986831548737418851613)
                  ·
                    refine ⟨1072495061830776532069355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859986831548737418851613 1072495061830776532069355)
                    ·
                      rfl

theorem cell22_3133015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_3133015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133015 prefixEnd_3133015 := by exact prefixLift 3133015
  have htrace : WordTrace (prefixWord ++ tailWord_3133015) baseStart_3133015 baseEnd_3133015 := by
    simpa [prefixWord, tailWord_3133015, baseEnd_3133015] using wordTrace_append hprefix tailTrace_3133015
  have hstable : (prefixWord ++ tailWord_3133015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133015).length < 2 ^ (prefixWord ++ tailWord_3133015).sum := by decide
  have hdescent : baseEnd_3133015 < baseStart_3133015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133028 : List Nat := [2, 3, 1, 1, 2, 5, 2, 6]
def baseStart_3133028 : Nat := 118140960795 + 3133028 * 2 ^ 59
def prefixEnd_3133028 : Nat := 4983230072969 + 3 ^ 40 * 3133028 * 2
def baseEnd_3133028 : Nat := 119166612444049870166035

theorem tailTrace_3133028 : CollatzResearch.WordTrace tailWord_3133028 prefixEnd_3133028 119166612444049870166035 := by
  unfold tailWord_3133028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57135459446791054713863869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76180612595721406285151825 57135459446791054713863869)
  ·
    refine ⟨21425797292546645517698951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57135459446791054713863869 21425797292546645517698951)
    ·
      refine ⟨32138695938819968276548427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21425797292546645517698951 32138695938819968276548427)
      ·
        refine ⟨48208043908229952414822641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32138695938819968276548427 48208043908229952414822641)
        ·
          refine ⟨36156032931172464311116981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48208043908229952414822641 36156032931172464311116981)
          ·
            refine ⟨3389628087297418529167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36156032931172464311116981 3389628087297418529167217)
            ·
              refine ⟨2542221065473063896875413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389628087297418529167217 2542221065473063896875413)
              ·
                refine ⟨119166612444049870166035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2542221065473063896875413 119166612444049870166035)
                ·
                  rfl

theorem cell22_3133028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_3133028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133028 prefixEnd_3133028 := by exact prefixLift 3133028
  have htrace : WordTrace (prefixWord ++ tailWord_3133028) baseStart_3133028 baseEnd_3133028 := by
    simpa [prefixWord, tailWord_3133028, baseEnd_3133028] using wordTrace_append hprefix tailTrace_3133028
  have hstable : (prefixWord ++ tailWord_3133028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133028).length < 2 ^ (prefixWord ++ tailWord_3133028).sum := by decide
  have hdescent : baseEnd_3133028 < baseStart_3133028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133056 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_3133056 : Nat := 118140960795 + 3133056 * 2 ^ 59
def prefixEnd_3133056 : Nat := 4983230072969 + 3 ^ 40 * 3133056 * 2
def baseEnd_3133056 : Nat := 357503032322888697264743

theorem tailTrace_3133056 : CollatzResearch.WordTrace tailWord_3133056 prefixEnd_3133056 357503032322888697264743 := by
  unfold tailWord_3133056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57135970068740335104873511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76181293424987113473164681 57135970068740335104873511)
  ·
    refine ⟨85703955103110502657310267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57135970068740335104873511 85703955103110502657310267)
    ·
      refine ⟨128555932654665753985965401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85703955103110502657310267 128555932654665753985965401)
      ·
        refine ⟨96416949490999315489474051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128555932654665753985965401 96416949490999315489474051)
        ·
          refine ⟨144625424236498973234211077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96416949490999315489474051 144625424236498973234211077)
          ·
            refine ⟨27117267044343557481414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144625424236498973234211077 27117267044343557481414577)
            ·
              refine ⟨20337950283257668111060933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27117267044343557481414577 20337950283257668111060933)
              ·
                refine ⟨3813365678110812770823925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20337950283257668111060933 3813365678110812770823925)
                ·
                  refine ⟨357503032322888697264743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813365678110812770823925 357503032322888697264743)
                  ·
                    rfl

theorem cell22_3133056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_3133056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133056 prefixEnd_3133056 := by exact prefixLift 3133056
  have htrace : WordTrace (prefixWord ++ tailWord_3133056) baseStart_3133056 baseEnd_3133056 := by
    simpa [prefixWord, tailWord_3133056, baseEnd_3133056] using wordTrace_append hprefix tailTrace_3133056
  have hstable : (prefixWord ++ tailWord_3133056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133056).length < 2 ^ (prefixWord ++ tailWord_3133056).sum := by decide
  have hdescent : baseEnd_3133056 < baseStart_3133056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133131 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_3133131 : Nat := 118140960795 + 3133131 * 2 ^ 59
def prefixEnd_3133131 : Nat := 4983230072969 + 3 ^ 40 * 3133131 * 2
def baseEnd_3133131 : Nat := 1072534771001390896168999

theorem tailTrace_3133131 : CollatzResearch.WordTrace tailWord_3133131 prefixEnd_3133131 1072534771001390896168999 := by
  unfold tailWord_3133131
  simp only [CollatzResearch.WordTrace]
  refine ⟨114274675612208958018727247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76183117074805972012484831 114274675612208958018727247)
  ·
    refine ⟨171412013418313437028090871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114274675612208958018727247 171412013418313437028090871)
    ·
      refine ⟨257118020127470155542136307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171412013418313437028090871 257118020127470155542136307)
      ·
        refine ⟨385677030191205233313204461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257118020127470155542136307 385677030191205233313204461)
        ·
          refine ⟨144628886321701962492451673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385677030191205233313204461 144628886321701962492451673)
          ·
            refine ⟨108471664741276471869338755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144628886321701962492451673 108471664741276471869338755)
            ·
              refine ⟨162707497111914707804008133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108471664741276471869338755 162707497111914707804008133)
              ·
                refine ⟨30507655708484007713251525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162707497111914707804008133 30507655708484007713251525)
                ·
                  refine ⟨5720185445340751446234661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30507655708484007713251525 5720185445340751446234661)
                  ·
                    refine ⟨1072534771001390896168999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720185445340751446234661 1072534771001390896168999)
                    ·
                      rfl

theorem cell22_3133131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_3133131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133131 prefixEnd_3133131 := by exact prefixLift 3133131
  have htrace : WordTrace (prefixWord ++ tailWord_3133131) baseStart_3133131 baseEnd_3133131 := by
    simpa [prefixWord, tailWord_3133131, baseEnd_3133131] using wordTrace_append hprefix tailTrace_3133131
  have hstable : (prefixWord ++ tailWord_3133131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133131).length < 2 ^ (prefixWord ++ tailWord_3133131).sum := by decide
  have hdescent : baseEnd_3133131 < baseStart_3133131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133176 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3133176 : Nat := 118140960795 + 3133176 * 2 ^ 59
def prefixEnd_3133176 : Nat := 4983230072969 + 3 ^ 40 * 3133176 * 2
def baseEnd_3133176 : Nat := 1072550175421025778793861

theorem tailTrace_3133176 : CollatzResearch.WordTrace tailWord_3133176 prefixEnd_3133176 1072550175421025778793861 := by
  unfold tailWord_3133176
  simp only [CollatzResearch.WordTrace]
  refine ⟨57138158448522965352057691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76184211264697287136076921 57138158448522965352057691)
  ·
    refine ⟨85707237672784448028086537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57138158448522965352057691 85707237672784448028086537)
    ·
      refine ⟨64280428254588336021064903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85707237672784448028086537 64280428254588336021064903)
      ·
        refine ⟨96420642381882504031597355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64280428254588336021064903 96420642381882504031597355)
        ·
          refine ⟨144630963572823756047396033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96420642381882504031597355 144630963572823756047396033)
          ·
            refine ⟨108473222679617817035547025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144630963572823756047396033 108473222679617817035547025)
            ·
              refine ⟨81354917009713362776660269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108473222679617817035547025 81354917009713362776660269)
              ·
                refine ⟨30508093878642511041247601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81354917009713362776660269 30508093878642511041247601)
                ·
                  refine ⟨22881070408981883280935701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30508093878642511041247601 22881070408981883280935701)
                  ·
                    refine ⟨1072550175421025778793861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22881070408981883280935701 1072550175421025778793861)
                    ·
                      rfl

theorem cell22_3133176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3133176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133176 prefixEnd_3133176 := by exact prefixLift 3133176
  have htrace : WordTrace (prefixWord ++ tailWord_3133176) baseStart_3133176 baseEnd_3133176 := by
    simpa [prefixWord, tailWord_3133176, baseEnd_3133176] using wordTrace_append hprefix tailTrace_3133176
  have hstable : (prefixWord ++ tailWord_3133176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133176).length < 2 ^ (prefixWord ++ tailWord_3133176).sum := by decide
  have hdescent : baseEnd_3133176 < baseStart_3133176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133214 : List Nat := [4, 3, 2, 2, 2, 1, 8]
def baseStart_3133214 : Nat := 118140960795 + 3133214 * 2 ^ 59
def prefixEnd_3133214 : Nat := 4983230072969 + 3 ^ 40 * 3133214 * 2
def baseEnd_3133214 : Nat := 39724562355466901716435

theorem tailTrace_3133214 : CollatzResearch.WordTrace tailWord_3133214 prefixEnd_3133214 39724562355466901716435 := by
  unfold tailWord_3133214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284712858863532899249837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76185135247272175462665797 14284712858863532899249837)
  ·
    refine ⟨5356767322073824837218689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14284712858863532899249837 5356767322073824837218689)
    ·
      refine ⟨4017575491555368627914017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356767322073824837218689 4017575491555368627914017)
      ·
        refine ⟨3013181618666526470935513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017575491555368627914017 3013181618666526470935513)
        ·
          refine ⟨2259886213999894853201635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013181618666526470935513 2259886213999894853201635)
          ·
            refine ⟨3389829320999842279802453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259886213999894853201635 3389829320999842279802453)
            ·
              refine ⟨39724562355466901716435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3389829320999842279802453 39724562355466901716435)
              ·
                rfl

theorem cell22_3133214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 8].length) (baseStart_3133214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133214 prefixEnd_3133214 := by exact prefixLift 3133214
  have htrace : WordTrace (prefixWord ++ tailWord_3133214) baseStart_3133214 baseEnd_3133214 := by
    simpa [prefixWord, tailWord_3133214, baseEnd_3133214] using wordTrace_append hprefix tailTrace_3133214
  have hstable : (prefixWord ++ tailWord_3133214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133214).length < 2 ^ (prefixWord ++ tailWord_3133214).sum := by decide
  have hdescent : baseEnd_3133214 < baseStart_3133214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133242 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_3133242 : Nat := 118140960795 + 3133242 * 2 ^ 59
def prefixEnd_3133242 : Nat := 4983230072969 + 3 ^ 40 * 3133242 * 2
def baseEnd_3133242 : Nat := 357524256189941202214553

theorem tailTrace_3133242 : CollatzResearch.WordTrace tailWord_3133242 prefixEnd_3133242 357524256189941202214553 := by
  unfold tailWord_3133242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28569681028701705994004495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76185816076537882650678653 28569681028701705994004495)
  ·
    refine ⟨42854521543052558991006743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28569681028701705994004495 42854521543052558991006743)
    ·
      refine ⟨64281782314578838486510115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42854521543052558991006743 64281782314578838486510115)
      ·
        refine ⟨96422673471868257729765173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64281782314578838486510115 96422673471868257729765173)
        ·
          refine ⟨9039625637987649162165485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96422673471868257729765173 9039625637987649162165485)
          ·
            refine ⟨3389859614245368435812057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9039625637987649162165485 3389859614245368435812057)
            ·
              refine ⟨2542394710684026326859043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389859614245368435812057 2542394710684026326859043)
              ·
                refine ⟨3813592066026039490288565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542394710684026326859043 3813592066026039490288565)
                ·
                  refine ⟨357524256189941202214553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813592066026039490288565 357524256189941202214553)
                  ·
                    rfl

theorem cell22_3133242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_3133242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133242 prefixEnd_3133242 := by exact prefixLift 3133242
  have htrace : WordTrace (prefixWord ++ tailWord_3133242) baseStart_3133242 baseEnd_3133242 := by
    simpa [prefixWord, tailWord_3133242, baseEnd_3133242] using wordTrace_append hprefix tailTrace_3133242
  have hstable : (prefixWord ++ tailWord_3133242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133242).length < 2 ^ (prefixWord ++ tailWord_3133242).sum := by decide
  have hdescent : baseEnd_3133242 < baseStart_3133242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133255 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3133255 : Nat := 118140960795 + 3133255 * 2 ^ 59
def prefixEnd_3133255 : Nat := 4983230072969 + 3 ^ 40 * 3133255 * 2
def baseEnd_3133255 : Nat := 1072577218735495906068619

theorem tailTrace_3133255 : CollatzResearch.WordTrace tailWord_3133255 prefixEnd_3133255 1072577218735495906068619 := by
  unfold tailWord_3133255
  simp only [CollatzResearch.WordTrace]
  refine ⟨114279198263759727196241219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76186132175839818130827479 114279198263759727196241219)
  ·
    refine ⟨171418797395639590794361829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114279198263759727196241219 171418797395639590794361829)
    ·
      refine ⟨32141024511682423273942843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171418797395639590794361829 32141024511682423273942843)
      ·
        refine ⟨48211536767523634910914265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32141024511682423273942843 48211536767523634910914265)
        ·
          refine ⟨36158652575642726183185699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48211536767523634910914265 36158652575642726183185699)
          ·
            refine ⟨54237978863464089274778549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36158652575642726183185699 54237978863464089274778549)
            ·
              refine ⟨5084810518449758369510489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54237978863464089274778549 5084810518449758369510489)
              ·
                refine ⟨3813607888837318777132867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5084810518449758369510489 3813607888837318777132867)
                ·
                  refine ⟨5720411833255978165699301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813607888837318777132867 5720411833255978165699301)
                  ·
                    refine ⟨1072577218735495906068619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720411833255978165699301 1072577218735495906068619)
                    ·
                      rfl

theorem cell22_3133255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3133255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133255 prefixEnd_3133255 := by exact prefixLift 3133255
  have htrace : WordTrace (prefixWord ++ tailWord_3133255) baseStart_3133255 baseEnd_3133255 := by
    simpa [prefixWord, tailWord_3133255, baseEnd_3133255] using wordTrace_append hprefix tailTrace_3133255
  have hstable : (prefixWord ++ tailWord_3133255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133255).length < 2 ^ (prefixWord ++ tailWord_3133255).sum := by decide
  have hdescent : baseEnd_3133255 < baseStart_3133255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133315 : List Nat := [1, 1, 1, 3, 4, 3, 3, 6]
def baseStart_3133315 : Nat := 118140960795 + 3133315 * 2 ^ 59
def prefixEnd_3133315 : Nat := 4983230072969 + 3 ^ 40 * 3133315 * 2
def baseEnd_3133315 : Nat := 119177528662408416618715

theorem tailTrace_3133315 : CollatzResearch.WordTrace tailWord_3133315 prefixEnd_3133315 119177528662408416618715 := by
  unfold tailWord_3133315
  simp only [CollatzResearch.WordTrace]
  refine ⟨114281386643542357443425399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76187591095694904962283599 114281386643542357443425399)
  ·
    refine ⟨171422079965313536165138099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114281386643542357443425399 171422079965313536165138099)
    ·
      refine ⟨257133119947970304247707149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171422079965313536165138099 257133119947970304247707149)
      ·
        refine ⟨96424919980488864092890181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257133119947970304247707149 96424919980488864092890181)
        ·
          refine ⟨18079672496341662017416909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96424919980488864092890181 18079672496341662017416909)
          ·
            refine ⟨6779877186128123256531341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18079672496341662017416909 6779877186128123256531341)
            ·
              refine ⟨2542453944798046221199253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6779877186128123256531341 2542453944798046221199253)
              ·
                refine ⟨119177528662408416618715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2542453944798046221199253 119177528662408416618715)
                ·
                  rfl

theorem cell22_3133315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 6].length) (baseStart_3133315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133315 prefixEnd_3133315 := by exact prefixLift 3133315
  have htrace : WordTrace (prefixWord ++ tailWord_3133315) baseStart_3133315 baseEnd_3133315 := by
    simpa [prefixWord, tailWord_3133315, baseEnd_3133315] using wordTrace_append hprefix tailTrace_3133315
  have hstable : (prefixWord ++ tailWord_3133315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133315).length < 2 ^ (prefixWord ++ tailWord_3133315).sum := by decide
  have hdescent : baseEnd_3133315 < baseStart_3133315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133336 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_3133336 : Nat := 118140960795 + 3133336 * 2 ^ 59
def prefixEnd_3133336 : Nat := 4983230072969 + 3 ^ 40 * 3133336 * 2
def baseEnd_3133336 : Nat := 1072604946690838694793371

theorem tailTrace_3133336 : CollatzResearch.WordTrace tailWord_3133336 prefixEnd_3133336 1072604946690838694793371 := by
  unfold tailWord_3133336
  simp only [CollatzResearch.WordTrace]
  refine ⟨57141076288233139014969931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76188101717644185353293241 57141076288233139014969931)
  ·
    refine ⟨85711614432349708522454897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57141076288233139014969931 85711614432349708522454897)
    ·
      refine ⟨64283710824262281391841173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85711614432349708522454897 64283710824262281391841173)
      ·
        refine ⟨3013298944887294440242555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64283710824262281391841173 3013298944887294440242555)
        ·
          refine ⟨4519948417330941660363833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013298944887294440242555 4519948417330941660363833)
          ·
            refine ⟨3389961312998206245272875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4519948417330941660363833 3389961312998206245272875)
            ·
              refine ⟨5084941969497309367909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389961312998206245272875 5084941969497309367909313)
              ·
                refine ⟨3813706477122982025931985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5084941969497309367909313 3813706477122982025931985)
                ·
                  refine ⟨2860279857842236519448989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813706477122982025931985 2860279857842236519448989)
                  ·
                    refine ⟨1072604946690838694793371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860279857842236519448989 1072604946690838694793371)
                    ·
                      rfl

theorem cell22_3133336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_3133336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133336 prefixEnd_3133336 := by exact prefixLift 3133336
  have htrace : WordTrace (prefixWord ++ tailWord_3133336) baseStart_3133336 baseEnd_3133336 := by
    simpa [prefixWord, tailWord_3133336, baseEnd_3133336] using wordTrace_append hprefix tailTrace_3133336
  have hstable : (prefixWord ++ tailWord_3133336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133336).length < 2 ^ (prefixWord ++ tailWord_3133336).sum := by decide
  have hdescent : baseEnd_3133336 < baseStart_3133336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133398 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3133398 : Nat := 118140960795 + 3133398 * 2 ^ 59
def prefixEnd_3133398 : Nat := 4983230072969 + 3 ^ 40 * 3133398 * 2
def baseEnd_3133398 : Nat := 1072626170557891199743181

theorem tailTrace_3133398 : CollatzResearch.WordTrace tailWord_3133398 prefixEnd_3133398 1072626170557891199743181 := by
  unfold tailWord_3133398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142775868890103913668553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76189609268161108412464565 7142775868890103913668553)
  ·
    refine ⟨5357081901667577935251415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7142775868890103913668553 5357081901667577935251415)
    ·
      refine ⟨8035622852501366902877123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357081901667577935251415 8035622852501366902877123)
      ·
        refine ⟨12053434278752050354315685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035622852501366902877123 12053434278752050354315685)
        ·
          refine ⟨2260018927266009441434191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12053434278752050354315685 2260018927266009441434191)
          ·
            refine ⟨3390028390899014162151287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260018927266009441434191 3390028390899014162151287)
            ·
              refine ⟨5085042586348521243226931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390028390899014162151287 5085042586348521243226931)
              ·
                refine ⟨7627563879522781864840397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085042586348521243226931 7627563879522781864840397)
                ·
                  refine ⟨2860336454821043199315149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627563879522781864840397 2860336454821043199315149)
                  ·
                    refine ⟨1072626170557891199743181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860336454821043199315149 1072626170557891199743181)
                    ·
                      rfl

theorem cell22_3133398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3133398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133398 prefixEnd_3133398 := by exact prefixLift 3133398
  have htrace : WordTrace (prefixWord ++ tailWord_3133398) baseStart_3133398 baseEnd_3133398 := by
    simpa [prefixWord, tailWord_3133398, baseEnd_3133398] using wordTrace_append hprefix tailTrace_3133398
  have hstable : (prefixWord ++ tailWord_3133398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133398).length < 2 ^ (prefixWord ++ tailWord_3133398).sum := by decide
  have hdescent : baseEnd_3133398 < baseStart_3133398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133435 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_3133435 : Nat := 118140960795 + 3133435 * 2 ^ 59
def prefixEnd_3133435 : Nat := 4983230072969 + 3 ^ 40 * 3133435 * 2
def baseEnd_3133435 : Nat := 1072638836414035436568067

theorem tailTrace_3133435 : CollatzResearch.WordTrace tailWord_3133435 prefixEnd_3133435 1072638836414035436568067 := by
  unfold tailWord_3133435
  simp only [CollatzResearch.WordTrace]
  refine ⟨114285763403107617937793759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76190508935405078625195839 114285763403107617937793759)
  ·
    refine ⟨171428645104661426906690639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114285763403107617937793759 171428645104661426906690639)
    ·
      refine ⟨257142967656992140360035959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171428645104661426906690639 257142967656992140360035959)
      ·
        refine ⟨385714451485488210540053939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257142967656992140360035959 385714451485488210540053939)
        ·
          refine ⟨578571677228232315810080909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385714451485488210540053939 578571677228232315810080909)
          ·
            refine ⟨216964378960587118428780341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578571677228232315810080909 216964378960587118428780341)
            ·
              refine ⟨20340410527555042352698157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216964378960587118428780341 20340410527555042352698157)
              ·
                refine ⟨7627653947833140882261809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20340410527555042352698157 7627653947833140882261809)
                ·
                  refine ⟨5720740460874855661696357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7627653947833140882261809 5720740460874855661696357)
                  ·
                    refine ⟨1072638836414035436568067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720740460874855661696357 1072638836414035436568067)
                    ·
                      rfl

theorem cell22_3133435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_3133435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133435 prefixEnd_3133435 := by exact prefixLift 3133435
  have htrace : WordTrace (prefixWord ++ tailWord_3133435) baseStart_3133435 baseEnd_3133435 := by
    simpa [prefixWord, tailWord_3133435, baseEnd_3133435] using wordTrace_append hprefix tailTrace_3133435
  have hstable : (prefixWord ++ tailWord_3133435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133435).length < 2 ^ (prefixWord ++ tailWord_3133435).sum := by decide
  have hdescent : baseEnd_3133435 < baseStart_3133435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133450 : List Nat := [3, 1, 2, 2, 4, 10]
def baseStart_3133450 : Nat := 118140960795 + 3133450 * 2 ^ 59
def prefixEnd_3133450 : Nat := 4983230072969 + 3 ^ 40 * 3133450 * 2
def baseEnd_3133450 : Nat := 13242518163217041943741

theorem tailTrace_3133450 : CollatzResearch.WordTrace tailWord_3133450 prefixEnd_3133450 13242518163217041943741 := by
  unfold tailWord_3133450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571577624513318874897451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76190873665368850333059869 28571577624513318874897451)
  ·
    refine ⟨42857366436769978312346177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571577624513318874897451 42857366436769978312346177)
    ·
      refine ⟨32143024827577483734259633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42857366436769978312346177 32143024827577483734259633)
      ·
        refine ⟨24107268620683112800694725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32143024827577483734259633 24107268620683112800694725)
        ·
          refine ⟨4520112866378083650130261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24107268620683112800694725 4520112866378083650130261)
          ·
            refine ⟨13242518163217041943741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4520112866378083650130261 13242518163217041943741)
            ·
              rfl

theorem cell22_3133450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 10].length) (baseStart_3133450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133450 prefixEnd_3133450 := by exact prefixLift 3133450
  have htrace : WordTrace (prefixWord ++ tailWord_3133450) baseStart_3133450 baseEnd_3133450 := by
    simpa [prefixWord, tailWord_3133450, baseEnd_3133450] using wordTrace_append hprefix tailTrace_3133450
  have hstable : (prefixWord ++ tailWord_3133450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133450).length < 2 ^ (prefixWord ++ tailWord_3133450).sum := by decide
  have hdescent : baseEnd_3133450 < baseStart_3133450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133454 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3133454 : Nat := 118140960795 + 3133454 * 2 ^ 59
def prefixEnd_3133454 : Nat := 4983230072969 + 3 ^ 40 * 3133454 * 2
def baseEnd_3133454 : Nat := 1072645340502325720343009

theorem tailTrace_3133454 : CollatzResearch.WordTrace tailWord_3133454 prefixEnd_3133454 1072645340502325720343009 := by
  unfold tailWord_3133454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285807048754848022841927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76190970926692522788490277 14285807048754848022841927)
  ·
    refine ⟨21428710573132272034262891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14285807048754848022841927 21428710573132272034262891)
    ·
      refine ⟨32143065859698408051394337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428710573132272034262891 32143065859698408051394337)
      ·
        refine ⟨24107299394773806038545753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32143065859698408051394337 24107299394773806038545753)
        ·
          refine ⟨18080474546080354528909315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24107299394773806038545753 18080474546080354528909315)
          ·
            refine ⟨27120711819120531793363973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18080474546080354528909315 27120711819120531793363973)
            ·
              refine ⟨5085133466085099711255745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27120711819120531793363973 5085133466085099711255745)
              ·
                refine ⟨3813850099563824783441809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085133466085099711255745 3813850099563824783441809)
                ·
                  refine ⟨2860387574672868587581357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813850099563824783441809 2860387574672868587581357)
                  ·
                    refine ⟨1072645340502325720343009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860387574672868587581357 1072645340502325720343009)
                    ·
                      rfl

theorem cell22_3133454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3133454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133454 prefixEnd_3133454 := by exact prefixLift 3133454
  have htrace : WordTrace (prefixWord ++ tailWord_3133454) baseStart_3133454 baseEnd_3133454 := by
    simpa [prefixWord, tailWord_3133454, baseEnd_3133454] using wordTrace_append hprefix tailTrace_3133454
  have hstable : (prefixWord ++ tailWord_3133454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133454).length < 2 ^ (prefixWord ++ tailWord_3133454).sum := by decide
  have hdescent : baseEnd_3133454 < baseStart_3133454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133589 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_3133589 : Nat := 118140960795 + 3133589 * 2 ^ 59
def prefixEnd_3133589 : Nat := 4983230072969 + 3 ^ 40 * 3133589 * 2
def baseEnd_3133589 : Nat := 1072691553761230368217595

theorem tailTrace_3133589 : CollatzResearch.WordTrace tailWord_3133589 prefixEnd_3133589 1072691553761230368217595 := by
  unfold tailWord_3133589
  simp only [CollatzResearch.WordTrace]
  refine ⟨114291380244549702238899821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76194253496366468159266547 114291380244549702238899821)
  ·
    refine ⟨42859267591706138339587433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114291380244549702238899821 42859267591706138339587433)
    ·
      refine ⟨32144450693779603754690575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42859267591706138339587433 32144450693779603754690575)
      ·
        refine ⟨48216676040669405632035863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32144450693779603754690575 48216676040669405632035863)
        ·
          refine ⟨72325014061004108448053795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48216676040669405632035863 72325014061004108448053795)
          ·
            refine ⟨108487521091506162672080693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72325014061004108448053795 108487521091506162672080693)
            ·
              refine ⟨10170705102328702750507565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108487521091506162672080693 10170705102328702750507565)
              ·
                refine ⟨3814014413373263531440337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10170705102328702750507565 3814014413373263531440337)
                ·
                  refine ⟨2860510810029947648580253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814014413373263531440337 2860510810029947648580253)
                  ·
                    refine ⟨1072691553761230368217595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860510810029947648580253 1072691553761230368217595)
                    ·
                      rfl

theorem cell22_3133589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_3133589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133589 prefixEnd_3133589 := by exact prefixLift 3133589
  have htrace : WordTrace (prefixWord ++ tailWord_3133589) baseStart_3133589 baseEnd_3133589 := by
    simpa [prefixWord, tailWord_3133589, baseEnd_3133589] using wordTrace_append hprefix tailTrace_3133589
  have hstable : (prefixWord ++ tailWord_3133589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133589).length < 2 ^ (prefixWord ++ tailWord_3133589).sum := by decide
  have hdescent : baseEnd_3133589 < baseStart_3133589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133632 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_3133632 : Nat := 118140960795 + 3133632 * 2 ^ 59
def prefixEnd_3133632 : Nat := 4983230072969 + 3 ^ 40 * 3133632 * 2
def baseEnd_3133632 : Nat := 1072706273539992589392463

theorem tailTrace_3133632 : CollatzResearch.WordTrace tailWord_3133632 prefixEnd_3133632 1072706273539992589392463 := by
  unfold tailWord_3133632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57146474291696960291357575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76195299055595947055143433 57146474291696960291357575)
  ·
    refine ⟨85719711437545440437036363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57146474291696960291357575 85719711437545440437036363)
    ·
      refine ⟨128579567156318160655554545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85719711437545440437036363 128579567156318160655554545)
      ·
        refine ⟨96434675367238620491665909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128579567156318160655554545 96434675367238620491665909)
        ·
          refine ⟨9040750815678620671093679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96434675367238620491665909 9040750815678620671093679)
          ·
            refine ⟨13561126223517931006640519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040750815678620671093679 13561126223517931006640519)
            ·
              refine ⟨20341689335276896509960779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13561126223517931006640519 20341689335276896509960779)
              ·
                refine ⟨30512534002915344764941169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20341689335276896509960779 30512534002915344764941169)
                ·
                  refine ⟨22884400502186508573705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30512534002915344764941169 22884400502186508573705877)
                  ·
                    refine ⟨1072706273539992589392463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22884400502186508573705877 1072706273539992589392463)
                    ·
                      rfl

theorem cell22_3133632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_3133632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133632 prefixEnd_3133632 := by exact prefixLift 3133632
  have htrace : WordTrace (prefixWord ++ tailWord_3133632) baseStart_3133632 baseEnd_3133632 := by
    simpa [prefixWord, tailWord_3133632, baseEnd_3133632] using wordTrace_append hprefix tailTrace_3133632
  have hstable : (prefixWord ++ tailWord_3133632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133632).length < 2 ^ (prefixWord ++ tailWord_3133632).sum := by decide
  have hdescent : baseEnd_3133632 < baseStart_3133632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133647 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 5]
def baseStart_3133647 : Nat := 118140960795 + 3133647 * 2 ^ 59
def prefixEnd_3133647 : Nat := 4983230072969 + 3 ^ 40 * 3133647 * 2
def baseEnd_3133647 : Nat := 357570469448845850089139

theorem tailTrace_3133647 : CollatzResearch.WordTrace tailWord_3133647 prefixEnd_3133647 357570469448845850089139 := by
  unfold tailWord_3133647
  simp only [CollatzResearch.WordTrace]
  refine ⟨114293495678339578144511195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76195663785559718763007463 114293495678339578144511195)
  ·
    refine ⟨171440243517509367216766793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114293495678339578144511195 171440243517509367216766793)
    ·
      refine ⟨128580182638132025412575095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171440243517509367216766793 128580182638132025412575095)
      ·
        refine ⟨192870273957198038118862643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128580182638132025412575095 192870273957198038118862643)
        ·
          refine ⟨289305410935797057178293965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192870273957198038118862643 289305410935797057178293965)
          ·
            refine ⟨108489529100923896441860237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289305410935797057178293965 108489529100923896441860237)
            ·
              refine ⟨40683573412846461165697589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108489529100923896441860237 40683573412846461165697589)
              ·
                refine ⟨3814085007454355734284149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40683573412846461165697589 3814085007454355734284149)
                ·
                  refine ⟨357570469448845850089139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814085007454355734284149 357570469448845850089139)
                  ·
                    rfl

theorem cell22_3133647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].length) (baseStart_3133647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133647 prefixEnd_3133647 := by exact prefixLift 3133647
  have htrace : WordTrace (prefixWord ++ tailWord_3133647) baseStart_3133647 baseEnd_3133647 := by
    simpa [prefixWord, tailWord_3133647, baseEnd_3133647] using wordTrace_append hprefix tailTrace_3133647
  have hstable : (prefixWord ++ tailWord_3133647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133647).length < 2 ^ (prefixWord ++ tailWord_3133647).sum := by decide
  have hdescent : baseEnd_3133647 < baseStart_3133647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133698 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3133698 : Nat := 118140960795 + 3133698 * 2 ^ 59
def prefixEnd_3133698 : Nat := 4983230072969 + 3 ^ 40 * 3133698 * 2
def baseEnd_3133698 : Nat := 357576288896263472414087

theorem tailTrace_3133698 : CollatzResearch.WordTrace tailWord_3133698 prefixEnd_3133698 357576288896263472414087 := by
  unfold tailWord_3133698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28573838950288703463654437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76196903867436542569745165 28573838950288703463654437)
  ·
    refine ⟨5357594803179131899435207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28573838950288703463654437 5357594803179131899435207)
    ·
      refine ⟨8036392204768697849152811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357594803179131899435207 8036392204768697849152811)
      ·
        refine ⟨12054588307153046773729217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8036392204768697849152811 12054588307153046773729217)
        ·
          refine ⟨9040941230364785080296913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12054588307153046773729217 9040941230364785080296913)
          ·
            refine ⟨6780705922773588810222685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040941230364785080296913 6780705922773588810222685)
            ·
              refine ⟨2542764721040095803833507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6780705922773588810222685 2542764721040095803833507)
              ·
                refine ⟨3814147081560143705750261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542764721040095803833507 3814147081560143705750261)
                ·
                  refine ⟨357576288896263472414087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814147081560143705750261 357576288896263472414087)
                  ·
                    rfl

theorem cell22_3133698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3133698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133698 prefixEnd_3133698 := by exact prefixLift 3133698
  have htrace : WordTrace (prefixWord ++ tailWord_3133698) baseStart_3133698 baseEnd_3133698 := by
    simpa [prefixWord, tailWord_3133698, baseEnd_3133698] using wordTrace_append hprefix tailTrace_3133698
  have hstable : (prefixWord ++ tailWord_3133698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133698).length < 2 ^ (prefixWord ++ tailWord_3133698).sum := by decide
  have hdescent : baseEnd_3133698 < baseStart_3133698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133754 : List Nat := [3, 1, 1, 1, 4, 3, 2, 7]
def baseStart_3133754 : Nat := 118140960795 + 3133754 * 2 ^ 59
def prefixEnd_3133754 : Nat := 4983230072969 + 3 ^ 40 * 3133754 * 2
def baseEnd_3133754 : Nat := 119194226292580548649121

theorem tailTrace_3133754 : CollatzResearch.WordTrace tailWord_3133754 prefixEnd_3133754 119194226292580548649121 := by
  unfold tailWord_3133754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28574349572237983854664079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76198265525967956945770877 28574349572237983854664079)
  ·
    refine ⟨42861524358356975781996119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28574349572237983854664079 42861524358356975781996119)
    ·
      refine ⟨64292286537535463672994179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42861524358356975781996119 64292286537535463672994179)
      ·
        refine ⟨96438429806303195509491269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64292286537535463672994179 96438429806303195509491269)
        ·
          refine ⟨18082205588681849158029613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96438429806303195509491269 18082205588681849158029613)
          ·
            refine ⟨6780827095755693434261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18082205588681849158029613 6780827095755693434261105)
            ·
              refine ⟨5085620321816770075695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6780827095755693434261105 5085620321816770075695829)
              ·
                refine ⟨119194226292580548649121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5085620321816770075695829 119194226292580548649121)
                ·
                  rfl

theorem cell22_3133754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_3133754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133754 prefixEnd_3133754 := by exact prefixLift 3133754
  have htrace : WordTrace (prefixWord ++ tailWord_3133754) baseStart_3133754 baseEnd_3133754 := by
    simpa [prefixWord, tailWord_3133754, baseEnd_3133754] using wordTrace_append hprefix tailTrace_3133754
  have hstable : (prefixWord ++ tailWord_3133754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133754).length < 2 ^ (prefixWord ++ tailWord_3133754).sum := by decide
  have hdescent : baseEnd_3133754 < baseStart_3133754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133758 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_3133758 : Nat := 118140960795 + 3133758 * 2 ^ 59
def prefixEnd_3133758 : Nat := 4983230072969 + 3 ^ 40 * 3133758 * 2
def baseEnd_3133758 : Nat := 1072749405914970260742077

theorem tailTrace_3133758 : CollatzResearch.WordTrace tailWord_3133758 prefixEnd_3133758 1072749405914970260742077 := by
  unfold tailWord_3133758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287193022617180512725241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76198362787291629401201285 14287193022617180512725241)
  ·
    refine ⟨10715394766962885384543931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14287193022617180512725241 10715394766962885384543931)
    ·
      refine ⟨16073092150444328076815897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10715394766962885384543931 16073092150444328076815897)
      ·
        refine ⟨12054819112833246057611923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16073092150444328076815897 12054819112833246057611923)
        ·
          refine ⟨18082228669249869086417885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12054819112833246057611923 18082228669249869086417885)
          ·
            refine ⟨6780835750968700907406707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18082228669249869086417885 6780835750968700907406707)
            ·
              refine ⟨10171253626453051361110061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780835750968700907406707 10171253626453051361110061)
              ·
                refine ⟨3814220109919894260416273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10171253626453051361110061 3814220109919894260416273)
                ·
                  refine ⟨2860665082439920695312205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814220109919894260416273 2860665082439920695312205)
                  ·
                    refine ⟨1072749405914970260742077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860665082439920695312205 1072749405914970260742077)
                    ·
                      rfl

theorem cell22_3133758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_3133758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133758 prefixEnd_3133758 := by exact prefixLift 3133758
  have htrace : WordTrace (prefixWord ++ tailWord_3133758) baseStart_3133758 baseEnd_3133758 := by
    simpa [prefixWord, tailWord_3133758, baseEnd_3133758] using wordTrace_append hprefix tailTrace_3133758
  have hstable : (prefixWord ++ tailWord_3133758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133758).length < 2 ^ (prefixWord ++ tailWord_3133758).sum := by decide
  have hdescent : baseEnd_3133758 < baseStart_3133758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133769 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_3133769 : Nat := 118140960795 + 3133769 * 2 ^ 59
def prefixEnd_3133769 : Nat := 4983230072969 + 3 ^ 40 * 3133769 * 2
def baseEnd_3133769 : Nat := 1072753171439769898717043

theorem tailTrace_3133769 : CollatzResearch.WordTrace tailWord_3133769 prefixEnd_3133769 1072753171439769898717043 := by
  unfold tailWord_3133769
  simp only [CollatzResearch.WordTrace]
  refine ⟨114297945383897592980452361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76198630255931728653634907 114297945383897592980452361)
  ·
    refine ⟨85723459037923194735339271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114297945383897592980452361 85723459037923194735339271)
    ·
      refine ⟨128585188556884792103008907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85723459037923194735339271 128585188556884792103008907)
      ·
        refine ⟨192877782835327188154513361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128585188556884792103008907 192877782835327188154513361)
        ·
          refine ⟨144658337126495391115885021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192877782835327188154513361 144658337126495391115885021)
          ·
            refine ⟨54246876422435771668456883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144658337126495391115885021 54246876422435771668456883)
            ·
              refine ⟨81370314633653657502685325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54246876422435771668456883 81370314633653657502685325)
              ·
                refine ⟨30513867987620121563506997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81370314633653657502685325 30513867987620121563506997)
                ·
                  refine ⟨2860675123839386396578781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30513867987620121563506997 2860675123839386396578781)
                  ·
                    refine ⟨1072753171439769898717043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860675123839386396578781 1072753171439769898717043)
                    ·
                      rfl

theorem cell22_3133769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_3133769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133769 prefixEnd_3133769 := by exact prefixLift 3133769
  have htrace : WordTrace (prefixWord ++ tailWord_3133769) baseStart_3133769 baseEnd_3133769 := by
    simpa [prefixWord, tailWord_3133769, baseEnd_3133769] using wordTrace_append hprefix tailTrace_3133769
  have hstable : (prefixWord ++ tailWord_3133769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133769).length < 2 ^ (prefixWord ++ tailWord_3133769).sum := by decide
  have hdescent : baseEnd_3133769 < baseStart_3133769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133861 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 4]
def baseStart_3133861 : Nat := 118140960795 + 3133861 * 2 ^ 59
def prefixEnd_3133861 : Nat := 4983230072969 + 3 ^ 40 * 3133861 * 2
def baseEnd_3133861 : Nat := 357594888306637441805587

theorem tailTrace_3133861 : CollatzResearch.WordTrace tailWord_3133861 prefixEnd_3133861 357594888306637441805587 := by
  unfold tailWord_3133861
  simp only [CollatzResearch.WordTrace]
  refine ⟨114301300899564292692801437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76200867266376195128534291 114301300899564292692801437)
  ·
    refine ⟨42862987837336609759800539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114301300899564292692801437 42862987837336609759800539)
    ·
      refine ⟨64294481756004914639700809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42862987837336609759800539 64294481756004914639700809)
      ·
        refine ⟨48220861317003685979775607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64294481756004914639700809 48220861317003685979775607)
        ·
          refine ⟨72331291975505528969663411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48220861317003685979775607 72331291975505528969663411)
          ·
            refine ⟨108496937963258293454495117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72331291975505528969663411 108496937963258293454495117)
            ·
              refine ⟨40686351736221860045435669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108496937963258293454495117 40686351736221860045435669)
              ·
                refine ⟨1907172737635399689629797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40686351736221860045435669 1907172737635399689629797)
                ·
                  refine ⟨357594888306637441805587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907172737635399689629797 357594888306637441805587)
                  ·
                    rfl

theorem cell22_3133861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_3133861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133861 prefixEnd_3133861 := by exact prefixLift 3133861
  have htrace : WordTrace (prefixWord ++ tailWord_3133861) baseStart_3133861 baseEnd_3133861 := by
    simpa [prefixWord, tailWord_3133861, baseEnd_3133861] using wordTrace_append hprefix tailTrace_3133861
  have hstable : (prefixWord ++ tailWord_3133861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133861).length < 2 ^ (prefixWord ++ tailWord_3133861).sum := by decide
  have hdescent : baseEnd_3133861 < baseStart_3133861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133874 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3133874 : Nat := 118140960795 + 3133874 * 2 ^ 59
def prefixEnd_3133874 : Nat := 4983230072969 + 3 ^ 40 * 3133874 * 2
def baseEnd_3133874 : Nat := 1072789115085584624841721

theorem tailTrace_3133874 : CollatzResearch.WordTrace tailWord_3133874 prefixEnd_3133874 1072789115085584624841721 := by
  unfold tailWord_3133874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28575443762129298978256169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76201183365678130608683117 28575443762129298978256169)
  ·
    refine ⟨21431582821596974233692127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28575443762129298978256169 21431582821596974233692127)
    ·
      refine ⟨32147374232395461350538191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21431582821596974233692127 32147374232395461350538191)
      ·
        refine ⟨48221061348593192025807287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32147374232395461350538191 48221061348593192025807287)
        ·
          refine ⟨72331592022889788038710931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48221061348593192025807287 72331592022889788038710931)
          ·
            refine ⟨108497388034334682058066397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72331592022889788038710931 108497388034334682058066397)
            ·
              refine ⟨40686520512875505771774899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108497388034334682058066397 40686520512875505771774899)
              ·
                refine ⟨61029780769313258657662349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40686520512875505771774899 61029780769313258657662349)
                ·
                  refine ⟨22886167788492471996623381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61029780769313258657662349 22886167788492471996623381)
                  ·
                    refine ⟨1072789115085584624841721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22886167788492471996623381 1072789115085584624841721)
                    ·
                      rfl

theorem cell22_3133874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3133874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133874 prefixEnd_3133874 := by exact prefixLift 3133874
  have htrace : WordTrace (prefixWord ++ tailWord_3133874) baseStart_3133874 baseEnd_3133874 := by
    simpa [prefixWord, tailWord_3133874, baseEnd_3133874] using wordTrace_append hprefix tailTrace_3133874
  have hstable : (prefixWord ++ tailWord_3133874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133874).length < 2 ^ (prefixWord ++ tailWord_3133874).sum := by decide
  have hdescent : baseEnd_3133874 < baseStart_3133874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133908 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3133908 : Nat := 118140960795 + 3133908 * 2 ^ 59
def prefixEnd_3133908 : Nat := 4983230072969 + 3 ^ 40 * 3133908 * 2
def baseEnd_3133908 : Nat := 1072800753980419869491617

theorem tailTrace_3133908 : CollatzResearch.WordTrace tailWord_3133908 prefixEnd_3133908 1072800753980419869491617 := by
  unfold tailWord_3133908
  simp only [CollatzResearch.WordTrace]
  refine ⟨57151507565197009859881189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76202010086929346479841585 57151507565197009859881189)
  ·
    refine ⟨10715907668474439348727723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57151507565197009859881189 10715907668474439348727723)
    ·
      refine ⟨16073861502711659023091585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10715907668474439348727723 16073861502711659023091585)
      ·
        refine ⟨12055396127033744267318689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16073861502711659023091585 12055396127033744267318689)
        ·
          refine ⟨9041547095275308200489017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12055396127033744267318689 9041547095275308200489017)
          ·
            refine ⟨6781160321456481150366763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9041547095275308200489017 6781160321456481150366763)
            ·
              refine ⟨10171740482184721725550145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781160321456481150366763 10171740482184721725550145)
              ·
                refine ⟨7628805361638541294162609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10171740482184721725550145 7628805361638541294162609)
                ·
                  refine ⟨5721604021228905970621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7628805361638541294162609 5721604021228905970621957)
                  ·
                    refine ⟨1072800753980419869491617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721604021228905970621957 1072800753980419869491617)
                    ·
                      rfl

theorem cell22_3133908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3133908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133908 prefixEnd_3133908 := by exact prefixLift 3133908
  have htrace : WordTrace (prefixWord ++ tailWord_3133908) baseStart_3133908 baseEnd_3133908 := by
    simpa [prefixWord, tailWord_3133908, baseEnd_3133908] using wordTrace_append hprefix tailTrace_3133908
  have hstable : (prefixWord ++ tailWord_3133908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133908).length < 2 ^ (prefixWord ++ tailWord_3133908).sum := by decide
  have hdescent : baseEnd_3133908 < baseStart_3133908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133910 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3133910 : Nat := 118140960795 + 3133910 * 2 ^ 59
def prefixEnd_3133910 : Nat := 4983230072969 + 3 ^ 40 * 3133910 * 2
def baseEnd_3133910 : Nat := 1072801438621292530941611

theorem tailTrace_3133910 : CollatzResearch.WordTrace tailWord_3133910 prefixEnd_3133910 1072801438621292530941611 := by
  unfold tailWord_3133910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143943004774173378833449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76202058717591182707556789 7143943004774173378833449)
  ·
    refine ⟨5357957253580630034125087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7143943004774173378833449 5357957253580630034125087)
    ·
      refine ⟨8036935880370945051187631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357957253580630034125087 8036935880370945051187631)
      ·
        refine ⟨12055403820556417576781447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8036935880370945051187631 12055403820556417576781447)
        ·
          refine ⟨18083105730834626365172171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055403820556417576781447 18083105730834626365172171)
          ·
            refine ⟨27124658596251939547758257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083105730834626365172171 27124658596251939547758257)
            ·
              refine ⟨20343493947188954660818693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27124658596251939547758257 20343493947188954660818693)
              ·
                refine ⟨3814405115097928998903505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20343493947188954660818693 3814405115097928998903505)
                ·
                  refine ⟨2860803836323446749177629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814405115097928998903505 2860803836323446749177629)
                  ·
                    refine ⟨1072801438621292530941611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860803836323446749177629 1072801438621292530941611)
                    ·
                      rfl

theorem cell22_3133910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3133910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133910 prefixEnd_3133910 := by exact prefixLift 3133910
  have htrace : WordTrace (prefixWord ++ tailWord_3133910) baseStart_3133910 baseEnd_3133910 := by
    simpa [prefixWord, tailWord_3133910, baseEnd_3133910] using wordTrace_append hprefix tailTrace_3133910
  have hstable : (prefixWord ++ tailWord_3133910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133910).length < 2 ^ (prefixWord ++ tailWord_3133910).sum := by decide
  have hdescent : baseEnd_3133910 < baseStart_3133910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133979 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 12]
def baseStart_3133979 : Nat := 118140960795 + 3133979 * 2 ^ 59
def prefixEnd_3133979 : Nat := 4983230072969 + 3 ^ 40 * 3133979 * 2
def baseEnd_3133979 : Nat := 357608352910466450322133

theorem tailTrace_3133979 : CollatzResearch.WordTrace tailWord_3133979 prefixEnd_3133979 357608352910466450322133 := by
  unfold tailWord_3133979
  simp only [CollatzResearch.WordTrace]
  refine ⟨114305604713136798845596991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76203736475424532563731327 114305604713136798845596991)
  ·
    refine ⟨171458407069705198268395487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114305604713136798845596991 171458407069705198268395487)
    ·
      refine ⟨257187610604557797402593231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171458407069705198268395487 257187610604557797402593231)
      ·
        refine ⟨385781415906836696103889847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257187610604557797402593231 385781415906836696103889847)
        ·
          refine ⟨578672123860255044155834771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385781415906836696103889847 578672123860255044155834771)
          ·
            refine ⟨868008185790382566233752157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578672123860255044155834771 868008185790382566233752157)
            ·
              refine ⟨325503069671393462337657059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868008185790382566233752157 325503069671393462337657059)
              ·
                refine ⟨488254604507090193506485589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325503069671393462337657059 488254604507090193506485589)
                ·
                  refine ⟨357608352910466450322133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 488254604507090193506485589 357608352910466450322133)
                  ·
                    rfl

theorem cell22_3133979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_3133979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3133979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3133979 prefixEnd_3133979 := by exact prefixLift 3133979
  have htrace : WordTrace (prefixWord ++ tailWord_3133979) baseStart_3133979 baseEnd_3133979 := by
    simpa [prefixWord, tailWord_3133979, baseEnd_3133979] using wordTrace_append hprefix tailTrace_3133979
  have hstable : (prefixWord ++ tailWord_3133979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133979).length < 2 ^ (prefixWord ++ tailWord_3133979).sum := by decide
  have hdescent : baseEnd_3133979 < baseStart_3133979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134028 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_3134028 : Nat := 118140960795 + 3134028 * 2 ^ 59
def prefixEnd_3134028 : Nat := 4983230072969 + 3 ^ 40 * 3134028 * 2
def baseEnd_3134028 : Nat := 1072841832432779556491249

theorem tailTrace_3134028 : CollatzResearch.WordTrace tailWord_3134028 prefixEnd_3134028 1072841832432779556491249 := by
  unfold tailWord_3134028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57153695944979640107065369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76204927926639520142753825 57153695944979640107065369)
  ·
    refine ⟨42865271958734730080299027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57153695944979640107065369 42865271958734730080299027)
    ·
      refine ⟨64297907938102095120448541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42865271958734730080299027 64297907938102095120448541)
      ·
        refine ⟨24111715476788285670168203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64297907938102095120448541 24111715476788285670168203)
        ·
          refine ⟨36167573215182428505252305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24111715476788285670168203 36167573215182428505252305)
          ·
            refine ⟨27125679911386821378939229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36167573215182428505252305 27125679911386821378939229)
            ·
              refine ⟨10172129966770058017102211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27125679911386821378939229 10172129966770058017102211)
              ·
                refine ⟨15258194950155087025653317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10172129966770058017102211 15258194950155087025653317)
                ·
                  refine ⟨2860911553154078817309997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15258194950155087025653317 2860911553154078817309997)
                  ·
                    refine ⟨1072841832432779556491249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860911553154078817309997 1072841832432779556491249)
                    ·
                      rfl

theorem cell22_3134028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_3134028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134028 prefixEnd_3134028 := by exact prefixLift 3134028
  have htrace : WordTrace (prefixWord ++ tailWord_3134028) baseStart_3134028 baseEnd_3134028 := by
    simpa [prefixWord, tailWord_3134028, baseEnd_3134028] using wordTrace_append hprefix tailTrace_3134028
  have hstable : (prefixWord ++ tailWord_3134028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134028).length < 2 ^ (prefixWord ++ tailWord_3134028).sum := by decide
  have hdescent : baseEnd_3134028 < baseStart_3134028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134103 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 5]
def baseStart_3134103 : Nat := 118140960795 + 3134103 * 2 ^ 59
def prefixEnd_3134103 : Nat := 4983230072969 + 3 ^ 40 * 3134103 * 2
def baseEnd_3134103 : Nat := 357622502155168120288673

theorem tailTrace_3134103 : CollatzResearch.WordTrace tailWord_3134103 prefixEnd_3134103 357622502155168120288673 := by
  unfold tailWord_3134103
  simp only [CollatzResearch.WordTrace]
  refine ⟨114310127364687568023110963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76206751576458378682073975 114310127364687568023110963)
  ·
    refine ⟨171465191047031352034666445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114310127364687568023110963 171465191047031352034666445)
    ·
      refine ⟨64299446642636757012999917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171465191047031352034666445 64299446642636757012999917)
      ·
        refine ⟨24112292490988783879874969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64299446642636757012999917 24112292490988783879874969)
        ·
          refine ⟨18084219368241587909906227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24112292490988783879874969 18084219368241587909906227)
          ·
            refine ⟨27126329052362381864859341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18084219368241587909906227 27126329052362381864859341)
            ·
              refine ⟨10172373394635893199322253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27126329052362381864859341 10172373394635893199322253)
              ·
                refine ⟨3814640022988459949745845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10172373394635893199322253 3814640022988459949745845)
                ·
                  refine ⟨357622502155168120288673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814640022988459949745845 357622502155168120288673)
                  ·
                    rfl

theorem cell22_3134103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].length) (baseStart_3134103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134103 prefixEnd_3134103 := by exact prefixLift 3134103
  have htrace : WordTrace (prefixWord ++ tailWord_3134103) baseStart_3134103 baseEnd_3134103 := by
    simpa [prefixWord, tailWord_3134103, baseEnd_3134103] using wordTrace_append hprefix tailTrace_3134103
  have hstable : (prefixWord ++ tailWord_3134103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134103).length < 2 ^ (prefixWord ++ tailWord_3134103).sum := by decide
  have hdescent : baseEnd_3134103 < baseStart_3134103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134184 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3134184 : Nat := 118140960795 + 3134184 * 2 ^ 59
def prefixEnd_3134184 : Nat := 4983230072969 + 3 ^ 40 * 3134184 * 2
def baseEnd_3134184 : Nat := 1072895234420847149590771

theorem tailTrace_3134184 : CollatzResearch.WordTrace tailWord_3134184 prefixEnd_3134184 1072895234420847149590771 := by
  unfold tailWord_3134184
  simp only [CollatzResearch.WordTrace]
  refine ⟨57156540838697059428404803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76208721118262745904539737 57156540838697059428404803)
  ·
    refine ⟨85734811258045589142607205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57156540838697059428404803 85734811258045589142607205)
    ·
      refine ⟨16075277110883547964238851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85734811258045589142607205 16075277110883547964238851)
      ·
        refine ⟨24112915666325321946358277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16075277110883547964238851 24112915666325321946358277)
        ·
          refine ⟨4521171687435997864942177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24112915666325321946358277 4521171687435997864942177)
          ·
            refine ⟨3390878765576998398706633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521171687435997864942177 3390878765576998398706633)
            ·
              refine ⟨2543159074182748799029975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390878765576998398706633 2543159074182748799029975)
              ·
                refine ⟨3814738611274123198544963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543159074182748799029975 3814738611274123198544963)
                ·
                  refine ⟨5722107916911184797817445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814738611274123198544963 5722107916911184797817445)
                  ·
                    refine ⟨1072895234420847149590771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722107916911184797817445 1072895234420847149590771)
                    ·
                      rfl

theorem cell22_3134184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3134184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134184 prefixEnd_3134184 := by exact prefixLift 3134184
  have htrace : WordTrace (prefixWord ++ tailWord_3134184) baseStart_3134184 baseEnd_3134184 := by
    simpa [prefixWord, tailWord_3134184, baseEnd_3134184] using wordTrace_append hprefix tailTrace_3134184
  have hstable : (prefixWord ++ tailWord_3134184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134184).length < 2 ^ (prefixWord ++ tailWord_3134184).sum := by decide
  have hdescent : baseEnd_3134184 < baseStart_3134184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134225 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_3134225 : Nat := 118140960795 + 3134225 * 2 ^ 59
def prefixEnd_3134225 : Nat := 4983230072969 + 3 ^ 40 * 3134225 * 2
def baseEnd_3134225 : Nat := 1072909269558736709315645

theorem tailTrace_3134225 : CollatzResearch.WordTrace tailWord_3134225 prefixEnd_3134225 1072909269558736709315645 := by
  unfold tailWord_3134225
  simp only [CollatzResearch.WordTrace]
  refine ⟨114314577070245582859052129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76209718046830388572701419 114314577070245582859052129)
  ·
    refine ⟨85735932802684187144289097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114314577070245582859052129 85735932802684187144289097)
    ·
      refine ⟨64301949602013140358216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85735932802684187144289097 64301949602013140358216823)
      ·
        refine ⟨96452924403019710537325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64301949602013140358216823 96452924403019710537325235)
        ·
          refine ⟨144679386604529565805987853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96452924403019710537325235 144679386604529565805987853)
          ·
            refine ⟨54254769976698587177245445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144679386604529565805987853 54254769976698587177245445)
            ·
              refine ⟨10172769370630985095733521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54254769976698587177245445 10172769370630985095733521)
              ·
                refine ⟨7629577027973238821800141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10172769370630985095733521 7629577027973238821800141)
                ·
                  refine ⟨2861091385489964558175053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7629577027973238821800141 2861091385489964558175053)
                  ·
                    refine ⟨1072909269558736709315645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861091385489964558175053 1072909269558736709315645)
                    ·
                      rfl

theorem cell22_3134225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_3134225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134225 prefixEnd_3134225 := by exact prefixLift 3134225
  have htrace : WordTrace (prefixWord ++ tailWord_3134225) baseStart_3134225 baseEnd_3134225 := by
    simpa [prefixWord, tailWord_3134225, baseEnd_3134225] using wordTrace_append hprefix tailTrace_3134225
  have hstable : (prefixWord ++ tailWord_3134225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134225).length < 2 ^ (prefixWord ++ tailWord_3134225).sum := by decide
  have hdescent : baseEnd_3134225 < baseStart_3134225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134268 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3134268 : Nat := 118140960795 + 3134268 * 2 ^ 59
def prefixEnd_3134268 : Nat := 4983230072969 + 3 ^ 40 * 3134268 * 2
def baseEnd_3134268 : Nat := 1072923989337498930490513

theorem tailTrace_3134268 : CollatzResearch.WordTrace tailWord_3134268 prefixEnd_3134268 1072923989337498930490513 := by
  unfold tailWord_3134268
  simp only [CollatzResearch.WordTrace]
  refine ⟨57158072704544900601433729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76210763606059867468578305 57158072704544900601433729)
  ·
    refine ⟨42868554528408675451075297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57158072704544900601433729 42868554528408675451075297)
    ·
      refine ⟨32151415896306506588306473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42868554528408675451075297 32151415896306506588306473)
      ·
        refine ⟨24113561922229879941229855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32151415896306506588306473 24113561922229879941229855)
        ·
          refine ⟨36170342883344819911844783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24113561922229879941229855 36170342883344819911844783)
          ·
            refine ⟨54255514325017229867767175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36170342883344819911844783 54255514325017229867767175)
            ·
              refine ⟨81383271487525844801650763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54255514325017229867767175 81383271487525844801650763)
              ·
                refine ⟨122074907231288767202476145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81383271487525844801650763 122074907231288767202476145)
                ·
                  refine ⟨91556180423466575401857109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122074907231288767202476145 91556180423466575401857109)
                  ·
                    refine ⟨1072923989337498930490513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91556180423466575401857109 1072923989337498930490513)
                    ·
                      rfl

theorem cell22_3134268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3134268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134268 prefixEnd_3134268 := by exact prefixLift 3134268
  have htrace : WordTrace (prefixWord ++ tailWord_3134268) baseStart_3134268 baseEnd_3134268 := by
    simpa [prefixWord, tailWord_3134268, baseEnd_3134268] using wordTrace_append hprefix tailTrace_3134268
  have hstable : (prefixWord ++ tailWord_3134268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134268).length < 2 ^ (prefixWord ++ tailWord_3134268).sum := by decide
  have hdescent : baseEnd_3134268 < baseStart_3134268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134313 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3134313 : Nat := 118140960795 + 3134313 * 2 ^ 59
def prefixEnd_3134313 : Nat := 4983230072969 + 3 ^ 40 * 3134313 * 2
def baseEnd_3134313 : Nat := 1072939393757133813115375

theorem tailTrace_3134313 : CollatzResearch.WordTrace tailWord_3134313 prefixEnd_3134313 1072939393757133813115375 := by
  unfold tailWord_3134313
  simp only [CollatzResearch.WordTrace]
  refine ⟨114317786693926773888255593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76211857795951182592170395 114317786693926773888255593)
  ·
    refine ⟨85738340020445080416191695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114317786693926773888255593 85738340020445080416191695)
    ·
      refine ⟨128607510030667620624287543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85738340020445080416191695 128607510030667620624287543)
      ·
        refine ⟨192911265046001430936431315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128607510030667620624287543 192911265046001430936431315)
        ·
          refine ⟨289366897569002146404646973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192911265046001430936431315 289366897569002146404646973)
          ·
            refine ⟨108512586588375804901742615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289366897569002146404646973 108512586588375804901742615)
            ·
              refine ⟨162768879882563707352613923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108512586588375804901742615 162768879882563707352613923)
              ·
                refine ⟨244153319823845561028920885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162768879882563707352613923 244153319823845561028920885)
                ·
                  refine ⟨22889373733485521346461333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244153319823845561028920885 22889373733485521346461333)
                  ·
                    refine ⟨1072939393757133813115375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22889373733485521346461333 1072939393757133813115375)
                    ·
                      rfl

theorem cell22_3134313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3134313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134313 prefixEnd_3134313 := by exact prefixLift 3134313
  have htrace : WordTrace (prefixWord ++ tailWord_3134313) baseStart_3134313 baseEnd_3134313 := by
    simpa [prefixWord, tailWord_3134313, baseEnd_3134313] using wordTrace_append hprefix tailTrace_3134313
  have hstable : (prefixWord ++ tailWord_3134313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134313).length < 2 ^ (prefixWord ++ tailWord_3134313).sum := by decide
  have hdescent : baseEnd_3134313 < baseStart_3134313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134315 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 4, 3]
def baseStart_3134315 : Nat := 118140960795 + 3134315 * 2 ^ 59
def prefixEnd_3134315 : Nat := 4983230072969 + 3 ^ 40 * 3134315 * 2
def baseEnd_3134315 : Nat := 1072940078398006474565369

theorem tailTrace_3134315 : CollatzResearch.WordTrace tailWord_3134315 prefixEnd_3134315 1072940078398006474565369 := by
  unfold tailWord_3134315
  simp only [CollatzResearch.WordTrace]
  refine ⟨114317859639919528229828399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76211906426613018819885599 114317859639919528229828399)
  ·
    refine ⟨171476789459879292344742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114317859639919528229828399 171476789459879292344742599)
    ·
      refine ⟨257215184189818938517113899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171476789459879292344742599 257215184189818938517113899)
      ·
        refine ⟨385822776284728407775670849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257215184189818938517113899 385822776284728407775670849)
        ·
          refine ⟨289367082213546305831753137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385822776284728407775670849 289367082213546305831753137)
          ·
            refine ⟨217025311660159729373814853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289367082213546305831753137 217025311660159729373814853)
            ·
              refine ⟨40692245936279949257590285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217025311660159729373814853 40692245936279949257590285)
              ·
                refine ⟨15259592226104980971596357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40692245936279949257590285 15259592226104980971596357)
                ·
                  refine ⟨2861173542394683932174317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15259592226104980971596357 2861173542394683932174317)
                  ·
                    refine ⟨1072940078398006474565369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861173542394683932174317 1072940078398006474565369)
                    ·
                      rfl

theorem cell22_3134315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].length) (baseStart_3134315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134315 prefixEnd_3134315 := by exact prefixLift 3134315
  have htrace : WordTrace (prefixWord ++ tailWord_3134315) baseStart_3134315 baseEnd_3134315 := by
    simpa [prefixWord, tailWord_3134315, baseEnd_3134315] using wordTrace_append hprefix tailTrace_3134315
  have hstable : (prefixWord ++ tailWord_3134315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134315).length < 2 ^ (prefixWord ++ tailWord_3134315).sum := by decide
  have hdescent : baseEnd_3134315 < baseStart_3134315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134328 : List Nat := [2, 1, 2, 1, 1, 1, 1, 13]
def baseStart_3134328 : Nat := 118140960795 + 3134328 * 2 ^ 59
def prefixEnd_3134328 : Nat := 4983230072969 + 3 ^ 40 * 3134328 * 2
def baseEnd_3134328 : Nat := 119216058729297641554481

theorem tailTrace_3134328 : CollatzResearch.WordTrace tailWord_3134328 prefixEnd_3134328 119216058729297641554481 := by
  unfold tailWord_3134328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57159166894436215725025819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76212222525914954300034425 57159166894436215725025819)
  ·
    refine ⟨85738750341654323587538729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57159166894436215725025819 85738750341654323587538729)
    ·
      refine ⟨64304062756240742690654047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85738750341654323587538729 64304062756240742690654047)
      ·
        refine ⟨96456094134361114035981071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64304062756240742690654047 96456094134361114035981071)
        ·
          refine ⟨144684141201541671053971607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96456094134361114035981071 144684141201541671053971607)
          ·
            refine ⟨217026211802312506580957411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144684141201541671053971607 217026211802312506580957411)
            ·
              refine ⟨325539317703468759871436117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217026211802312506580957411 325539317703468759871436117)
              ·
                refine ⟨119216058729297641554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 325539317703468759871436117 119216058729297641554481)
                ·
                  rfl

theorem cell22_3134328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_3134328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134328 prefixEnd_3134328 := by exact prefixLift 3134328
  have htrace : WordTrace (prefixWord ++ tailWord_3134328) baseStart_3134328 baseEnd_3134328 := by
    simpa [prefixWord, tailWord_3134328, baseEnd_3134328] using wordTrace_append hprefix tailTrace_3134328
  have hstable : (prefixWord ++ tailWord_3134328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134328).length < 2 ^ (prefixWord ++ tailWord_3134328).sum := by decide
  have hdescent : baseEnd_3134328 < baseStart_3134328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134334 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3134334 : Nat := 118140960795 + 3134334 * 2 ^ 59
def prefixEnd_3134334 : Nat := 4983230072969 + 3 ^ 40 * 3134334 * 2
def baseEnd_3134334 : Nat := 357648860828765586113437

theorem tailTrace_3134334 : CollatzResearch.WordTrace tailWord_3134334 prefixEnd_3134334 357648860828765586113437 := by
  unfold tailWord_3134334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289819078356336809346257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76212368417900462983180037 14289819078356336809346257)
  ·
    refine ⟨10717364308767252607009693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14289819078356336809346257 10717364308767252607009693)
    ·
      refine ⟨4019011615787719727628635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10717364308767252607009693 4019011615787719727628635)
      ·
        refine ⟨6028517423681579591442953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019011615787719727628635 6028517423681579591442953)
        ·
          refine ⟨4521388067761184693582215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6028517423681579591442953 4521388067761184693582215)
          ·
            refine ⟨6782082101641777040373323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521388067761184693582215 6782082101641777040373323)
            ·
              refine ⟨10173123152462665560559985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782082101641777040373323 10173123152462665560559985)
              ·
                refine ⟨7629842364346999170419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10173123152462665560559985 7629842364346999170419989)
                ·
                  refine ⟨357648860828765586113437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7629842364346999170419989 357648860828765586113437)
                  ·
                    rfl

theorem cell22_3134334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3134334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134334 prefixEnd_3134334 := by exact prefixLift 3134334
  have htrace : WordTrace (prefixWord ++ tailWord_3134334) baseStart_3134334 baseEnd_3134334 := by
    simpa [prefixWord, tailWord_3134334, baseEnd_3134334] using wordTrace_append hprefix tailTrace_3134334
  have hstable : (prefixWord ++ tailWord_3134334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134334).length < 2 ^ (prefixWord ++ tailWord_3134334).sum := by decide
  have hdescent : baseEnd_3134334 < baseStart_3134334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134377 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_3134377 : Nat := 118140960795 + 3134377 * 2 ^ 59
def prefixEnd_3134377 : Nat := 4983230072969 + 3 ^ 40 * 3134377 * 2
def baseEnd_3134377 : Nat := 1072961302265058979515179

theorem tailTrace_3134377 : CollatzResearch.WordTrace tailWord_3134377 prefixEnd_3134377 1072961302265058979515179 := by
  unfold tailWord_3134377
  simp only [CollatzResearch.WordTrace]
  refine ⟨114320120965694912818585385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76213413977129941879056923 114320120965694912818585385)
  ·
    refine ⟨85740090724271184613939039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114320120965694912818585385 85740090724271184613939039)
    ·
      refine ⟨128610136086406776920908559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85740090724271184613939039 128610136086406776920908559)
      ·
        refine ⟨192915204129610165381362839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128610136086406776920908559 192915204129610165381362839)
        ·
          refine ⟨289372806194415248072044259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192915204129610165381362839 289372806194415248072044259)
          ·
            refine ⟨434059209291622872108066389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289372806194415248072044259 434059209291622872108066389)
            ·
              refine ⟨5086631358886205532516403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 434059209291622872108066389 5086631358886205532516403)
              ·
                refine ⟨7629947038329308298774605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086631358886205532516403 7629947038329308298774605)
                ·
                  refine ⟨2861230139373490612040477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7629947038329308298774605 2861230139373490612040477)
                  ·
                    refine ⟨1072961302265058979515179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861230139373490612040477 1072961302265058979515179)
                    ·
                      rfl

theorem cell22_3134377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_3134377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134377 prefixEnd_3134377 := by exact prefixLift 3134377
  have htrace : WordTrace (prefixWord ++ tailWord_3134377) baseStart_3134377 baseEnd_3134377 := by
    simpa [prefixWord, tailWord_3134377, baseEnd_3134377] using wordTrace_append hprefix tailTrace_3134377
  have hstable : (prefixWord ++ tailWord_3134377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134377).length < 2 ^ (prefixWord ++ tailWord_3134377).sum := by decide
  have hdescent : baseEnd_3134377 < baseStart_3134377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134411 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 1, 3]
def baseStart_3134411 : Nat := 118140960795 + 3134411 * 2 ^ 59
def prefixEnd_3134411 : Nat := 4983230072969 + 3 ^ 40 * 3134411 * 2
def baseEnd_3134411 : Nat := 1072972941159894224165075

theorem tailTrace_3134411 : CollatzResearch.WordTrace tailWord_3134411 prefixEnd_3134411 1072972941159894224165075 := by
  unfold tailWord_3134411
  simp only [CollatzResearch.WordTrace]
  refine ⟨114321361047571736625323087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76214240698381157750215391 114321361047571736625323087)
  ·
    refine ⟨171482041571357604937984631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114321361047571736625323087 171482041571357604937984631)
    ·
      refine ⟨257223062357036407406976947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171482041571357604937984631 257223062357036407406976947)
      ·
        refine ⟨385834593535554611110465421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257223062357036407406976947 385834593535554611110465421)
        ·
          refine ⟨144687972575832979166424533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385834593535554611110465421 144687972575832979166424533)
          ·
            refine ⟨3391124357246085449213075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 144687972575832979166424533 3391124357246085449213075)
            ·
              refine ⟨5086686535869128173819613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391124357246085449213075 5086686535869128173819613)
              ·
                refine ⟨1907507450950923065182355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5086686535869128173819613 1907507450950923065182355)
                ·
                  refine ⟨2861261176426384597773533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907507450950923065182355 2861261176426384597773533)
                  ·
                    refine ⟨1072972941159894224165075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861261176426384597773533 1072972941159894224165075)
                    ·
                      rfl

theorem cell22_3134411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 3].length) (baseStart_3134411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134411 prefixEnd_3134411 := by exact prefixLift 3134411
  have htrace : WordTrace (prefixWord ++ tailWord_3134411) baseStart_3134411 baseEnd_3134411 := by
    simpa [prefixWord, tailWord_3134411, baseEnd_3134411] using wordTrace_append hprefix tailTrace_3134411
  have hstable : (prefixWord ++ tailWord_3134411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134411).length < 2 ^ (prefixWord ++ tailWord_3134411).sum := by decide
  have hdescent : baseEnd_3134411 < baseStart_3134411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134413 : List Nat := [1, 6, 3, 1, 2, 1, 8]
def baseStart_3134413 : Nat := 118140960795 + 3134413 * 2 ^ 59
def prefixEnd_3134413 : Nat := 4983230072969 + 3 ^ 40 * 3134413 * 2
def baseEnd_3134413 : Nat := 39739763918546921689447

theorem tailTrace_3134413 : CollatzResearch.WordTrace tailWord_3134413 prefixEnd_3134413 39739763918546921689447 := by
  unfold tailWord_3134413
  simp only [CollatzResearch.WordTrace]
  refine ⟨114321433993564490966895893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76214289329042993977930595 114321433993564490966895893)
  ·
    refine ⟨5358817218448335514073245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114321433993564490966895893 5358817218448335514073245)
    ·
      refine ⟨2009556456918125817777467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5358817218448335514073245 2009556456918125817777467)
      ·
        refine ⟨3014334685377188726666201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009556456918125817777467 3014334685377188726666201)
        ·
          refine ⟨2260751014032891544999651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3014334685377188726666201 2260751014032891544999651)
          ·
            refine ⟨3391126521049337317499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260751014032891544999651 3391126521049337317499477)
            ·
              refine ⟨39739763918546921689447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3391126521049337317499477 39739763918546921689447)
              ·
                rfl

theorem cell22_3134413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 8].length) (baseStart_3134413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134413 prefixEnd_3134413 := by exact prefixLift 3134413
  have htrace : WordTrace (prefixWord ++ tailWord_3134413) baseStart_3134413 baseEnd_3134413 := by
    simpa [prefixWord, tailWord_3134413, baseEnd_3134413] using wordTrace_append hprefix tailTrace_3134413
  have hstable : (prefixWord ++ tailWord_3134413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134413).length < 2 ^ (prefixWord ++ tailWord_3134413).sum := by decide
  have hdescent : baseEnd_3134413 < baseStart_3134413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134454 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3134454 : Nat := 118140960795 + 3134454 * 2 ^ 59
def prefixEnd_3134454 : Nat := 4983230072969 + 3 ^ 40 * 3134454 * 2
def baseEnd_3134454 : Nat := 1072987660938656445339943

theorem tailTrace_3134454 : CollatzResearch.WordTrace tailWord_3134454 prefixEnd_3134454 1072987660938656445339943 := by
  unfold tailWord_3134454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145183086650997185571151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76215286257610636646092277 7145183086650997185571151)
  ·
    refine ⟨10717774629976495778356727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7145183086650997185571151 10717774629976495778356727)
    ·
      refine ⟨16076661944964743667535091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10717774629976495778356727 16076661944964743667535091)
      ·
        refine ⟨24114992917447115501302637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16076661944964743667535091 24114992917447115501302637)
        ·
          refine ⟨9043122344042668312988489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24114992917447115501302637 9043122344042668312988489)
          ·
            refine ⟨6782341758032001234741367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043122344042668312988489 6782341758032001234741367)
            ·
              refine ⟨10173512637048001852112051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782341758032001234741367 10173512637048001852112051)
              ·
                refine ⟨15260268955572002778168077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173512637048001852112051 15260268955572002778168077)
                ·
                  refine ⟨5722600858339501041813029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15260268955572002778168077 5722600858339501041813029)
                  ·
                    refine ⟨1072987660938656445339943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722600858339501041813029 1072987660938656445339943)
                    ·
                      rfl

theorem cell22_3134454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3134454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134454 prefixEnd_3134454 := by exact prefixLift 3134454
  have htrace : WordTrace (prefixWord ++ tailWord_3134454) baseStart_3134454 baseEnd_3134454 := by
    simpa [prefixWord, tailWord_3134454, baseEnd_3134454] using wordTrace_append hprefix tailTrace_3134454
  have hstable : (prefixWord ++ tailWord_3134454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134454).length < 2 ^ (prefixWord ++ tailWord_3134454).sum := by decide
  have hdescent : baseEnd_3134454 < baseStart_3134454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134497 : List Nat := [1, 2, 3, 2, 3, 1, 3, 7]
def baseStart_3134497 : Nat := 118140960795 + 3134497 * 2 ^ 59
def prefixEnd_3134497 : Nat := 4983230072969 + 3 ^ 40 * 3134497 * 2
def baseEnd_3134497 : Nat := 119222486746379851834979

theorem tailTrace_3134497 : CollatzResearch.WordTrace tailWord_3134497 prefixEnd_3134497 119222486746379851834979 := by
  unfold tailWord_3134497
  simp only [CollatzResearch.WordTrace]
  refine ⟨114324497725260173312953745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76216331816840115541969163 114324497725260173312953745)
  ·
    refine ⟨85743373293945129984715309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114324497725260173312953745 85743373293945129984715309)
    ·
      refine ⟨32153764985229423744268241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85743373293945129984715309 32153764985229423744268241)
      ·
        refine ⟨24115323738922067808201181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32153764985229423744268241 24115323738922067808201181)
        ·
          refine ⟨9043246402095775428075443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24115323738922067808201181 9043246402095775428075443)
          ·
            refine ⟨13564869603143663142113165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043246402095775428075443 13564869603143663142113165)
            ·
              refine ⟨5086826101178873678292437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13564869603143663142113165 5086826101178873678292437)
              ·
                refine ⟨119222486746379851834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5086826101178873678292437 119222486746379851834979)
                ·
                  rfl

theorem cell22_3134497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 7].length) (baseStart_3134497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134497 prefixEnd_3134497 := by exact prefixLift 3134497
  have htrace : WordTrace (prefixWord ++ tailWord_3134497) baseStart_3134497 baseEnd_3134497 := by
    simpa [prefixWord, tailWord_3134497, baseEnd_3134497] using wordTrace_append hprefix tailTrace_3134497
  have hstable : (prefixWord ++ tailWord_3134497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134497).length < 2 ^ (prefixWord ++ tailWord_3134497).sum := by decide
  have hdescent : baseEnd_3134497 < baseStart_3134497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134516 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3134516 : Nat := 118140960795 + 3134516 * 2 ^ 59
def prefixEnd_3134516 : Nat := 4983230072969 + 3 ^ 40 * 3134516 * 2
def baseEnd_3134516 : Nat := 1073008884805708950289753

theorem tailTrace_3134516 : CollatzResearch.WordTrace tailWord_3134516 prefixEnd_3134516 1073008884805708950289753 := by
  unfold tailWord_3134516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57162595356095669778947701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76216793808127559705263601 57162595356095669778947701)
  ·
    refine ⟨5358993314633969041776347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57162595356095669778947701 5358993314633969041776347)
    ·
      refine ⟨8038489971950953562664521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358993314633969041776347 8038489971950953562664521)
      ·
        refine ⟨6028867478963215171998391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038489971950953562664521 6028867478963215171998391)
        ·
          refine ⟨9043301218444822757997587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028867478963215171998391 9043301218444822757997587)
          ·
            refine ⟨13564951827667234136996381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043301218444822757997587 13564951827667234136996381)
            ·
              refine ⟨5086856935375212801373643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13564951827667234136996381 5086856935375212801373643)
              ·
                refine ⟨7630285403062819202060465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086856935375212801373643 7630285403062819202060465)
                ·
                  refine ⟨5722714052297114401545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630285403062819202060465 5722714052297114401545349)
                  ·
                    refine ⟨1073008884805708950289753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722714052297114401545349 1073008884805708950289753)
                    ·
                      rfl

theorem cell22_3134516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3134516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134516 prefixEnd_3134516 := by exact prefixLift 3134516
  have htrace : WordTrace (prefixWord ++ tailWord_3134516) baseStart_3134516 baseEnd_3134516 := by
    simpa [prefixWord, tailWord_3134516, baseEnd_3134516] using wordTrace_append hprefix tailTrace_3134516
  have hstable : (prefixWord ++ tailWord_3134516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134516).length < 2 ^ (prefixWord ++ tailWord_3134516).sum := by decide
  have hdescent : baseEnd_3134516 < baseStart_3134516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134542 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3134542 : Nat := 118140960795 + 3134542 * 2 ^ 59
def prefixEnd_3134542 : Nat := 4983230072969 + 3 ^ 40 * 3134542 * 2
def baseEnd_3134542 : Nat := 357672595045684516379891

theorem tailTrace_3134542 : CollatzResearch.WordTrace tailWord_3134542 prefixEnd_3134542 357672595045684516379891 := by
  unfold tailWord_3134542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290767376262143249792735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76217426006731430665561253 14290767376262143249792735)
  ·
    refine ⟨21436151064393214874689103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14290767376262143249792735 21436151064393214874689103)
    ·
      refine ⟨32154226596589822312033655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436151064393214874689103 32154226596589822312033655)
      ·
        refine ⟨48231339894884733468050483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32154226596589822312033655 48231339894884733468050483)
        ·
          refine ⟨72347009842327100202075725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48231339894884733468050483 72347009842327100202075725)
          ·
            refine ⟨27130128690872662575778397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72347009842327100202075725 27130128690872662575778397)
            ·
              refine ⟨10173798259077248465916899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27130128690872662575778397 10173798259077248465916899)
              ·
                refine ⟨15260697388615872698875349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173798259077248465916899 15260697388615872698875349)
                ·
                  refine ⟨357672595045684516379891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15260697388615872698875349 357672595045684516379891)
                  ·
                    rfl

theorem cell22_3134542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3134542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134542 prefixEnd_3134542 := by exact prefixLift 3134542
  have htrace : WordTrace (prefixWord ++ tailWord_3134542) baseStart_3134542 baseEnd_3134542 := by
    simpa [prefixWord, tailWord_3134542, baseEnd_3134542] using wordTrace_append hprefix tailTrace_3134542
  have hstable : (prefixWord ++ tailWord_3134542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134542).length < 2 ^ (prefixWord ++ tailWord_3134542).sum := by decide
  have hdescent : baseEnd_3134542 < baseStart_3134542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134546 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3134546 : Nat := 118140960795 + 3134546 * 2 ^ 59
def prefixEnd_3134546 : Nat := 4983230072969 + 3 ^ 40 * 3134546 * 2
def baseEnd_3134546 : Nat := 1073019154418798872039661

theorem tailTrace_3134546 : CollatzResearch.WordTrace tailWord_3134546 prefixEnd_3134546 1073019154418798872039661 := by
  unfold tailWord_3134546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581571225520663670371873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76217523268055103120991661 28581571225520663670371873)
  ·
    refine ⟨21436178419140497752778905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28581571225520663670371873 21436178419140497752778905)
    ·
      refine ⟨16077133814355373314584179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21436178419140497752778905 16077133814355373314584179)
      ·
        refine ⟨24115700721533059971876269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077133814355373314584179 24115700721533059971876269)
        ·
          refine ⟨9043387770574897489453601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24115700721533059971876269 9043387770574897489453601)
          ·
            refine ⟨6782540827931173117090201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043387770574897489453601 6782540827931173117090201)
            ·
              refine ⟨5086905620948379837817651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6782540827931173117090201 5086905620948379837817651)
              ·
                refine ⟨7630358431422569756726477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086905620948379837817651 7630358431422569756726477)
                ·
                  refine ⟨2861384411783463658772429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7630358431422569756726477 2861384411783463658772429)
                  ·
                    refine ⟨1073019154418798872039661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861384411783463658772429 1073019154418798872039661)
                    ·
                      rfl

theorem cell22_3134546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3134546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134546 prefixEnd_3134546 := by exact prefixLift 3134546
  have htrace : WordTrace (prefixWord ++ tailWord_3134546) baseStart_3134546 baseEnd_3134546 := by
    simpa [prefixWord, tailWord_3134546, baseEnd_3134546] using wordTrace_append hprefix tailTrace_3134546
  have hstable : (prefixWord ++ tailWord_3134546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134546).length < 2 ^ (prefixWord ++ tailWord_3134546).sum := by decide
  have hdescent : baseEnd_3134546 < baseStart_3134546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134559 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 5]
def baseStart_3134559 : Nat := 118140960795 + 3134559 * 2 ^ 59
def prefixEnd_3134559 : Nat := 4983230072969 + 3 ^ 40 * 3134559 * 2
def baseEnd_3134559 : Nat := 357674534861490390488207

theorem tailTrace_3134559 : CollatzResearch.WordTrace tailWord_3134559 prefixEnd_3134559 357674534861490390488207 := by
  unfold tailWord_3134559
  simp only [CollatzResearch.WordTrace]
  refine ⟨114326759051035557901710731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76217839367357038601140487 114326759051035557901710731)
  ·
    refine ⟨171490138576553336852566097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114326759051035557901710731 171490138576553336852566097)
    ·
      refine ⟨128617603932415002639424573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171490138576553336852566097 128617603932415002639424573)
      ·
        refine ⟨48231601474655625989784215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128617603932415002639424573 48231601474655625989784215)
        ·
          refine ⟨72347402211983438984676323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48231601474655625989784215 72347402211983438984676323)
          ·
            refine ⟨108521103317975158477014485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72347402211983438984676323 108521103317975158477014485)
            ·
              refine ⟨2543463359015042776805027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108521103317975158477014485 2543463359015042776805027)
              ·
                refine ⟨3815195038522564165207541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543463359015042776805027 3815195038522564165207541)
                ·
                  refine ⟨357674534861490390488207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815195038522564165207541 357674534861490390488207)
                  ·
                    rfl

theorem cell22_3134559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 5].length) (baseStart_3134559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134559 prefixEnd_3134559 := by exact prefixLift 3134559
  have htrace : WordTrace (prefixWord ++ tailWord_3134559) baseStart_3134559 baseEnd_3134559 := by
    simpa [prefixWord, tailWord_3134559, baseEnd_3134559] using wordTrace_append hprefix tailTrace_3134559
  have hstable : (prefixWord ++ tailWord_3134559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134559).length < 2 ^ (prefixWord ++ tailWord_3134559).sum := by decide
  have hdescent : baseEnd_3134559 < baseStart_3134559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134589 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3134589 : Nat := 118140960795 + 3134589 * 2 ^ 59
def prefixEnd_3134589 : Nat := 4983230072969 + 3 ^ 40 * 3134589 * 2
def baseEnd_3134589 : Nat := 1073033874197561093214529

theorem tailTrace_3134589 : CollatzResearch.WordTrace tailWord_3134589 prefixEnd_3134589 1073033874197561093214529 := by
  unfold tailWord_3134589
  simp only [CollatzResearch.WordTrace]
  refine ⟨114327853240926873025302821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76218568827284582016868547 114327853240926873025302821)
  ·
    refine ⟨21436472482673788692244279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114327853240926873025302821 21436472482673788692244279)
    ·
      refine ⟨32154708724010683038366419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436472482673788692244279 32154708724010683038366419)
      ·
        refine ⟨48232063086016024557549629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32154708724010683038366419 48232063086016024557549629)
        ·
          refine ⟨18087023657256009209081111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48232063086016024557549629 18087023657256009209081111)
          ·
            refine ⟨27130535485884013813621667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18087023657256009209081111 27130535485884013813621667)
            ·
              refine ⟨40695803228826020720432501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27130535485884013813621667 40695803228826020720432501)
              ·
                refine ⟨3815231552702439442540547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40695803228826020720432501 3815231552702439442540547)
                ·
                  refine ⟨5722847329053659163810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815231552702439442540547 5722847329053659163810821)
                  ·
                    refine ⟨1073033874197561093214529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722847329053659163810821 1073033874197561093214529)
                    ·
                      rfl

theorem cell22_3134589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3134589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134589 prefixEnd_3134589 := by exact prefixLift 3134589
  have htrace : WordTrace (prefixWord ++ tailWord_3134589) baseStart_3134589 baseEnd_3134589 := by
    simpa [prefixWord, tailWord_3134589, baseEnd_3134589] using wordTrace_append hprefix tailTrace_3134589
  have hstable : (prefixWord ++ tailWord_3134589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134589).length < 2 ^ (prefixWord ++ tailWord_3134589).sum := by decide
  have hdescent : baseEnd_3134589 < baseStart_3134589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134604 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_3134604 : Nat := 118140960795 + 3134604 * 2 ^ 59
def prefixEnd_3134604 : Nat := 4983230072969 + 3 ^ 40 * 3134604 * 2
def baseEnd_3134604 : Nat := 357679669668035351363161

theorem tailTrace_3134604 : CollatzResearch.WordTrace tailWord_3134604 prefixEnd_3134604 357679669668035351363161 := by
  unfold tailWord_3134604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57164200167936265293549433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76218933557248353724732577 57164200167936265293549433)
  ·
    refine ⟨42873150125952198970162075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57164200167936265293549433 42873150125952198970162075)
    ·
      refine ⟨64309725188928298455243113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42873150125952198970162075 64309725188928298455243113)
      ·
        refine ⟨48232293891696223841432335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64309725188928298455243113 48232293891696223841432335)
        ·
          refine ⟨72348440837544335762148503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48232293891696223841432335 72348440837544335762148503)
          ·
            refine ⟨108522661256316503643222755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72348440837544335762148503 108522661256316503643222755)
            ·
              refine ⟨162783991884474755464834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108522661256316503643222755 162783991884474755464834133)
              ·
                refine ⟨1907624904896188540603525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 162783991884474755464834133 1907624904896188540603525)
                ·
                  refine ⟨357679669668035351363161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907624904896188540603525 357679669668035351363161)
                  ·
                    rfl

theorem cell22_3134604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_3134604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134604 prefixEnd_3134604 := by exact prefixLift 3134604
  have htrace : WordTrace (prefixWord ++ tailWord_3134604) baseStart_3134604 baseEnd_3134604 := by
    simpa [prefixWord, tailWord_3134604, baseEnd_3134604] using wordTrace_append hprefix tailTrace_3134604
  have hstable : (prefixWord ++ tailWord_3134604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134604).length < 2 ^ (prefixWord ++ tailWord_3134604).sum := by decide
  have hdescent : baseEnd_3134604 < baseStart_3134604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134623 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 1, 4]
def baseStart_3134623 : Nat := 118140960795 + 3134623 * 2 ^ 59
def prefixEnd_3134623 : Nat := 4983230072969 + 3 ^ 40 * 3134623 * 2
def baseEnd_3134623 : Nat := 1073045513092396337864425

theorem tailTrace_3134623 : CollatzResearch.WordTrace tailWord_3134623 prefixEnd_3134623 1073045513092396337864425 := by
  unfold tailWord_3134623
  simp only [CollatzResearch.WordTrace]
  refine ⟨114329093322803696832040523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76219395548535797888027015 114329093322803696832040523)
  ·
    refine ⟨171493639984205545248060785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114329093322803696832040523 171493639984205545248060785)
    ·
      refine ⟨128620229988154158936045589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171493639984205545248060785 128620229988154158936045589)
      ·
        refine ⟨6029073280694726200127137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128620229988154158936045589 6029073280694726200127137)
        ·
          refine ⟨4521804960521044650095353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6029073280694726200127137 4521804960521044650095353)
          ·
            refine ⟨3391353720390783487571515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521804960521044650095353 3391353720390783487571515)
            ·
              refine ⟨5087030580586175231357273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391353720390783487571515 5087030580586175231357273)
              ·
                refine ⟨3815272935439631423517955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087030580586175231357273 3815272935439631423517955)
                ·
                  refine ⟨5722909403159447135276933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815272935439631423517955 5722909403159447135276933)
                  ·
                    refine ⟨1073045513092396337864425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722909403159447135276933 1073045513092396337864425)
                    ·
                      rfl

theorem cell22_3134623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_3134623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134623 prefixEnd_3134623 := by exact prefixLift 3134623
  have htrace : WordTrace (prefixWord ++ tailWord_3134623) baseStart_3134623 baseEnd_3134623 := by
    simpa [prefixWord, tailWord_3134623, baseEnd_3134623] using wordTrace_append hprefix tailTrace_3134623
  have hstable : (prefixWord ++ tailWord_3134623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134623).length < 2 ^ (prefixWord ++ tailWord_3134623).sum := by decide
  have hdescent : baseEnd_3134623 < baseStart_3134623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134685 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3134685 : Nat := 118140960795 + 3134685 * 2 ^ 59
def prefixEnd_3134685 : Nat := 4983230072969 + 3 ^ 40 * 3134685 * 2
def baseEnd_3134685 : Nat := 1073066736959448842814235

theorem tailTrace_3134685 : CollatzResearch.WordTrace tailWord_3134685 prefixEnd_3134685 1073066736959448842814235 := by
  unfold tailWord_3134685
  simp only [CollatzResearch.WordTrace]
  refine ⟨114331354648579081420797509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76220903099052720947198339 114331354648579081420797509)
  ·
    refine ⟨21437128996608577766399533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114331354648579081420797509 21437128996608577766399533)
    ·
      refine ⟨8038923373728216662399825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21437128996608577766399533 8038923373728216662399825)
      ·
        refine ⟨6029192530296162496799869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038923373728216662399825 6029192530296162496799869)
        ·
          refine ⟨2260947198861060936299951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6029192530296162496799869 2260947198861060936299951)
          ·
            refine ⟨3391420798291591404449927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260947198861060936299951 3391420798291591404449927)
            ·
              refine ⟨5087131197437387106674891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391420798291591404449927 5087131197437387106674891)
              ·
                refine ⟨7630696796156080660012337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087131197437387106674891 7630696796156080660012337)
                ·
                  refine ⟨5723022597117060495009253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630696796156080660012337 5723022597117060495009253)
                  ·
                    refine ⟨1073066736959448842814235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723022597117060495009253 1073066736959448842814235)
                    ·
                      rfl

theorem cell22_3134685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3134685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134685 prefixEnd_3134685 := by exact prefixLift 3134685
  have htrace : WordTrace (prefixWord ++ tailWord_3134685) baseStart_3134685 baseEnd_3134685 := by
    simpa [prefixWord, tailWord_3134685, baseEnd_3134685] using wordTrace_append hprefix tailTrace_3134685
  have hstable : (prefixWord ++ tailWord_3134685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134685).length < 2 ^ (prefixWord ++ tailWord_3134685).sum := by decide
  have hdescent : baseEnd_3134685 < baseStart_3134685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134698 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_3134698 : Nat := 118140960795 + 3134698 * 2 ^ 59
def prefixEnd_3134698 : Nat := 4983230072969 + 3 ^ 40 * 3134698 * 2
def baseEnd_3134698 : Nat := 1073071187125121142239195

theorem tailTrace_3134698 : CollatzResearch.WordTrace tailWord_3134698 prefixEnd_3134698 1073071187125121142239195 := by
  unfold tailWord_3134698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582957199382996160255187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76221219198354656427347165 28582957199382996160255187)
  ·
    refine ⟨42874435799074494240382781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28582957199382996160255187 42874435799074494240382781)
    ·
      refine ⟨16077913424652935340143543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42874435799074494240382781 16077913424652935340143543)
      ·
        refine ⟨24116870136979403010215315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077913424652935340143543 24116870136979403010215315)
        ·
          refine ⟨36175305205469104515322973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24116870136979403010215315 36175305205469104515322973)
          ·
            refine ⟨13565739452050914193246115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36175305205469104515322973 13565739452050914193246115)
            ·
              refine ⟨20348609178076371289869173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565739452050914193246115 20348609178076371289869173)
              ·
                refine ⟨1907682110444659808425235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20348609178076371289869173 1907682110444659808425235)
                ·
                  refine ⟨2861523165666989712637853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907682110444659808425235 2861523165666989712637853)
                  ·
                    refine ⟨1073071187125121142239195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861523165666989712637853 1073071187125121142239195)
                    ·
                      rfl

theorem cell22_3134698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_3134698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134698 prefixEnd_3134698 := by exact prefixLift 3134698
  have htrace : WordTrace (prefixWord ++ tailWord_3134698) baseStart_3134698 baseEnd_3134698 := by
    simpa [prefixWord, tailWord_3134698, baseEnd_3134698] using wordTrace_append hprefix tailTrace_3134698
  have hstable : (prefixWord ++ tailWord_3134698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134698).length < 2 ^ (prefixWord ++ tailWord_3134698).sum := by decide
  have hdescent : baseEnd_3134698 < baseStart_3134698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134728 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_3134728 : Nat := 118140960795 + 3134728 * 2 ^ 59
def prefixEnd_3134728 : Nat := 4983230072969 + 3 ^ 40 * 3134728 * 2
def baseEnd_3134728 : Nat := 357693818912737021329701

theorem tailTrace_3134728 : CollatzResearch.WordTrace tailWord_3134728 prefixEnd_3134728 357693818912737021329701 := by
  unfold tailWord_3134728
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166461493711649882306419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76221948658282199843075225 57166461493711649882306419)
  ·
    refine ⟨85749692240567474823459629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57166461493711649882306419 85749692240567474823459629)
    ·
      refine ⟨32156134590212803058797361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85749692240567474823459629 32156134590212803058797361)
      ·
        refine ⟨24117100942659602294098021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32156134590212803058797361 24117100942659602294098021)
        ·
          refine ⟨4521956426748675430143379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24117100942659602294098021 4521956426748675430143379)
          ·
            refine ⟨6782934640123013145215069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521956426748675430143379 6782934640123013145215069)
            ·
              refine ⟨2543600490046129929455651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6782934640123013145215069 2543600490046129929455651)
              ·
                refine ⟨3815400735069194894183477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543600490046129929455651 3815400735069194894183477)
                ·
                  refine ⟨357693818912737021329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815400735069194894183477 357693818912737021329701)
                  ·
                    rfl

theorem cell22_3134728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_3134728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134728 prefixEnd_3134728 := by exact prefixLift 3134728
  have htrace : WordTrace (prefixWord ++ tailWord_3134728) baseStart_3134728 baseEnd_3134728 := by
    simpa [prefixWord, tailWord_3134728, baseEnd_3134728] using wordTrace_append hprefix tailTrace_3134728
  have hstable : (prefixWord ++ tailWord_3134728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134728).length < 2 ^ (prefixWord ++ tailWord_3134728).sum := by decide
  have hdescent : baseEnd_3134728 < baseStart_3134728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134771 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 4, 3]
def baseStart_3134771 : Nat := 118140960795 + 3134771 * 2 ^ 59
def prefixEnd_3134771 : Nat := 4983230072969 + 3 ^ 40 * 3134771 * 2
def baseEnd_3134771 : Nat := 1073096176516973285163971

theorem tailTrace_3134771 : CollatzResearch.WordTrace tailWord_3134771 prefixEnd_3134771 1073096176516973285163971 := by
  unfold tailWord_3134771
  simp only [CollatzResearch.WordTrace]
  refine ⟨114334491326267518108428167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76222994217511678738952111 114334491326267518108428167)
  ·
    refine ⟨171501736989401277162642251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114334491326267518108428167 171501736989401277162642251)
    ·
      refine ⟨257252605484101915743963377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171501736989401277162642251 257252605484101915743963377)
      ·
        refine ⟨192939454113076436807972533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257252605484101915743963377 192939454113076436807972533)
        ·
          refine ⟨18088073823100915950747425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192939454113076436807972533 18088073823100915950747425)
          ·
            refine ⟨13566055367325686963060569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18088073823100915950747425 13566055367325686963060569)
            ·
              refine ⟨10174541525494265222295427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13566055367325686963060569 10174541525494265222295427)
              ·
                refine ⟨15261812288241397833443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174541525494265222295427 15261812288241397833443141)
                ·
                  refine ⟨2861589804045262093770589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15261812288241397833443141 2861589804045262093770589)
                  ·
                    refine ⟨1073096176516973285163971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861589804045262093770589 1073096176516973285163971)
                    ·
                      rfl

theorem cell22_3134771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].length) (baseStart_3134771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134771 prefixEnd_3134771 := by exact prefixLift 3134771
  have htrace : WordTrace (prefixWord ++ tailWord_3134771) baseStart_3134771 baseEnd_3134771 := by
    simpa [prefixWord, tailWord_3134771, baseEnd_3134771] using wordTrace_append hprefix tailTrace_3134771
  have hstable : (prefixWord ++ tailWord_3134771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134771).length < 2 ^ (prefixWord ++ tailWord_3134771).sum := by decide
  have hdescent : baseEnd_3134771 < baseStart_3134771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134784 : List Nat := [2, 1, 1, 2, 2, 1, 6, 7]
def baseStart_3134784 : Nat := 118140960795 + 3134784 * 2 ^ 59
def prefixEnd_3134784 : Nat := 4983230072969 + 3 ^ 40 * 3134784 * 2
def baseEnd_3134784 : Nat := 119233402964738398287659

theorem tailTrace_3134784 : CollatzResearch.WordTrace tailWord_3134784 prefixEnd_3134784 119233402964738398287659 := by
  unfold tailWord_3134784
  simp only [CollatzResearch.WordTrace]
  refine ⟨57167482737610210664325703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76223310316813614219100937 57167482737610210664325703)
  ·
    refine ⟨85751224106415315996488555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57167482737610210664325703 85751224106415315996488555)
    ·
      refine ⟨128626836159622973994732833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85751224106415315996488555 128626836159622973994732833)
      ·
        refine ⟨96470127119717230496049625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128626836159622973994732833 96470127119717230496049625)
        ·
          refine ⟨72352595339787922872037219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96470127119717230496049625 72352595339787922872037219)
          ·
            refine ⟨108528893009681884308055829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72352595339787922872037219 108528893009681884308055829)
            ·
              refine ⟨5087291859828838326940117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108528893009681884308055829 5087291859828838326940117)
              ·
                refine ⟨119233402964738398287659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5087291859828838326940117 119233402964738398287659)
                ·
                  rfl

theorem cell22_3134784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_3134784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134784 prefixEnd_3134784 := by exact prefixLift 3134784
  have htrace : WordTrace (prefixWord ++ tailWord_3134784) baseStart_3134784 baseEnd_3134784 := by
    simpa [prefixWord, tailWord_3134784, baseEnd_3134784] using wordTrace_append hprefix tailTrace_3134784
  have hstable : (prefixWord ++ tailWord_3134784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134784).length < 2 ^ (prefixWord ++ tailWord_3134784).sum := by decide
  have hdescent : baseEnd_3134784 < baseStart_3134784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134850 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3134850 : Nat := 118140960795 + 3134850 * 2 ^ 59
def prefixEnd_3134850 : Nat := 4983230072969 + 3 ^ 40 * 3134850 * 2
def baseEnd_3134850 : Nat := 1073123219831443412438729

theorem tailTrace_3134850 : CollatzResearch.WordTrace tailWord_3134850 prefixEnd_3134850 1073123219831443412438729 := by
  unfold tailWord_3134850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28584343173245328650138501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76224915128654209733702669 28584343173245328650138501)
  ·
    refine ⟨5359564344983499121900969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28584343173245328650138501 5359564344983499121900969)
    ·
      refine ⟨4019673258737624341425727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359564344983499121900969 4019673258737624341425727)
      ·
        refine ⟨6029509888106436512138591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019673258737624341425727 6029509888106436512138591)
        ·
          refine ⟨9044264832159654768207887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029509888106436512138591 9044264832159654768207887)
          ·
            refine ⟨13566397248239482152311831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044264832159654768207887 13566397248239482152311831)
            ·
              refine ⟨20349595872359223228467747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13566397248239482152311831 20349595872359223228467747)
              ·
                refine ⟨30524393808538834842701621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20349595872359223228467747 30524393808538834842701621)
                ·
                  refine ⟨2861661919550515766503277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30524393808538834842701621 2861661919550515766503277)
                  ·
                    refine ⟨1073123219831443412438729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861661919550515766503277 1073123219831443412438729)
                    ·
                      rfl

theorem cell22_3134850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3134850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134850 prefixEnd_3134850 := by exact prefixLift 3134850
  have htrace : WordTrace (prefixWord ++ tailWord_3134850) baseStart_3134850 baseEnd_3134850 := by
    simpa [prefixWord, tailWord_3134850, baseEnd_3134850] using wordTrace_append hprefix tailTrace_3134850
  have hstable : (prefixWord ++ tailWord_3134850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134850).length < 2 ^ (prefixWord ++ tailWord_3134850).sum := by decide
  have hdescent : baseEnd_3134850 < baseStart_3134850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134889 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3134889 : Nat := 118140960795 + 3134889 * 2 ^ 59
def prefixEnd_3134889 : Nat := 4983230072969 + 3 ^ 40 * 3134889 * 2
def baseEnd_3134889 : Nat := 1073136570328460310713609

theorem tailTrace_3134889 : CollatzResearch.WordTrace tailWord_3134889 prefixEnd_3134889 1073136570328460310713609 := by
  unfold tailWord_3134889
  simp only [CollatzResearch.WordTrace]
  refine ⟨114338795139840024261223721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76225863426560016174149147 114338795139840024261223721)
  ·
    refine ⟨85754096354880018195917791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114338795139840024261223721 85754096354880018195917791)
    ·
      refine ⟨128631144532320027293876687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85754096354880018195917791 128631144532320027293876687)
      ·
        refine ⟨192946716798480040940815031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128631144532320027293876687 192946716798480040940815031)
        ·
          refine ⟨289420075197720061411222547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192946716798480040940815031 289420075197720061411222547)
          ·
            refine ⟨434130112796580092116833821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289420075197720061411222547 434130112796580092116833821)
            ·
              refine ⟨162798792298717534543812683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434130112796580092116833821 162798792298717534543812683)
              ·
                refine ⟨244198188448076301815719025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162798792298717534543812683 244198188448076301815719025)
                ·
                  refine ⟨183148641336057226361789269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244198188448076301815719025 183148641336057226361789269)
                  ·
                    refine ⟨1073136570328460310713609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183148641336057226361789269 1073136570328460310713609)
                    ·
                      rfl

theorem cell22_3134889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3134889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134889 prefixEnd_3134889 := by exact prefixLift 3134889
  have htrace : WordTrace (prefixWord ++ tailWord_3134889) baseStart_3134889 baseEnd_3134889 := by
    simpa [prefixWord, tailWord_3134889, baseEnd_3134889] using wordTrace_append hprefix tailTrace_3134889
  have hstable : (prefixWord ++ tailWord_3134889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134889).length < 2 ^ (prefixWord ++ tailWord_3134889).sum := by decide
  have hdescent : baseEnd_3134889 < baseStart_3134889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134921 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_3134921 : Nat := 118140960795 + 3134921 * 2 ^ 59
def prefixEnd_3134921 : Nat := 4983230072969 + 3 ^ 40 * 3134921 * 2
def baseEnd_3134921 : Nat := 1073147524582422893913511

theorem tailTrace_3134921 : CollatzResearch.WordTrace tailWord_3134921 prefixEnd_3134921 1073147524582422893913511 := by
  unfold tailWord_3134921
  simp only [CollatzResearch.WordTrace]
  refine ⟨114339962275724093726388617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76226641517149395817592411 114339962275724093726388617)
  ·
    refine ⟨85754971706793070294791463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114339962275724093726388617 85754971706793070294791463)
    ·
      refine ⟨128632457560189605442187195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85754971706793070294791463 128632457560189605442187195)
      ·
        refine ⟨192948686340284408163280793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128632457560189605442187195 192948686340284408163280793)
        ·
          refine ⟨144711514755213306122460595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192948686340284408163280793 144711514755213306122460595)
          ·
            refine ⟨217067272132819959183690893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144711514755213306122460595 217067272132819959183690893)
            ·
              refine ⟨81400227049807484693884085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217067272132819959183690893 81400227049807484693884085)
              ·
                refine ⟨7631271285919451690051633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81400227049807484693884085 7631271285919451690051633)
                ·
                  refine ⟨5723453464439588767538725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631271285919451690051633 5723453464439588767538725)
                  ·
                    refine ⟨1073147524582422893913511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723453464439588767538725 1073147524582422893913511)
                    ·
                      rfl

theorem cell22_3134921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_3134921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134921 prefixEnd_3134921 := by exact prefixLift 3134921
  have htrace : WordTrace (prefixWord ++ tailWord_3134921) baseStart_3134921 baseEnd_3134921 := by
    simpa [prefixWord, tailWord_3134921, baseEnd_3134921] using wordTrace_append hprefix tailTrace_3134921
  have hstable : (prefixWord ++ tailWord_3134921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134921).length < 2 ^ (prefixWord ++ tailWord_3134921).sum := by decide
  have hdescent : baseEnd_3134921 < baseStart_3134921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134938 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_3134938 : Nat := 118140960795 + 3134938 * 2 ^ 59
def prefixEnd_3134938 : Nat := 4983230072969 + 3 ^ 40 * 3134938 * 2
def baseEnd_3134938 : Nat := 1073153344029840516238459

theorem tailTrace_3134938 : CollatzResearch.WordTrace tailWord_3134938 prefixEnd_3134938 1073153344029840516238459 := by
  unfold tailWord_3134938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28585145579165626407439367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76227054877775003753171645 28585145579165626407439367)
  ·
    refine ⟨42877718368748439611159051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28585145579165626407439367 42877718368748439611159051)
    ·
      refine ⟨64316577553122659416738577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42877718368748439611159051 64316577553122659416738577)
      ·
        refine ⟨48237433164841994562553933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64316577553122659416738577 48237433164841994562553933)
        ·
          refine ⟨18089037436815747960957725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48237433164841994562553933 18089037436815747960957725)
          ·
            refine ⟨6783389038805905485359147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18089037436815747960957725 6783389038805905485359147)
            ·
              refine ⟨10175083558208858228038721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783389038805905485359147 10175083558208858228038721)
              ·
                refine ⟨7631312668656643671029041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10175083558208858228038721 7631312668656643671029041)
                ·
                  refine ⟨5723484501492482753271781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631312668656643671029041 5723484501492482753271781)
                  ·
                    refine ⟨1073153344029840516238459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723484501492482753271781 1073153344029840516238459)
                    ·
                      rfl

theorem cell22_3134938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_3134938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134938 prefixEnd_3134938 := by exact prefixLift 3134938
  have htrace : WordTrace (prefixWord ++ tailWord_3134938) baseStart_3134938 baseEnd_3134938 := by
    simpa [prefixWord, tailWord_3134938, baseEnd_3134938] using wordTrace_append hprefix tailTrace_3134938
  have hstable : (prefixWord ++ tailWord_3134938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134938).length < 2 ^ (prefixWord ++ tailWord_3134938).sum := by decide
  have hdescent : baseEnd_3134938 < baseStart_3134938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134957 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3134957 : Nat := 118140960795 + 3134957 * 2 ^ 59
def prefixEnd_3134957 : Nat := 4983230072969 + 3 ^ 40 * 3134957 * 2
def baseEnd_3134957 : Nat := 1073159848118130800013401

theorem tailTrace_3134957 : CollatzResearch.WordTrace tailWord_3134957 prefixEnd_3134957 1073159848118130800013401 := by
  unfold tailWord_3134957
  simp only [CollatzResearch.WordTrace]
  refine ⟨114341275303593671874699125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76227516869062447916466083 114341275303593671874699125)
  ·
    refine ⟨10719494559711906738253043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114341275303593671874699125 10719494559711906738253043)
    ·
      refine ⟨16079241839567860107379565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719494559711906738253043 16079241839567860107379565)
      ·
        refine ⟨6029715689837947540267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16079241839567860107379565 6029715689837947540267337)
        ·
          refine ⟨4522286767378460655200503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6029715689837947540267337 4522286767378460655200503)
          ·
            refine ⟨6783430151067690982800755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522286767378460655200503 6783430151067690982800755)
            ·
              refine ⟨10175145226601536474201133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783430151067690982800755 10175145226601536474201133)
              ·
                refine ⟨3815679459975576177825425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10175145226601536474201133 3815679459975576177825425)
                ·
                  refine ⟨2861759594981682133369069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815679459975576177825425 2861759594981682133369069)
                  ·
                    refine ⟨1073159848118130800013401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861759594981682133369069 1073159848118130800013401)
                    ·
                      rfl

theorem cell22_3134957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3134957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134957 prefixEnd_3134957 := by exact prefixLift 3134957
  have htrace : WordTrace (prefixWord ++ tailWord_3134957) baseStart_3134957 baseEnd_3134957 := by
    simpa [prefixWord, tailWord_3134957, baseEnd_3134957] using wordTrace_append hprefix tailTrace_3134957
  have hstable : (prefixWord ++ tailWord_3134957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134957).length < 2 ^ (prefixWord ++ tailWord_3134957).sum := by decide
  have hdescent : baseEnd_3134957 < baseStart_3134957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134985 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_3134985 : Nat := 118140960795 + 3134985 * 2 ^ 59
def prefixEnd_3134985 : Nat := 4983230072969 + 3 ^ 40 * 3134985 * 2
def baseEnd_3134985 : Nat := 1073169433090348060313315

theorem tailTrace_3134985 : CollatzResearch.WordTrace tailWord_3134985 prefixEnd_3134985 1073169433090348060313315 := by
  unfold tailWord_3134985
  simp only [CollatzResearch.WordTrace]
  refine ⟨114342296547492232656718409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76228197698328155104478939 114342296547492232656718409)
  ·
    refine ⟨85756722410619174492538807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114342296547492232656718409 85756722410619174492538807)
    ·
      refine ⟨128635083615928761738808211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85756722410619174492538807 128635083615928761738808211)
      ·
        refine ⟨192952625423893142608212317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128635083615928761738808211 192952625423893142608212317)
        ·
          refine ⟨72357234533959928478079619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192952625423893142608212317 72357234533959928478079619)
          ·
            refine ⟨108535851800939892717119429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72357234533959928478079619 108535851800939892717119429)
            ·
              refine ⟨20350472212676229884459893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108535851800939892717119429 20350472212676229884459893)
              ·
                refine ⟨1907856769938396551668115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20350472212676229884459893 1907856769938396551668115)
                ·
                  refine ⟨2861785154907594827502173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907856769938396551668115 2861785154907594827502173)
                  ·
                    refine ⟨1073169433090348060313315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861785154907594827502173 1073169433090348060313315)
                    ·
                      rfl

theorem cell22_3134985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_3134985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3134985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3134985 prefixEnd_3134985 := by exact prefixLift 3134985
  have htrace : WordTrace (prefixWord ++ tailWord_3134985) baseStart_3134985 baseEnd_3134985 := by
    simpa [prefixWord, tailWord_3134985, baseEnd_3134985] using wordTrace_append hprefix tailTrace_3134985
  have hstable : (prefixWord ++ tailWord_3134985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134985).length < 2 ^ (prefixWord ++ tailWord_3134985).sum := by decide
  have hdescent : baseEnd_3134985 < baseStart_3134985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135060 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3135060 : Nat := 118140960795 + 3135060 * 2 ^ 59
def prefixEnd_3135060 : Nat := 4983230072969 + 3 ^ 40 * 3135060 * 2
def baseEnd_3135060 : Nat := 357731702374357621562695

theorem tailTrace_3135060 : CollatzResearch.WordTrace tailWord_3135060 prefixEnd_3135060 357731702374357621562695 := by
  unfold tailWord_3135060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57172516011110260232849317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76230021348147013643799089 57172516011110260232849317)
  ·
    refine ⟨10719846752083173793659247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57172516011110260232849317 10719846752083173793659247)
    ·
      refine ⟨16079770128124760690488871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719846752083173793659247 16079770128124760690488871)
      ·
        refine ⟨24119655192187141035733307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079770128124760690488871 24119655192187141035733307)
        ·
          refine ⟨36179482788280711553599961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24119655192187141035733307 36179482788280711553599961)
          ·
            refine ⟨27134612091210533665199971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36179482788280711553599961 27134612091210533665199971)
            ·
              refine ⟨40701918136815800497799957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27134612091210533665199971 40701918136815800497799957)
              ·
                refine ⟨1907902412663240648334373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40701918136815800497799957 1907902412663240648334373)
                ·
                  refine ⟨357731702374357621562695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907902412663240648334373 357731702374357621562695)
                  ·
                    rfl

theorem cell22_3135060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3135060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135060 prefixEnd_3135060 := by exact prefixLift 3135060
  have htrace : WordTrace (prefixWord ++ tailWord_3135060) baseStart_3135060 baseEnd_3135060 := by
    simpa [prefixWord, tailWord_3135060, baseEnd_3135060] using wordTrace_append hprefix tailTrace_3135060
  have hstable : (prefixWord ++ tailWord_3135060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135060).length < 2 ^ (prefixWord ++ tailWord_3135060).sum := by decide
  have hdescent : baseEnd_3135060 < baseStart_3135060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135075 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 5]
def baseStart_3135075 : Nat := 118140960795 + 3135075 * 2 ^ 59
def prefixEnd_3135075 : Nat := 4983230072969 + 3 ^ 40 * 3135075 * 2
def baseEnd_3135075 : Nat := 1073200241929617825563039

theorem tailTrace_3135075 : CollatzResearch.WordTrace tailWord_3135075 prefixEnd_3135075 1073200241929617825563039 := by
  unfold tailWord_3135075
  simp only [CollatzResearch.WordTrace]
  refine ⟨114345579117166178027494679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76230386078110785351663119 114345579117166178027494679)
  ·
    refine ⟨171518368675749267041242019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114345579117166178027494679 171518368675749267041242019)
    ·
      refine ⟨257277553013623900561863029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171518368675749267041242019 257277553013623900561863029)
      ·
        refine ⟨24119770595027240677674659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257277553013623900561863029 24119770595027240677674659)
        ·
          refine ⟨36179655892540861016511989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24119770595027240677674659 36179655892540861016511989)
          ·
            refine ⟨3391842739925705720297999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36179655892540861016511989 3391842739925705720297999)
            ·
              refine ⟨5087764109888558580446999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391842739925705720297999 5087764109888558580446999)
              ·
                refine ⟨7631646164832837870670499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087764109888558580446999 7631646164832837870670499)
                ·
                  refine ⟨11447469247249256806005749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631646164832837870670499 11447469247249256806005749)
                  ·
                    refine ⟨1073200241929617825563039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11447469247249256806005749 1073200241929617825563039)
                    ·
                      rfl

theorem cell22_3135075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].length) (baseStart_3135075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135075 prefixEnd_3135075 := by exact prefixLift 3135075
  have htrace : WordTrace (prefixWord ++ tailWord_3135075) baseStart_3135075 baseEnd_3135075 := by
    simpa [prefixWord, tailWord_3135075, baseEnd_3135075] using wordTrace_append hprefix tailTrace_3135075
  have hstable : (prefixWord ++ tailWord_3135075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135075).length < 2 ^ (prefixWord ++ tailWord_3135075).sum := by decide
  have hdescent : baseEnd_3135075 < baseStart_3135075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135088 : List Nat := [2, 1, 1, 1, 6, 2, 1, 8]
def baseStart_3135088 : Nat := 118140960795 + 3135088 * 2 ^ 59
def prefixEnd_3135088 : Nat := 4983230072969 + 3 ^ 40 * 3135088 * 2
def baseEnd_3135088 : Nat := 119244965788365569443111

theorem tailTrace_3135088 : CollatzResearch.WordTrace tailWord_3135088 prefixEnd_3135088 119244965788365569443111 := by
  unfold tailWord_3135088
  simp only [CollatzResearch.WordTrace]
  refine ⟨57173026633059540623858959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76230702177412720831811945 57173026633059540623858959)
  ·
    refine ⟨85759539949589310935788439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57173026633059540623858959 85759539949589310935788439)
    ·
      refine ⟨128639309924383966403682659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85759539949589310935788439 128639309924383966403682659)
      ·
        refine ⟨192958964886575949605523989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128639309924383966403682659 192958964886575949605523989)
        ·
          refine ⟨9044951479058247637758937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192958964886575949605523989 9044951479058247637758937)
          ·
            refine ⟨6783713609293685728319203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044951479058247637758937 6783713609293685728319203)
            ·
              refine ⟨10175570413940528592478805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783713609293685728319203 10175570413940528592478805)
              ·
                refine ⟨119244965788365569443111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10175570413940528592478805 119244965788365569443111)
                ·
                  rfl

theorem cell22_3135088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_3135088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135088 prefixEnd_3135088 := by exact prefixLift 3135088
  have htrace : WordTrace (prefixWord ++ tailWord_3135088) baseStart_3135088 baseEnd_3135088 := by
    simpa [prefixWord, tailWord_3135088, baseEnd_3135088] using wordTrace_append hprefix tailTrace_3135088
  have hstable : (prefixWord ++ tailWord_3135088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135088).length < 2 ^ (prefixWord ++ tailWord_3135088).sum := by decide
  have hdescent : baseEnd_3135088 < baseStart_3135088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135094 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3135094 : Nat := 118140960795 + 3135094 * 2 ^ 59
def prefixEnd_3135094 : Nat := 4983230072969 + 3 ^ 40 * 3135094 * 2
def baseEnd_3135094 : Nat := 357735582005969369779327

theorem tailTrace_3135094 : CollatzResearch.WordTrace tailWord_3135094 prefixEnd_3135094 357735582005969369779327 := by
  unfold tailWord_3135094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146642006506084017027271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76230848069398229514957557 7146642006506084017027271)
  ·
    refine ⟨10719963009759126025540907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7146642006506084017027271 10719963009759126025540907)
    ·
      refine ⟨16079944514638689038311361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719963009759126025540907 16079944514638689038311361)
      ·
        refine ⟨12059958385979016778733521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16079944514638689038311361 12059958385979016778733521)
        ·
          refine ⟨9044968789484262584050141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12059958385979016778733521 9044968789484262584050141)
          ·
            refine ⟨3391863296056598469018803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9044968789484262584050141 3391863296056598469018803)
            ·
              refine ⟨5087794944084897703528205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391863296056598469018803 5087794944084897703528205)
              ·
                refine ⟨1907923104031836638823077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5087794944084897703528205 1907923104031836638823077)
                ·
                  refine ⟨357735582005969369779327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907923104031836638823077 357735582005969369779327)
                  ·
                    rfl

theorem cell22_3135094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3135094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135094 prefixEnd_3135094 := by exact prefixLift 3135094
  have htrace : WordTrace (prefixWord ++ tailWord_3135094) baseStart_3135094 baseEnd_3135094 := by
    simpa [prefixWord, tailWord_3135094, baseEnd_3135094] using wordTrace_append hprefix tailTrace_3135094
  have hstable : (prefixWord ++ tailWord_3135094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135094).length < 2 ^ (prefixWord ++ tailWord_3135094).sum := by decide
  have hdescent : baseEnd_3135094 < baseStart_3135094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135210 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3135210 : Nat := 118140960795 + 3135210 * 2 ^ 59
def prefixEnd_3135210 : Nat := 4983230072969 + 3 ^ 40 * 3135210 * 2
def baseEnd_3135210 : Nat := 1073246455188522473437625

theorem tailTrace_3135210 : CollatzResearch.WordTrace tailWord_3135210 prefixEnd_3135210 1073246455188522473437625 := by
  unfold tailWord_3135210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587625742919274020914771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76233668647784730722439389 28587625742919274020914771)
  ·
    refine ⟨42881438614378911031372157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28587625742919274020914771 42881438614378911031372157)
    ·
      refine ⟨16080539480392091636764559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42881438614378911031372157 16080539480392091636764559)
      ·
        refine ⟨24120809220588137455146839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16080539480392091636764559 24120809220588137455146839)
        ·
          refine ⟨36181213830882206182720259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120809220588137455146839 36181213830882206182720259)
          ·
            refine ⟨54271820746323309274080389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36181213830882206182720259 54271820746323309274080389)
            ·
              refine ⟨10175966389935620488890073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54271820746323309274080389 10175966389935620488890073)
              ·
                refine ⟨7631974792451715366667555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10175966389935620488890073 7631974792451715366667555)
                ·
                  refine ⟨11447962188677573050001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631974792451715366667555 11447962188677573050001333)
                  ·
                    refine ⟨1073246455188522473437625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11447962188677573050001333 1073246455188522473437625)
                    ·
                      rfl

theorem cell22_3135210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3135210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135210 prefixEnd_3135210 := by exact prefixLift 3135210
  have htrace : WordTrace (prefixWord ++ tailWord_3135210) baseStart_3135210 baseEnd_3135210 := by
    simpa [prefixWord, tailWord_3135210, baseEnd_3135210] using wordTrace_append hprefix tailTrace_3135210
  have hstable : (prefixWord ++ tailWord_3135210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135210).length < 2 ^ (prefixWord ++ tailWord_3135210).sum := by decide
  have hdescent : baseEnd_3135210 < baseStart_3135210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135345 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3135345 : Nat := 118140960795 + 3135345 * 2 ^ 59
def prefixEnd_3135345 : Nat := 4983230072969 + 3 ^ 40 * 3135345 * 2
def baseEnd_3135345 : Nat := 1073292668447427121312211

theorem tailTrace_3135345 : CollatzResearch.WordTrace tailWord_3135345 prefixEnd_3135345 1073292668447427121312211 := by
  unfold tailWord_3135345
  simp only [CollatzResearch.WordTrace]
  refine ⟨114355426826188014139823489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76236951217458676093215659 114355426826188014139823489)
  ·
    refine ⟨85766570119641010604867617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114355426826188014139823489 85766570119641010604867617)
    ·
      refine ⟨64324927589730757953650713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85766570119641010604867617 64324927589730757953650713)
      ·
        refine ⟨48243695692298068465238035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64324927589730757953650713 48243695692298068465238035)
        ·
          refine ⟨72365543538447102697857053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48243695692298068465238035 72365543538447102697857053)
          ·
            refine ⟨27137078826917663511696395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72365543538447102697857053 27137078826917663511696395)
            ·
              refine ⟨40705618240376495267544593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27137078826917663511696395 40705618240376495267544593)
              ·
                refine ⟨30529213680282371450658445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40705618240376495267544593 30529213680282371450658445)
                ·
                  refine ⟨11448455130105889293996917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30529213680282371450658445 11448455130105889293996917)
                  ·
                    refine ⟨1073292668447427121312211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11448455130105889293996917 1073292668447427121312211)
                    ·
                      rfl

theorem cell22_3135345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3135345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135345 prefixEnd_3135345 := by exact prefixLift 3135345
  have htrace : WordTrace (prefixWord ++ tailWord_3135345) baseStart_3135345 baseEnd_3135345 := by
    simpa [prefixWord, tailWord_3135345, baseEnd_3135345] using wordTrace_append hprefix tailTrace_3135345
  have hstable : (prefixWord ++ tailWord_3135345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135345).length < 2 ^ (prefixWord ++ tailWord_3135345).sum := by decide
  have hdescent : baseEnd_3135345 < baseStart_3135345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135360 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_3135360 : Nat := 118140960795 + 3135360 * 2 ^ 59
def prefixEnd_3135360 : Nat := 4983230072969 + 3 ^ 40 * 3135360 * 2
def baseEnd_3135360 : Nat := 1073297803253972082187165

theorem tailTrace_3135360 : CollatzResearch.WordTrace tailWord_3135360 prefixEnd_3135360 1073297803253972082187165 := by
  unfold tailWord_3135360
  simp only [CollatzResearch.WordTrace]
  refine ⟨57177986960566835850809767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76237315947422447801079689 57177986960566835850809767)
  ·
    refine ⟨85766980440850253776214651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57177986960566835850809767 85766980440850253776214651)
    ·
      refine ⟨128650470661275380664321977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85766980440850253776214651 128650470661275380664321977)
      ·
        refine ⟨96487852995956535498241483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128650470661275380664321977 96487852995956535498241483)
        ·
          refine ⟨144731779493934803247362225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96487852995956535498241483 144731779493934803247362225)
          ·
            refine ⟨108548834620451102435521669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144731779493934803247362225 108548834620451102435521669)
            ·
              refine ⟨20352906491334581706660313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108548834620451102435521669 20352906491334581706660313)
              ·
                refine ⟨15264679868500936279995235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20352906491334581706660313 15264679868500936279995235)
                ·
                  refine ⟨22897019802751404419992853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15264679868500936279995235 22897019802751404419992853)
                  ·
                    refine ⟨1073297803253972082187165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22897019802751404419992853 1073297803253972082187165)
                    ·
                      rfl

theorem cell22_3135360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_3135360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135360 prefixEnd_3135360 := by exact prefixLift 3135360
  have htrace : WordTrace (prefixWord ++ tailWord_3135360) baseStart_3135360 baseEnd_3135360 := by
    simpa [prefixWord, tailWord_3135360, baseEnd_3135360] using wordTrace_append hprefix tailTrace_3135360
  have hstable : (prefixWord ++ tailWord_3135360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135360).length < 2 ^ (prefixWord ++ tailWord_3135360).sum := by decide
  have hdescent : baseEnd_3135360 < baseStart_3135360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135377 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3135377 : Nat := 118140960795 + 3135377 * 2 ^ 59
def prefixEnd_3135377 : Nat := 4983230072969 + 3 ^ 40 * 3135377 * 2
def baseEnd_3135377 : Nat := 1073303622701389704512113

theorem tailTrace_3135377 : CollatzResearch.WordTrace tailWord_3135377 prefixEnd_3135377 1073303622701389704512113 := by
  unfold tailWord_3135377
  simp only [CollatzResearch.WordTrace]
  refine ⟨114356593962072083604988385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76237729308048055736658923 114356593962072083604988385)
  ·
    refine ⟨85767445471554062703741289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114356593962072083604988385 85767445471554062703741289)
    ·
      refine ⟨64325584103665547027805967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85767445471554062703741289 64325584103665547027805967)
      ·
        refine ⟨96488376155498320541708951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64325584103665547027805967 96488376155498320541708951)
        ·
          refine ⟨144732564233247480812563427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96488376155498320541708951 144732564233247480812563427)
          ·
            refine ⟨217098846349871221218845141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144732564233247480812563427 217098846349871221218845141)
            ·
              refine ⟨5088254211325106747316683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 217098846349871221218845141 5088254211325106747316683)
              ·
                refine ⟨7632381316987660120975025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088254211325106747316683 7632381316987660120975025)
                ·
                  refine ⟨5724285987740745090731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7632381316987660120975025 5724285987740745090731269)
                  ·
                    refine ⟨1073303622701389704512113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724285987740745090731269 1073303622701389704512113)
                    ·
                      rfl

theorem cell22_3135377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3135377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135377 prefixEnd_3135377 := by exact prefixLift 3135377
  have htrace : WordTrace (prefixWord ++ tailWord_3135377) baseStart_3135377 baseEnd_3135377 := by
    simpa [prefixWord, tailWord_3135377, baseEnd_3135377] using wordTrace_append hprefix tailTrace_3135377
  have hstable : (prefixWord ++ tailWord_3135377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135377).length < 2 ^ (prefixWord ++ tailWord_3135377).sum := by decide
  have hdescent : baseEnd_3135377 < baseStart_3135377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135396 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_3135396 : Nat := 118140960795 + 3135396 * 2 ^ 59
def prefixEnd_3135396 : Nat := 4983230072969 + 3 ^ 40 * 3135396 * 2
def baseEnd_3135396 : Nat := 1073310126789679988287055

theorem tailTrace_3135396 : CollatzResearch.WordTrace tailWord_3135396 prefixEnd_3135396 1073310126789679988287055 := by
  unfold tailWord_3135396
  simp only [CollatzResearch.WordTrace]
  refine ⟨57178643474501624924965021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76238191299335499899953361 57178643474501624924965021)
  ·
    refine ⟨21441991302938109346861883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57178643474501624924965021 21441991302938109346861883)
    ·
      refine ⟨32162986954407164020292825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21441991302938109346861883 32162986954407164020292825)
      ·
        refine ⟨24122240215805373015219619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32162986954407164020292825 24122240215805373015219619)
        ·
          refine ⟨36183360323708059522829429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24122240215805373015219619 36183360323708059522829429)
          ·
            refine ⟨3392190030347630580265259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36183360323708059522829429 3392190030347630580265259)
            ·
              refine ⟨5088285045521445870397889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392190030347630580265259 5088285045521445870397889)
              ·
                refine ⟨3816213784141084402798417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088285045521445870397889 3816213784141084402798417)
                ·
                  refine ⟨2862160338105813302098813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816213784141084402798417 2862160338105813302098813)
                  ·
                    refine ⟨1073310126789679988287055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2862160338105813302098813 1073310126789679988287055)
                    ·
                      rfl

theorem cell22_3135396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_3135396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135396 prefixEnd_3135396 := by exact prefixLift 3135396
  have htrace : WordTrace (prefixWord ++ tailWord_3135396) baseStart_3135396 baseEnd_3135396 := by
    simpa [prefixWord, tailWord_3135396, baseEnd_3135396] using wordTrace_append hprefix tailTrace_3135396
  have hstable : (prefixWord ++ tailWord_3135396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135396).length < 2 ^ (prefixWord ++ tailWord_3135396).sum := by decide
  have hdescent : baseEnd_3135396 < baseStart_3135396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135499 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 4]
def baseStart_3135499 : Nat := 118140960795 + 3135499 * 2 ^ 59
def prefixEnd_3135499 : Nat := 4983230072969 + 3 ^ 40 * 3135499 * 2
def baseEnd_3135499 : Nat := 357781795264874017653913

theorem tailTrace_3135499 : CollatzResearch.WordTrace tailWord_3135499 prefixEnd_3135499 357781795264874017653913 := by
  unfold tailWord_3135499
  simp only [CollatzResearch.WordTrace]
  refine ⟨114361043667630098440929551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76240695778420065627286367 114361043667630098440929551)
  ·
    refine ⟨171541565501445147661394327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114361043667630098440929551 171541565501445147661394327)
    ·
      refine ⟨257312348252167721492091491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171541565501445147661394327 257312348252167721492091491)
      ·
        refine ⟨385968522378251582238137237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257312348252167721492091491 385968522378251582238137237)
        ·
          refine ⟨18092274486480542917412683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 385968522378251582238137237 18092274486480542917412683)
          ·
            refine ⟨27138411729720814376119025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092274486480542917412683 27138411729720814376119025)
            ·
              refine ⟨20353808797290610782089269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27138411729720814376119025 20353808797290610782089269)
              ·
                refine ⟨1908169574745994760820869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20353808797290610782089269 1908169574745994760820869)
                ·
                  refine ⟨357781795264874017653913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908169574745994760820869 357781795264874017653913)
                  ·
                    rfl

theorem cell22_3135499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 4].length) (baseStart_3135499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135499 prefixEnd_3135499 := by exact prefixLift 3135499
  have htrace : WordTrace (prefixWord ++ tailWord_3135499) baseStart_3135499 baseEnd_3135499 := by
    simpa [prefixWord, tailWord_3135499, baseEnd_3135499] using wordTrace_append hprefix tailTrace_3135499
  have hstable : (prefixWord ++ tailWord_3135499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135499).length < 2 ^ (prefixWord ++ tailWord_3135499).sum := by decide
  have hdescent : baseEnd_3135499 < baseStart_3135499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135516 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_3135516 : Nat := 118140960795 + 3135516 * 2 ^ 59
def prefixEnd_3135516 : Nat := 4983230072969 + 3 ^ 40 * 3135516 * 2
def baseEnd_3135516 : Nat := 357783735080679891762229

theorem tailTrace_3135516 : CollatzResearch.WordTrace tailWord_3135516 prefixEnd_3135516 357783735080679891762229 := by
  unfold tailWord_3135516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57180831854284255172149201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76241109139045673562865601 57180831854284255172149201)
  ·
    refine ⟨42885623890713191379111901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57180831854284255172149201 42885623890713191379111901)
    ·
      refine ⟨16082108959017446767166963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42885623890713191379111901 16082108959017446767166963)
      ·
        refine ⟨24123163438526170150750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16082108959017446767166963 24123163438526170150750445)
        ·
          refine ⟨9046186289447313806531417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24123163438526170150750445 9046186289447313806531417)
          ·
            refine ⟨6784639717085485354898563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9046186289447313806531417 6784639717085485354898563)
            ·
              refine ⟨10176959575628228032347845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784639717085485354898563 10176959575628228032347845)
              ·
                refine ⟨1908179920430292756065221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10176959575628228032347845 1908179920430292756065221)
                ·
                  refine ⟨357783735080679891762229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908179920430292756065221 357783735080679891762229)
                  ·
                    rfl

theorem cell22_3135516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_3135516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135516 prefixEnd_3135516 := by exact prefixLift 3135516
  have htrace : WordTrace (prefixWord ++ tailWord_3135516) baseStart_3135516 baseEnd_3135516 := by
    simpa [prefixWord, tailWord_3135516, baseEnd_3135516] using wordTrace_append hprefix tailTrace_3135516
  have hstable : (prefixWord ++ tailWord_3135516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135516).length < 2 ^ (prefixWord ++ tailWord_3135516).sum := by decide
  have hdescent : baseEnd_3135516 < baseStart_3135516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135559 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3135559 : Nat := 118140960795 + 3135559 * 2 ^ 59
def prefixEnd_3135559 : Nat := 4983230072969 + 3 ^ 40 * 3135559 * 2
def baseEnd_3135559 : Nat := 1073365925020801896461555

theorem tailTrace_3135559 : CollatzResearch.WordTrace tailWord_3135559 prefixEnd_3135559 1073365925020801896461555 := by
  unfold tailWord_3135559
  simp only [CollatzResearch.WordTrace]
  refine ⟨114363232047412728688113731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76242154698275152458742487 114363232047412728688113731)
  ·
    refine ⟨171544848071119093032170597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114363232047412728688113731 171544848071119093032170597)
    ·
      refine ⟨32164659013334829943531987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171544848071119093032170597 32164659013334829943531987)
      ·
        refine ⟨48246988520002244915297981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32164659013334829943531987 48246988520002244915297981)
        ·
          refine ⟨18092620695000841843236743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48246988520002244915297981 18092620695000841843236743)
          ·
            refine ⟨27138931042501262764855115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092620695000841843236743 27138931042501262764855115)
            ·
              refine ⟨40708396563751894147282673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138931042501262764855115 40708396563751894147282673)
              ·
                refine ⟨30531297422813920610462005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40708396563751894147282673 30531297422813920610462005)
                ·
                  refine ⟨2862309133388805057230813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30531297422813920610462005 2862309133388805057230813)
                  ·
                    refine ⟨1073365925020801896461555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2862309133388805057230813 1073365925020801896461555)
                    ·
                      rfl

theorem cell22_3135559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3135559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135559 prefixEnd_3135559 := by exact prefixLift 3135559
  have htrace : WordTrace (prefixWord ++ tailWord_3135559) baseStart_3135559 baseEnd_3135559 := by
    simpa [prefixWord, tailWord_3135559, baseEnd_3135559] using wordTrace_append hprefix tailTrace_3135559
  have hstable : (prefixWord ++ tailWord_3135559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135559).length < 2 ^ (prefixWord ++ tailWord_3135559).sum := by decide
  have hdescent : baseEnd_3135559 < baseStart_3135559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135576 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_3135576 : Nat := 118140960795 + 3135576 * 2 ^ 59
def prefixEnd_3135576 : Nat := 4983230072969 + 3 ^ 40 * 3135576 * 2
def baseEnd_3135576 : Nat := 1073371744468219518786503

theorem tailTrace_3135576 : CollatzResearch.WordTrace tailWord_3135576 prefixEnd_3135576 1073371744468219518786503 := by
  unfold tailWord_3135576
  simp only [CollatzResearch.WordTrace]
  refine ⟨57181926044175570295741291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76242568058900760394321721 57181926044175570295741291)
  ·
    refine ⟨85772889066263355443611937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57181926044175570295741291 85772889066263355443611937)
    ·
      refine ⟨64329666799697516582708953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85772889066263355443611937 64329666799697516582708953)
      ·
        refine ⟨48247250099773137437031715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64329666799697516582708953 48247250099773137437031715)
        ·
          refine ⟨72370875149659706155547573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48247250099773137437031715 72370875149659706155547573)
          ·
            refine ⟨6784769545280597452082585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72370875149659706155547573 6784769545280597452082585)
            ·
              refine ⟨5088577158960448089061939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6784769545280597452082585 5088577158960448089061939)
              ·
                refine ⟨7632865738440672133592909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088577158960448089061939 7632865738440672133592909)
                ·
                  refine ⟨2862324651915252050097341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7632865738440672133592909 2862324651915252050097341)
                  ·
                    refine ⟨1073371744468219518786503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2862324651915252050097341 1073371744468219518786503)
                    ·
                      rfl

theorem cell22_3135576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_3135576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135576 prefixEnd_3135576 := by exact prefixLift 3135576
  have htrace : WordTrace (prefixWord ++ tailWord_3135576) baseStart_3135576 baseEnd_3135576 := by
    simpa [prefixWord, tailWord_3135576, baseEnd_3135576] using wordTrace_append hprefix tailTrace_3135576
  have hstable : (prefixWord ++ tailWord_3135576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135576).length < 2 ^ (prefixWord ++ tailWord_3135576).sum := by decide
  have hdescent : baseEnd_3135576 < baseStart_3135576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135582 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3135582 : Nat := 118140960795 + 3135582 * 2 ^ 59
def prefixEnd_3135582 : Nat := 4983230072969 + 3 ^ 40 * 3135582 * 2
def baseEnd_3135582 : Nat := 1073373798390837503136485

theorem tailTrace_3135582 : CollatzResearch.WordTrace tailWord_3135582 prefixEnd_3135582 1073373798390837503136485 := by
  unfold tailWord_3135582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295508865791175452025125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76242713950886269077467333 14295508865791175452025125)
  ·
    refine ⟨2680407912335845397254711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14295508865791175452025125 2680407912335845397254711)
    ·
      refine ⟨4020611868503768095882067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680407912335845397254711 4020611868503768095882067)
      ·
        refine ⟨6030917802755652143823101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020611868503768095882067 6030917802755652143823101)
        ·
          refine ⟨2261594176033369553933663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6030917802755652143823101 2261594176033369553933663)
          ·
            refine ⟨3392391264050054330900495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261594176033369553933663 3392391264050054330900495)
            ·
              refine ⟨5088586896075081496350743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392391264050054330900495 5088586896075081496350743)
              ·
                refine ⟨7632880344112622244526115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088586896075081496350743 7632880344112622244526115)
                ·
                  refine ⟨11449320516168933366789173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632880344112622244526115 11449320516168933366789173)
                  ·
                    refine ⟨1073373798390837503136485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11449320516168933366789173 1073373798390837503136485)
                    ·
                      rfl

theorem cell22_3135582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3135582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135582 prefixEnd_3135582 := by exact prefixLift 3135582
  have htrace : WordTrace (prefixWord ++ tailWord_3135582) baseStart_3135582 baseEnd_3135582 := by
    simpa [prefixWord, tailWord_3135582, baseEnd_3135582] using wordTrace_append hprefix tailTrace_3135582
  have hstable : (prefixWord ++ tailWord_3135582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135582).length < 2 ^ (prefixWord ++ tailWord_3135582).sum := by decide
  have hdescent : baseEnd_3135582 < baseStart_3135582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135640 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_3135640 : Nat := 118140960795 + 3135640 * 2 ^ 59
def prefixEnd_3135640 : Nat := 4983230072969 + 3 ^ 40 * 3135640 * 2
def baseEnd_3135640 : Nat := 357797884325381561728769

theorem tailTrace_3135640 : CollatzResearch.WordTrace tailWord_3135640 prefixEnd_3135640 357797884325381561728769 := by
  unfold tailWord_3135640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57183093180059639760906187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76244124240079519681208249 57183093180059639760906187)
  ·
    refine ⟨85774639770089459641359281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57183093180059639760906187 85774639770089459641359281)
    ·
      refine ⟨64330979827567094731019461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85774639770089459641359281 64330979827567094731019461)
      ·
        refine ⟨12062058717668830262066149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64330979827567094731019461 12062058717668830262066149)
        ·
          refine ⟨2261636009562905674137403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12062058717668830262066149 2261636009562905674137403)
          ·
            refine ⟨3392454014344358511206105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261636009562905674137403 3392454014344358511206105)
            ·
              refine ⟨2544340510758268883404579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392454014344358511206105 2544340510758268883404579)
              ·
                refine ⟨3816510766137403325106869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544340510758268883404579 3816510766137403325106869)
                ·
                  refine ⟨357797884325381561728769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3816510766137403325106869 357797884325381561728769)
                  ·
                    rfl

theorem cell22_3135640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_3135640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135640 prefixEnd_3135640 := by exact prefixLift 3135640
  have htrace : WordTrace (prefixWord ++ tailWord_3135640) baseStart_3135640 baseEnd_3135640 := by
    simpa [prefixWord, tailWord_3135640, baseEnd_3135640] using wordTrace_append hprefix tailTrace_3135640
  have hstable : (prefixWord ++ tailWord_3135640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135640).length < 2 ^ (prefixWord ++ tailWord_3135640).sum := by decide
  have hdescent : baseEnd_3135640 < baseStart_3135640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135715 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 2, 4]
def baseStart_3135715 : Nat := 118140960795 + 3135715 * 2 ^ 59
def prefixEnd_3135715 : Nat := 4983230072969 + 3 ^ 40 * 3135715 * 2
def baseEnd_3135715 : Nat := 1073419327008869489561077

theorem tailTrace_3135715 : CollatzResearch.WordTrace tailWord_3135715 prefixEnd_3135715 1073419327008869489561077 := by
  unfold tailWord_3135715
  simp only [CollatzResearch.WordTrace]
  refine ⟨114368921834847567330792599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76245947889898378220528399 114368921834847567330792599)
  ·
    refine ⟨171553382752271350996188899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114368921834847567330792599 171553382752271350996188899)
    ·
      refine ⟨257330074128407026494283349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171553382752271350996188899 257330074128407026494283349)
      ·
        refine ⟨3015586806192269841729883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 257330074128407026494283349 3015586806192269841729883)
        ·
          refine ⟨4523380209288404762594825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015586806192269841729883 4523380209288404762594825)
          ·
            refine ⟨3392535156966303571946119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523380209288404762594825 3392535156966303571946119)
            ·
              refine ⟨5088802735449455357919179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392535156966303571946119 5088802735449455357919179)
              ·
                refine ⟨7633204103174183036878769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088802735449455357919179 7633204103174183036878769)
                ·
                  refine ⟨5724903077380637277659077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7633204103174183036878769 5724903077380637277659077)
                  ·
                    refine ⟨1073419327008869489561077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724903077380637277659077 1073419327008869489561077)
                    ·
                      rfl

theorem cell22_3135715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].length) (baseStart_3135715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135715 prefixEnd_3135715 := by exact prefixLift 3135715
  have htrace : WordTrace (prefixWord ++ tailWord_3135715) baseStart_3135715 baseEnd_3135715 := by
    simpa [prefixWord, tailWord_3135715, baseEnd_3135715] using wordTrace_append hprefix tailTrace_3135715
  have hstable : (prefixWord ++ tailWord_3135715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135715).length < 2 ^ (prefixWord ++ tailWord_3135715).sum := by decide
  have hdescent : baseEnd_3135715 < baseStart_3135715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135724 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3135724 : Nat := 118140960795 + 3135724 * 2 ^ 59
def prefixEnd_3135724 : Nat := 4983230072969 + 3 ^ 40 * 3135724 * 2
def baseEnd_3135724 : Nat := 357807469297598822028683

theorem tailTrace_3135724 : CollatzResearch.WordTrace tailWord_3135724 prefixEnd_3135724 357807469297598822028683 := by
  unfold tailWord_3135724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57184625045907480933935113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76246166727876641245246817 57184625045907480933935113)
  ·
    refine ⟨42888468784430610700451335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57184625045907480933935113 42888468784430610700451335)
    ·
      refine ⟨64332703176645916050677003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42888468784430610700451335 64332703176645916050677003)
      ·
        refine ⟨96499054764968874076015505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64332703176645916050677003 96499054764968874076015505)
        ·
          refine ⟨72374291073726655557011629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96499054764968874076015505 72374291073726655557011629)
          ·
            refine ⟨27140359152647495833879361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72374291073726655557011629 27140359152647495833879361)
            ·
              refine ⟨20355269364485621875409521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27140359152647495833879361 20355269364485621875409521)
              ·
                refine ⟨15266452023364216406557141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20355269364485621875409521 15266452023364216406557141)
                ·
                  refine ⟨357807469297598822028683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15266452023364216406557141 357807469297598822028683)
                  ·
                    rfl

theorem cell22_3135724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3135724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135724 prefixEnd_3135724 := by exact prefixLift 3135724
  have htrace : WordTrace (prefixWord ++ tailWord_3135724) baseStart_3135724 baseEnd_3135724 := by
    simpa [prefixWord, tailWord_3135724, baseEnd_3135724] using wordTrace_append hprefix tailTrace_3135724
  have hstable : (prefixWord ++ tailWord_3135724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135724).length < 2 ^ (prefixWord ++ tailWord_3135724).sum := by decide
  have hdescent : baseEnd_3135724 < baseStart_3135724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135758 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3135758 : Nat := 118140960795 + 3135758 * 2 ^ 59
def prefixEnd_3135758 : Nat := 4983230072969 + 3 ^ 40 * 3135758 * 2
def baseEnd_3135758 : Nat := 357811348929210570245315

theorem tailTrace_3135758 : CollatzResearch.WordTrace tailWord_3135758 prefixEnd_3135758 357811348929210570245315 := by
  unfold tailWord_3135758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296311271711473209325991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76246993449127857116405285 14296311271711473209325991)
  ·
    refine ⟨21444466907567209813988987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14296311271711473209325991 21444466907567209813988987)
    ·
      refine ⟨32166700361350814720983481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21444466907567209813988987 32166700361350814720983481)
      ·
        refine ⟨24125025271013111040737611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32166700361350814720983481 24125025271013111040737611)
        ·
          refine ⟨36187537906519666561106417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125025271013111040737611 36187537906519666561106417)
          ·
            refine ⟨27140653429889749920829813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36187537906519666561106417 27140653429889749920829813)
            ·
              refine ⟨2544436259052164055077795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27140653429889749920829813 2544436259052164055077795)
              ·
                refine ⟨3816654388578246082616693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544436259052164055077795 3816654388578246082616693)
                ·
                  refine ⟨357811348929210570245315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3816654388578246082616693 357811348929210570245315)
                  ·
                    rfl

theorem cell22_3135758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3135758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135758 prefixEnd_3135758 := by exact prefixLift 3135758
  have htrace : WordTrace (prefixWord ++ tailWord_3135758) baseStart_3135758 baseEnd_3135758 := by
    simpa [prefixWord, tailWord_3135758, baseEnd_3135758] using wordTrace_append hprefix tailTrace_3135758
  have hstable : (prefixWord ++ tailWord_3135758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135758).length < 2 ^ (prefixWord ++ tailWord_3135758).sum := by decide
  have hdescent : baseEnd_3135758 < baseStart_3135758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135771 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 1, 4]
def baseStart_3135771 : Nat := 118140960795 + 3135771 * 2 ^ 59
def prefixEnd_3135771 : Nat := 4983230072969 + 3 ^ 40 * 3135771 * 2
def baseEnd_3135771 : Nat := 1073438496953304010160905

theorem tailTrace_3135771 : CollatzResearch.WordTrace tailWord_3135771 prefixEnd_3135771 1073438496953304010160905 := by
  unfold tailWord_3135771
  simp only [CollatzResearch.WordTrace]
  refine ⟨114370964322644688894831167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76247309548429792596554111 114370964322644688894831167)
  ·
    refine ⟨171556446483967033342246751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114370964322644688894831167 171556446483967033342246751)
    ·
      refine ⟨257334669725950550013370127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171556446483967033342246751 257334669725950550013370127)
      ·
        refine ⟨386002004588925825020055191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257334669725950550013370127 386002004588925825020055191)
        ·
          refine ⟨579003006883388737530082787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386002004588925825020055191 579003006883388737530082787)
          ·
            refine ⟨868504510325083106295124181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579003006883388737530082787 868504510325083106295124181)
            ·
              refine ⟨20355574460744135303791973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 868504510325083106295124181 20355574460744135303791973)
              ·
                refine ⟨3816670211389525369460995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20355574460744135303791973 3816670211389525369460995)
                ·
                  refine ⟨5725005317084288054191493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816670211389525369460995 5725005317084288054191493)
                  ·
                    refine ⟨1073438496953304010160905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725005317084288054191493 1073438496953304010160905)
                    ·
                      rfl

theorem cell22_3135771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_3135771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135771 prefixEnd_3135771 := by exact prefixLift 3135771
  have htrace : WordTrace (prefixWord ++ tailWord_3135771) baseStart_3135771 baseEnd_3135771 := by
    simpa [prefixWord, tailWord_3135771, baseEnd_3135771] using wordTrace_append hprefix tailTrace_3135771
  have hstable : (prefixWord ++ tailWord_3135771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135771).length < 2 ^ (prefixWord ++ tailWord_3135771).sum := by decide
  have hdescent : baseEnd_3135771 < baseStart_3135771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135968 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_3135968 : Nat := 118140960795 + 3135968 * 2 ^ 59
def prefixEnd_3135968 : Nat := 4983230072969 + 3 ^ 40 * 3135968 * 2
def baseEnd_3135968 : Nat := 1073505934079261162985301

theorem tailTrace_3135968 : CollatzResearch.WordTrace tailWord_3135968 prefixEnd_3135968 1073505934079261162985301 := by
  unfold tailWord_3135968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57189074751465495769876279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76252099668620661026501705 57189074751465495769876279)
  ·
    refine ⟨85783612127198243654814419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57189074751465495769876279 85783612127198243654814419)
    ·
      refine ⟨128675418190797365482221629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85783612127198243654814419 128675418190797365482221629)
      ·
        refine ⟨48253281821549012055833111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128675418190797365482221629 48253281821549012055833111)
        ·
          refine ⟨72379922732323518083749667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48253281821549012055833111 72379922732323518083749667)
          ·
            refine ⟨108569884098485277125624501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72379922732323518083749667 108569884098485277125624501)
            ·
              refine ⟨10178426634232994730527297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108569884098485277125624501 10178426634232994730527297)
              ·
                refine ⟨7633819975674746047895473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10178426634232994730527297 7633819975674746047895473)
                ·
                  refine ⟨5725364981756059535921605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7633819975674746047895473 5725364981756059535921605)
                  ·
                    refine ⟨1073505934079261162985301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725364981756059535921605 1073505934079261162985301)
                    ·
                      rfl

theorem cell22_3135968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_3135968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3135968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3135968 prefixEnd_3135968 := by exact prefixLift 3135968
  have htrace : WordTrace (prefixWord ++ tailWord_3135968) baseStart_3135968 baseEnd_3135968 := by
    simpa [prefixWord, tailWord_3135968, baseEnd_3135968] using wordTrace_append hprefix tailTrace_3135968
  have hstable : (prefixWord ++ tailWord_3135968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135968).length < 2 ^ (prefixWord ++ tailWord_3135968).sum := by decide
  have hdescent : baseEnd_3135968 < baseStart_3135968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136088 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3136088 : Nat := 118140960795 + 3136088 * 2 ^ 59
def prefixEnd_3136088 : Nat := 4983230072969 + 3 ^ 40 * 3136088 * 2
def baseEnd_3136088 : Nat := 1073547012531620849984933

theorem tailTrace_3136088 : CollatzResearch.WordTrace tailWord_3136088 prefixEnd_3136088 1073547012531620849984933 := by
  unfold tailWord_3136088
  simp only [CollatzResearch.WordTrace]
  refine ⟨57191263131248126017060459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76255017508330834689413945 57191263131248126017060459)
  ·
    refine ⟨85786894696872189025590689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57191263131248126017060459 85786894696872189025590689)
    ·
      refine ⟨64340171022654141769193017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85786894696872189025590689 64340171022654141769193017)
      ·
        refine ⟨48255128266990606326894763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64340171022654141769193017 48255128266990606326894763)
        ·
          refine ⟨72382692400485909490342145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48255128266990606326894763 72382692400485909490342145)
          ·
            refine ⟨54287019300364432117756609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72382692400485909490342145 54287019300364432117756609)
            ·
              refine ⟨40715264475273324088317457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54287019300364432117756609 40715264475273324088317457)
              ·
                refine ⟨30536448356454993066238093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40715264475273324088317457 30536448356454993066238093)
                ·
                  refine ⟨11451168133670622399839285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30536448356454993066238093 11451168133670622399839285)
                  ·
                    refine ⟨1073547012531620849984933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11451168133670622399839285 1073547012531620849984933)
                    ·
                      rfl

theorem cell22_3136088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3136088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136088 prefixEnd_3136088 := by exact prefixLift 3136088
  have htrace : WordTrace (prefixWord ++ tailWord_3136088) baseStart_3136088 baseEnd_3136088 := by
    simpa [prefixWord, tailWord_3136088, baseEnd_3136088] using wordTrace_append hprefix tailTrace_3136088
  have hstable : (prefixWord ++ tailWord_3136088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136088).length < 2 ^ (prefixWord ++ tailWord_3136088).sum := by decide
  have hdescent : baseEnd_3136088 < baseStart_3136088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136156 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3136156 : Nat := 118140960795 + 3136156 * 2 ^ 59
def prefixEnd_3136156 : Nat := 4983230072969 + 3 ^ 40 * 3136156 * 2
def baseEnd_3136156 : Nat := 1073570290321291339284725

theorem tailTrace_3136156 : CollatzResearch.WordTrace tailWord_3136156 prefixEnd_3136156 1073570290321291339284725 := by
  unfold tailWord_3136156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57192503213124949823798161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76256670950833266431730881 57192503213124949823798161)
  ·
    refine ⟨42894377409843712367848621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57192503213124949823798161 42894377409843712367848621)
    ·
      refine ⟨16085391528691392137943233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42894377409843712367848621 16085391528691392137943233)
      ·
        refine ⟨12064043646518544103457425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16085391528691392137943233 12064043646518544103457425)
        ·
          refine ⟨9048032734888908077593069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12064043646518544103457425 9048032734888908077593069)
          ·
            refine ⟨3393012275583340529097401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9048032734888908077593069 3393012275583340529097401)
            ·
              refine ⟨2544759206687505396823051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393012275583340529097401 2544759206687505396823051)
              ·
                refine ⟨3817138810031258095234577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544759206687505396823051 3817138810031258095234577)
                ·
                  refine ⟨2862854107523443571425933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817138810031258095234577 2862854107523443571425933)
                  ·
                    refine ⟨1073570290321291339284725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2862854107523443571425933 1073570290321291339284725)
                    ·
                      rfl

theorem cell22_3136156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3136156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136156 prefixEnd_3136156 := by exact prefixLift 3136156
  have htrace : WordTrace (prefixWord ++ tailWord_3136156) baseStart_3136156 baseEnd_3136156 := by
    simpa [prefixWord, tailWord_3136156, baseEnd_3136156] using wordTrace_append hprefix tailTrace_3136156
  have hstable : (prefixWord ++ tailWord_3136156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136156).length < 2 ^ (prefixWord ++ tailWord_3136156).sum := by decide
  have hdescent : baseEnd_3136156 < baseStart_3136156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136163 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 9]
def baseStart_3136163 : Nat := 118140960795 + 3136163 * 2 ^ 59
def prefixEnd_3136163 : Nat := 4983230072969 + 3 ^ 40 * 3136163 * 2
def baseEnd_3136163 : Nat := 357857562188115218119901

theorem tailTrace_3136163 : CollatzResearch.WordTrace tailWord_3136163 prefixEnd_3136163 357857562188115218119901 := by
  unfold tailWord_3136163
  simp only [CollatzResearch.WordTrace]
  refine ⟨114385261737224539843101143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76256841158149693228734095 114385261737224539843101143)
  ·
    refine ⟨171577892605836809764651715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114385261737224539843101143 171577892605836809764651715)
    ·
      refine ⟨257366838908755214646977573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171577892605836809764651715 257366838908755214646977573)
      ·
        refine ⟨48256282295391602746308295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257366838908755214646977573 48256282295391602746308295)
        ·
          refine ⟨72384423443087404119462443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48256282295391602746308295 72384423443087404119462443)
          ·
            refine ⟨108576635164631106179193665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72384423443087404119462443 108576635164631106179193665)
            ·
              refine ⟨81432476373473329634395249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108576635164631106179193665 81432476373473329634395249)
              ·
                refine ⟨61074357280104997225796437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81432476373473329634395249 61074357280104997225796437)
                ·
                  refine ⟨357857562188115218119901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61074357280104997225796437 357857562188115218119901)
                  ·
                    rfl

theorem cell22_3136163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_3136163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136163 prefixEnd_3136163 := by exact prefixLift 3136163
  have htrace : WordTrace (prefixWord ++ tailWord_3136163) baseStart_3136163 baseEnd_3136163 := by
    simpa [prefixWord, tailWord_3136163, baseEnd_3136163] using wordTrace_append hprefix tailTrace_3136163
  have hstable : (prefixWord ++ tailWord_3136163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136163).length < 2 ^ (prefixWord ++ tailWord_3136163).sum := by decide
  have hdescent : baseEnd_3136163 < baseStart_3136163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136225 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 8]
def baseStart_3136225 : Nat := 118140960795 + 3136225 * 2 ^ 59
def prefixEnd_3136225 : Nat := 4983230072969 + 3 ^ 40 * 3136225 * 2
def baseEnd_3136225 : Nat := 357864636810466053103171

theorem tailTrace_3136225 : CollatzResearch.WordTrace tailWord_3136225 prefixEnd_3136225 357864636810466053103171 := by
  unfold tailWord_3136225
  simp only [CollatzResearch.WordTrace]
  refine ⟨114387523062999924431858129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76258348708666616287905419 114387523062999924431858129)
  ·
    refine ⟨85790642297249943323893597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114387523062999924431858129 85790642297249943323893597)
    ·
      refine ⟨32171490861468728746460099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85790642297249943323893597 32171490861468728746460099)
      ·
        refine ⟨48257236292203093119690149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171490861468728746460099 48257236292203093119690149)
        ·
          refine ⟨9048231804788079959941903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48257236292203093119690149 9048231804788079959941903)
          ·
            refine ⟨13572347707182119939912855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048231804788079959941903 13572347707182119939912855)
            ·
              refine ⟨20358521560773179909869283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13572347707182119939912855 20358521560773179909869283)
              ·
                refine ⟨30537782341159769864803925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20358521560773179909869283 30537782341159769864803925)
                ·
                  refine ⟨357864636810466053103171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30537782341159769864803925 357864636810466053103171)
                  ·
                    rfl

theorem cell22_3136225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_3136225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136225 prefixEnd_3136225 := by exact prefixLift 3136225
  have htrace : WordTrace (prefixWord ++ tailWord_3136225) baseStart_3136225 baseEnd_3136225 := by
    simpa [prefixWord, tailWord_3136225, baseEnd_3136225] using wordTrace_append hprefix tailTrace_3136225
  have hstable : (prefixWord ++ tailWord_3136225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136225).length < 2 ^ (prefixWord ++ tailWord_3136225).sum := by decide
  have hdescent : baseEnd_3136225 < baseStart_3136225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136227 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_3136227 : Nat := 118140960795 + 3136227 * 2 ^ 59
def prefixEnd_3136227 : Nat := 4983230072969 + 3 ^ 40 * 3136227 * 2
def baseEnd_3136227 : Nat := 1073594595072270820759507

theorem tailTrace_3136227 : CollatzResearch.WordTrace tailWord_3136227 prefixEnd_3136227 1073594595072270820759507 := by
  unfold tailWord_3136227
  simp only [CollatzResearch.WordTrace]
  refine ⟨114387596008992678773430935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76258397339328452515620623 114387596008992678773430935)
  ·
    refine ⟨171581394013489018160146403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114387596008992678773430935 171581394013489018160146403)
    ·
      refine ⟨257372091020233527240219605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171581394013489018160146403 257372091020233527240219605)
      ·
        refine ⟨6032158383286723294692647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 257372091020233527240219605 6032158383286723294692647)
        ·
          refine ⟨9048237574930084942038971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032158383286723294692647 9048237574930084942038971)
          ·
            refine ⟨13572356362395127413058457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048237574930084942038971 13572356362395127413058457)
            ·
              refine ⟨10179267271796345559793843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572356362395127413058457 10179267271796345559793843)
              ·
                refine ⟨15268900907694518339690765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179267271796345559793843 15268900907694518339690765)
                ·
                  refine ⟨5725837840385444377384037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15268900907694518339690765 5725837840385444377384037)
                  ·
                    refine ⟨1073594595072270820759507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725837840385444377384037 1073594595072270820759507)
                    ·
                      rfl

theorem cell22_3136227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_3136227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136227 prefixEnd_3136227 := by exact prefixLift 3136227
  have htrace : WordTrace (prefixWord ++ tailWord_3136227) baseStart_3136227 baseEnd_3136227 := by
    simpa [prefixWord, tailWord_3136227, baseEnd_3136227] using wordTrace_append hprefix tailTrace_3136227
  have hstable : (prefixWord ++ tailWord_3136227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136227).length < 2 ^ (prefixWord ++ tailWord_3136227).sum := by decide
  have hdescent : baseEnd_3136227 < baseStart_3136227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136240 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_3136240 : Nat := 118140960795 + 3136240 * 2 ^ 59
def prefixEnd_3136240 : Nat := 4983230072969 + 3 ^ 40 * 3136240 * 2
def baseEnd_3136240 : Nat := 1073599045237943120184467

theorem tailTrace_3136240 : CollatzResearch.WordTrace tailWord_3136240 prefixEnd_3136240 1073599045237943120184467 := by
  unfold tailWord_3136240
  simp only [CollatzResearch.WordTrace]
  refine ⟨57194035078972790996827087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76258713438630387995769449 57194035078972790996827087)
  ·
    refine ⟨85791052618459186495240631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57194035078972790996827087 85791052618459186495240631)
    ·
      refine ⟨128686578927688779742860947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85791052618459186495240631 128686578927688779742860947)
      ·
        refine ⟨193029868391533169614291421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128686578927688779742860947 193029868391533169614291421)
        ·
          refine ⟨72386200646824938605359283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193029868391533169614291421 72386200646824938605359283)
          ·
            refine ⟨108579300970237407908038925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72386200646824938605359283 108579300970237407908038925)
            ·
              refine ⟨40717237863839027965514597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108579300970237407908038925 40717237863839027965514597)
              ·
                refine ⟨7634482099469817743533987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40717237863839027965514597 7634482099469817743533987)
                ·
                  refine ⟨11451723149204726615300981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634482099469817743533987 11451723149204726615300981)
                  ·
                    refine ⟨1073599045237943120184467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11451723149204726615300981 1073599045237943120184467)
                    ·
                      rfl

theorem cell22_3136240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_3136240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136240 prefixEnd_3136240 := by exact prefixLift 3136240
  have htrace : WordTrace (prefixWord ++ tailWord_3136240) baseStart_3136240 baseEnd_3136240 := by
    simpa [prefixWord, tailWord_3136240, baseEnd_3136240] using wordTrace_append hprefix tailTrace_3136240
  have hstable : (prefixWord ++ tailWord_3136240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136240).length < 2 ^ (prefixWord ++ tailWord_3136240).sum := by decide
  have hdescent : baseEnd_3136240 < baseStart_3136240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136255 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3136255 : Nat := 118140960795 + 3136255 * 2 ^ 59
def prefixEnd_3136255 : Nat := 4983230072969 + 3 ^ 40 * 3136255 * 2
def baseEnd_3136255 : Nat := 1073604180044488081059421

theorem tailTrace_3136255 : CollatzResearch.WordTrace tailWord_3136255 prefixEnd_3136255 1073604180044488081059421 := by
  unfold tailWord_3136255
  simp only [CollatzResearch.WordTrace]
  refine ⟨114388617252891239555450219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76259078168594159703633479 114388617252891239555450219)
  ·
    refine ⟨171582925879336859333175329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114388617252891239555450219 171582925879336859333175329)
    ·
      refine ⟨128687194409502644499881497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171582925879336859333175329 128687194409502644499881497)
      ·
        refine ⟨96515395807126983374911123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128687194409502644499881497 96515395807126983374911123)
        ·
          refine ⟨144773093710690475062366685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96515395807126983374911123 144773093710690475062366685)
          ·
            refine ⟨54289910141508928148387507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144773093710690475062366685 54289910141508928148387507)
            ·
              refine ⟨81434865212263392222581261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54289910141508928148387507 81434865212263392222581261)
              ·
                refine ⟨30538074454598772083467973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81434865212263392222581261 30538074454598772083467973)
                ·
                  refine ⟨5725888960237269765650245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30538074454598772083467973 5725888960237269765650245)
                  ·
                    refine ⟨1073604180044488081059421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725888960237269765650245 1073604180044488081059421)
                    ·
                      rfl

theorem cell22_3136255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3136255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136255 prefixEnd_3136255 := by exact prefixLift 3136255
  have htrace : WordTrace (prefixWord ++ tailWord_3136255) baseStart_3136255 baseEnd_3136255 := by
    simpa [prefixWord, tailWord_3136255, baseEnd_3136255] using wordTrace_append hprefix tailTrace_3136255
  have hstable : (prefixWord ++ tailWord_3136255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136255).length < 2 ^ (prefixWord ++ tailWord_3136255).sum := by decide
  have hdescent : baseEnd_3136255 < baseStart_3136255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136270 : List Nat := [4, 1, 1, 2, 1, 1, 1, 11]
def baseStart_3136270 : Nat := 118140960795 + 3136270 * 2 ^ 59
def prefixEnd_3136270 : Nat := 4983230072969 + 3 ^ 40 * 3136270 * 2
def baseEnd_3136270 : Nat := 119289923872337004659375

theorem tailTrace_3136270 : CollatzResearch.WordTrace tailWord_3136270 prefixEnd_3136270 119289923872337004659375 := by
  unfold tailWord_3136270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14298645543479612139655783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76259442898557931411497509 14298645543479612139655783)
  ·
    refine ⟨21447968315219418209483675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14298645543479612139655783 21447968315219418209483675)
    ·
      refine ⟨32171952472829127314225513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21447968315219418209483675 32171952472829127314225513)
      ·
        refine ⟨24128964354621845485669135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32171952472829127314225513 24128964354621845485669135)
        ·
          refine ⟨36193446531932768228503703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24128964354621845485669135 36193446531932768228503703)
          ·
            refine ⟨54290169797899152342755555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36193446531932768228503703 54290169797899152342755555)
            ·
              refine ⟨81435254696848728514133333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54290169797899152342755555 81435254696848728514133333)
              ·
                refine ⟨119289923872337004659375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81435254696848728514133333 119289923872337004659375)
                ·
                  rfl

theorem cell22_3136270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_3136270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136270 prefixEnd_3136270 := by exact prefixLift 3136270
  have htrace : WordTrace (prefixWord ++ tailWord_3136270) baseStart_3136270 baseEnd_3136270 := by
    simpa [prefixWord, tailWord_3136270, baseEnd_3136270] using wordTrace_append hprefix tailTrace_3136270
  have hstable : (prefixWord ++ tailWord_3136270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136270).length < 2 ^ (prefixWord ++ tailWord_3136270).sum := by decide
  have hdescent : baseEnd_3136270 < baseStart_3136270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136287 : List Nat := [1, 1, 2, 4, 2, 2, 4, 6]
def baseStart_3136287 : Nat := 118140960795 + 3136287 * 2 ^ 59
def prefixEnd_3136287 : Nat := 4983230072969 + 3 ^ 40 * 3136287 * 2
def baseEnd_3136287 : Nat := 119290570477605629362147

theorem tailTrace_3136287 : CollatzResearch.WordTrace tailWord_3136287 prefixEnd_3136287 119290570477605629362147 := by
  unfold tailWord_3136287
  simp only [CollatzResearch.WordTrace]
  refine ⟨114389784388775309020615115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76259856259183539347076743 114389784388775309020615115)
  ·
    refine ⟨171584676583162963530922673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114389784388775309020615115 171584676583162963530922673)
    ·
      refine ⟨128688507437372222648192005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171584676583162963530922673 128688507437372222648192005)
      ·
        refine ⟨24129095144507291746536001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128688507437372222648192005 24129095144507291746536001)
        ·
          refine ⟨18096821358380468809902001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24129095144507291746536001 18096821358380468809902001)
          ·
            refine ⟨13572616018785351607426501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18096821358380468809902001 13572616018785351607426501)
            ·
              refine ⟨2544865503522253426392469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13572616018785351607426501 2544865503522253426392469)
              ·
                refine ⟨119290570477605629362147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2544865503522253426392469 119290570477605629362147)
                ·
                  rfl

theorem cell22_3136287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 6].length) (baseStart_3136287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136287 prefixEnd_3136287 := by exact prefixLift 3136287
  have htrace : WordTrace (prefixWord ++ tailWord_3136287) baseStart_3136287 baseEnd_3136287 := by
    simpa [prefixWord, tailWord_3136287, baseEnd_3136287] using wordTrace_append hprefix tailTrace_3136287
  have hstable : (prefixWord ++ tailWord_3136287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136287).length < 2 ^ (prefixWord ++ tailWord_3136287).sum := by decide
  have hdescent : baseEnd_3136287 < baseStart_3136287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136319 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 3, 3]
def baseStart_3136319 : Nat := 118140960795 + 3136319 * 2 ^ 59
def prefixEnd_3136319 : Nat := 4983230072969 + 3 ^ 40 * 3136319 * 2
def baseEnd_3136319 : Nat := 1073626088552413247459225

theorem tailTrace_3136319 : CollatzResearch.WordTrace tailWord_3136319 prefixEnd_3136319 1073626088552413247459225 := by
  unfold tailWord_3136319
  simp only [CollatzResearch.WordTrace]
  refine ⟨114390951524659378485780011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76260634349772918990520007 114390951524659378485780011)
  ·
    refine ⟨171586427286989067728670017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114390951524659378485780011 171586427286989067728670017)
    ·
      refine ⟨128689820465241800796502513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171586427286989067728670017 128689820465241800796502513)
      ·
        refine ⟨96517365348931350597376885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128689820465241800796502513 96517365348931350597376885)
        ·
          refine ⟨9048503001462314118504083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96517365348931350597376885 9048503001462314118504083)
          ·
            refine ⟨13572754502193471177756125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048503001462314118504083 13572754502193471177756125)
            ·
              refine ⟨5089782938322551691658547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13572754502193471177756125 5089782938322551691658547)
              ·
                refine ⟨7634674407483827537487821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089782938322551691658547 7634674407483827537487821)
                ·
                  refine ⟨2863002902806435326557933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7634674407483827537487821 2863002902806435326557933)
                  ·
                    refine ⟨1073626088552413247459225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863002902806435326557933 1073626088552413247459225)
                    ·
                      rfl

theorem cell22_3136319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_3136319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136319 prefixEnd_3136319 := by exact prefixLift 3136319
  have htrace : WordTrace (prefixWord ++ tailWord_3136319) baseStart_3136319 baseEnd_3136319 := by
    simpa [prefixWord, tailWord_3136319, baseEnd_3136319] using wordTrace_append hprefix tailTrace_3136319
  have hstable : (prefixWord ++ tailWord_3136319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136319).length < 2 ^ (prefixWord ++ tailWord_3136319).sum := by decide
  have hdescent : baseEnd_3136319 < baseStart_3136319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136366 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3136366 : Nat := 118140960795 + 3136366 * 2 ^ 59
def prefixEnd_3136366 : Nat := 4983230072969 + 3 ^ 40 * 3136366 * 2
def baseEnd_3136366 : Nat := 357880725870973597178027

theorem tailTrace_3136366 : CollatzResearch.WordTrace tailWord_3136366 prefixEnd_3136366 357880725870973597178027 := by
  unfold tailWord_3136366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299083219436138189092619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76261777170326070341827301 14299083219436138189092619)
  ·
    refine ⟨21448624829154207283638929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14299083219436138189092619 21448624829154207283638929)
    ·
      refine ⟨16086468621865655462729197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21448624829154207283638929 16086468621865655462729197)
      ·
        refine ⟨6032425733199620798523449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16086468621865655462729197 6032425733199620798523449)
        ·
          refine ⟨4524319299899715598892587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6032425733199620798523449 4524319299899715598892587)
          ·
            refine ⟨6786478949849573398338881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524319299899715598892587 6786478949849573398338881)
            ·
              refine ⟨5089859212387180048754161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786478949849573398338881 5089859212387180048754161)
              ·
                refine ⟨3817394409290385036565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5089859212387180048754161 3817394409290385036565621)
                ·
                  refine ⟨357880725870973597178027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3817394409290385036565621 357880725870973597178027)
                  ·
                    rfl

theorem cell22_3136366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3136366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136366 prefixEnd_3136366 := by exact prefixLift 3136366
  have htrace : WordTrace (prefixWord ++ tailWord_3136366) baseStart_3136366 baseEnd_3136366 := by
    simpa [prefixWord, tailWord_3136366, baseEnd_3136366] using wordTrace_append hprefix tailTrace_3136366
  have hstable : (prefixWord ++ tailWord_3136366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136366).length < 2 ^ (prefixWord ++ tailWord_3136366).sum := by decide
  have hdescent : baseEnd_3136366 < baseStart_3136366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136394 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_3136394 : Nat := 118140960795 + 3136394 * 2 ^ 59
def prefixEnd_3136394 : Nat := 4983230072969 + 3 ^ 40 * 3136394 * 2
def baseEnd_3136394 : Nat := 357883920861712683944665

theorem tailTrace_3136394 : CollatzResearch.WordTrace tailWord_3136394 prefixEnd_3136394 357883920861712683944665 := by
  unfold tailWord_3136394
  simp only [CollatzResearch.WordTrace]
  refine ⟨28598421749846916573690059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76262457999591777529840157 28598421749846916573690059)
  ·
    refine ⟨42897632624770374860535089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28598421749846916573690059 42897632624770374860535089)
    ·
      refine ⟨32173224468577781145401317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42897632624770374860535089 32173224468577781145401317)
      ·
        refine ⟨6032479587858333964762747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32173224468577781145401317 6032479587858333964762747)
        ·
          refine ⟨9048719381787500947144121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032479587858333964762747 9048719381787500947144121)
          ·
            refine ⟨6786539536340625710358091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048719381787500947144121 6786539536340625710358091)
            ·
              refine ⟨10179809304510938565537137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786539536340625710358091 10179809304510938565537137)
              ·
                refine ⟨7634856978383203924152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10179809304510938565537137 7634856978383203924152853)
                ·
                  refine ⟨357883920861712683944665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7634856978383203924152853 357883920861712683944665)
                  ·
                    rfl

theorem cell22_3136394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_3136394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136394 prefixEnd_3136394 := by exact prefixLift 3136394
  have htrace : WordTrace (prefixWord ++ tailWord_3136394) baseStart_3136394 baseEnd_3136394 := by
    simpa [prefixWord, tailWord_3136394, baseEnd_3136394] using wordTrace_append hprefix tailTrace_3136394
  have hstable : (prefixWord ++ tailWord_3136394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136394).length < 2 ^ (prefixWord ++ tailWord_3136394).sum := by decide
  have hdescent : baseEnd_3136394 < baseStart_3136394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136407 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3136407 : Nat := 118140960795 + 3136407 * 2 ^ 59
def prefixEnd_3136407 : Nat := 4983230072969 + 3 ^ 40 * 3136407 * 2
def baseEnd_3136407 : Nat := 1073656212750810351258955

theorem tailTrace_3136407 : CollatzResearch.WordTrace tailWord_3136407 prefixEnd_3136407 1073656212750810351258955 := by
  unfold tailWord_3136407
  simp only [CollatzResearch.WordTrace]
  refine ⟨114394161148340569514983475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76262774098893713009988983 114394161148340569514983475)
  ·
    refine ⟨171591241722510854272475213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114394161148340569514983475 171591241722510854272475213)
    ·
      refine ⟨64346715645941570352178205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171591241722510854272475213 64346715645941570352178205)
      ·
        refine ⟨24130018367228088882066827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64346715645941570352178205 24130018367228088882066827)
        ·
          refine ⟨36195027550842133323100241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24130018367228088882066827 36195027550842133323100241)
          ·
            refine ⟨27146270663131599992325181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36195027550842133323100241 27146270663131599992325181)
            ·
              refine ⟨10179851498674349997121943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27146270663131599992325181 10179851498674349997121943)
              ·
                refine ⟨15269777248011524995682915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179851498674349997121943 15269777248011524995682915)
                ·
                  refine ⟨22904665872017287493524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15269777248011524995682915 22904665872017287493524373)
                  ·
                    refine ⟨1073656212750810351258955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22904665872017287493524373 1073656212750810351258955)
                    ·
                      rfl

theorem cell22_3136407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3136407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136407 prefixEnd_3136407 := by exact prefixLift 3136407
  have htrace : WordTrace (prefixWord ++ tailWord_3136407) baseStart_3136407 baseEnd_3136407 := by
    simpa [prefixWord, tailWord_3136407, baseEnd_3136407] using wordTrace_append hprefix tailTrace_3136407
  have hstable : (prefixWord ++ tailWord_3136407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136407).length < 2 ^ (prefixWord ++ tailWord_3136407).sum := by decide
  have hdescent : baseEnd_3136407 < baseStart_3136407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136456 : List Nat := [2, 1, 3, 1, 5, 2, 2, 6]
def baseStart_3136456 : Nat := 118140960795 + 3136456 * 2 ^ 59
def prefixEnd_3136456 : Nat := 4983230072969 + 3 ^ 40 * 3136456 * 2
def baseEnd_3136456 : Nat := 119296998494687839642645

theorem tailTrace_3136456 : CollatzResearch.WordTrace tailWord_3136456 prefixEnd_3136456 119296998494687839642645 := by
  unfold tailWord_3136456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57197974162581525441758611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76263965550108700589011481 57197974162581525441758611)
  ·
    refine ⟨85796961243872288162637917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57197974162581525441758611 85796961243872288162637917)
    ·
      refine ⟨32173860466452108060989219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85796961243872288162637917 32173860466452108060989219)
      ·
        refine ⟨48260790699678162091483829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32173860466452108060989219 48260790699678162091483829)
        ·
          refine ⟨4524449128094827696076609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48260790699678162091483829 4524449128094827696076609)
          ·
            refine ⟨3393336846071120772057457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524449128094827696076609 3393336846071120772057457)
            ·
              refine ⟨2545002634553340579043093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393336846071120772057457 2545002634553340579043093)
              ·
                refine ⟨119296998494687839642645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2545002634553340579043093 119296998494687839642645)
                ·
                  rfl

theorem cell22_3136456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_3136456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136456 prefixEnd_3136456 := by exact prefixLift 3136456
  have htrace : WordTrace (prefixWord ++ tailWord_3136456) baseStart_3136456 baseEnd_3136456 := by
    simpa [prefixWord, tailWord_3136456, baseEnd_3136456] using wordTrace_append hprefix tailTrace_3136456
  have hstable : (prefixWord ++ tailWord_3136456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136456).length < 2 ^ (prefixWord ++ tailWord_3136456).sum := by decide
  have hdescent : baseEnd_3136456 < baseStart_3136456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136471 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 1, 3]
def baseStart_3136471 : Nat := 118140960795 + 3136471 * 2 ^ 59
def prefixEnd_3136471 : Nat := 4983230072969 + 3 ^ 40 * 3136471 * 2
def baseEnd_3136471 : Nat := 1073678121258735517658759

theorem tailTrace_3136471 : CollatzResearch.WordTrace tailWord_3136471 prefixEnd_3136471 1073678121258735517658759 := by
  unfold tailWord_3136471
  simp only [CollatzResearch.WordTrace]
  refine ⟨114396495420108708445313267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76264330280072472296875511 114396495420108708445313267)
  ·
    refine ⟨171594743130163062667969901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114396495420108708445313267 171594743130163062667969901)
    ·
      refine ⟨64348028673811148500488713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171594743130163062667969901 64348028673811148500488713)
      ·
        refine ⟨48261021505358361375366535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64348028673811148500488713 48261021505358361375366535)
        ·
          refine ⟨72391532258037542063049803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48261021505358361375366535 72391532258037542063049803)
          ·
            refine ⟨108587298387056313094574705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72391532258037542063049803 108587298387056313094574705)
            ·
              refine ⟨81440473790292234820931029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108587298387056313094574705 81440473790292234820931029)
              ·
                refine ⟨1908761104459974253615571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81440473790292234820931029 1908761104459974253615571)
                ·
                  refine ⟨2863141656689961380423357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908761104459974253615571 2863141656689961380423357)
                  ·
                    refine ⟨1073678121258735517658759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863141656689961380423357 1073678121258735517658759)
                    ·
                      rfl

theorem cell22_3136471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_3136471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136471 prefixEnd_3136471 := by exact prefixLift 3136471
  have htrace : WordTrace (prefixWord ++ tailWord_3136471) baseStart_3136471 baseEnd_3136471 := by
    simpa [prefixWord, tailWord_3136471, baseEnd_3136471] using wordTrace_append hprefix tailTrace_3136471
  have hstable : (prefixWord ++ tailWord_3136471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136471).length < 2 ^ (prefixWord ++ tailWord_3136471).sum := by decide
  have hdescent : baseEnd_3136471 < baseStart_3136471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136561 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_3136561 : Nat := 118140960795 + 3136561 * 2 ^ 59
def prefixEnd_3136561 : Nat := 4983230072969 + 3 ^ 40 * 3136561 * 2
def baseEnd_3136561 : Nat := 1073708930098005282908483

theorem tailTrace_3136561 : CollatzResearch.WordTrace tailWord_3136561 prefixEnd_3136561 1073708930098005282908483 := by
  unfold tailWord_3136561
  simp only [CollatzResearch.WordTrace]
  refine ⟨114399777989782653816089537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76266518659855102544059691 114399777989782653816089537)
  ·
    refine ⟨85799833492336990362067153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114399777989782653816089537 85799833492336990362067153)
    ·
      refine ⟨64349875119252742771550365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85799833492336990362067153 64349875119252742771550365)
      ·
        refine ⟨24131203169719778539331387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64349875119252742771550365 24131203169719778539331387)
        ·
          refine ⟨36196804754579667808997081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24131203169719778539331387 36196804754579667808997081)
          ·
            refine ⟨27147603565934750856747811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36196804754579667808997081 27147603565934750856747811)
            ·
              refine ⟨40721405348902126285121717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27147603565934750856747811 40721405348902126285121717)
              ·
                refine ⟨3817631751459574339230161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40721405348902126285121717 3817631751459574339230161)
                ·
                  refine ⟨2863223813594680754422621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817631751459574339230161 2863223813594680754422621)
                  ·
                    refine ⟨1073708930098005282908483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863223813594680754422621 1073708930098005282908483)
                    ·
                      rfl

theorem cell22_3136561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_3136561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136561 prefixEnd_3136561 := by exact prefixLift 3136561
  have htrace : WordTrace (prefixWord ++ tailWord_3136561) baseStart_3136561 baseEnd_3136561 := by
    simpa [prefixWord, tailWord_3136561, baseEnd_3136561] using wordTrace_append hprefix tailTrace_3136561
  have hstable : (prefixWord ++ tailWord_3136561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136561).length < 2 ^ (prefixWord ++ tailWord_3136561).sum := by decide
  have hdescent : baseEnd_3136561 < baseStart_3136561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136582 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3136582 : Nat := 118140960795 + 3136582 * 2 ^ 59
def prefixEnd_3136582 : Nat := 4983230072969 + 3 ^ 40 * 3136582 * 2
def baseEnd_3136582 : Nat := 1073716118827168228133419

theorem tailTrace_3136582 : CollatzResearch.WordTrace tailWord_3136582 prefixEnd_3136582 1073716118827168228133419 := by
  unfold tailWord_3136582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575016997584580450081375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76267029281804382935069333 3575016997584580450081375)
  ·
    refine ⟨5362525496376870675122063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575016997584580450081375 5362525496376870675122063)
    ·
      refine ⟨8043788244565306012683095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362525496376870675122063 8043788244565306012683095)
      ·
        refine ⟨12065682366847959019024643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043788244565306012683095 12065682366847959019024643)
        ·
          refine ⟨18098523550271938528536965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065682366847959019024643 18098523550271938528536965)
          ·
            refine ⟨3393473165675988474100681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18098523550271938528536965 3393473165675988474100681)
            ·
              refine ⟨2545104874256991355575511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393473165675988474100681 2545104874256991355575511)
              ·
                refine ⟨3817657311385487033363267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545104874256991355575511 3817657311385487033363267)
                ·
                  refine ⟨5726485967078230550044901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817657311385487033363267 5726485967078230550044901)
                  ·
                    refine ⟨1073716118827168228133419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726485967078230550044901 1073716118827168228133419)
                    ·
                      rfl

theorem cell22_3136582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3136582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136582 prefixEnd_3136582 := by exact prefixLift 3136582
  have htrace : WordTrace (prefixWord ++ tailWord_3136582) baseStart_3136582 baseEnd_3136582 := by
    simpa [prefixWord, tailWord_3136582, baseEnd_3136582] using wordTrace_append hprefix tailTrace_3136582
  have hstable : (prefixWord ++ tailWord_3136582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136582).length < 2 ^ (prefixWord ++ tailWord_3136582).sum := by decide
  have hdescent : baseEnd_3136582 < baseStart_3136582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136670 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3136670 : Nat := 118140960795 + 3136670 * 2 ^ 59
def prefixEnd_3136670 : Nat := 4983230072969 + 3 ^ 40 * 3136670 * 2
def baseEnd_3136670 : Nat := 357915414341855110644383

theorem tailTrace_3136670 : CollatzResearch.WordTrace tailWord_3136670 prefixEnd_3136670 357915414341855110644383 := by
  unfold tailWord_3136670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300469193298470678975933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76269169030925176954538309 14300469193298470678975933)
  ·
    refine ⟨5362675947486926504615975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14300469193298470678975933 5362675947486926504615975)
    ·
      refine ⟨8044013921230389756923963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362675947486926504615975 8044013921230389756923963)
      ·
        refine ⟨12066020881845584635385945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8044013921230389756923963 12066020881845584635385945)
        ·
          refine ⟨9049515661384188476539459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12066020881845584635385945 9049515661384188476539459)
          ·
            refine ⟨13574273492076282714809189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049515661384188476539459 13574273492076282714809189)
            ·
              refine ⟨2545176279764303009026723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13574273492076282714809189 2545176279764303009026723)
              ·
                refine ⟨3817764419646454513540085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545176279764303009026723 3817764419646454513540085)
                ·
                  refine ⟨357915414341855110644383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3817764419646454513540085 357915414341855110644383)
                  ·
                    rfl

theorem cell22_3136670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3136670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136670 prefixEnd_3136670 := by exact prefixLift 3136670
  have htrace : WordTrace (prefixWord ++ tailWord_3136670) baseStart_3136670 baseEnd_3136670 := by
    simpa [prefixWord, tailWord_3136670, baseEnd_3136670] using wordTrace_append hprefix tailTrace_3136670
  have hstable : (prefixWord ++ tailWord_3136670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136670).length < 2 ^ (prefixWord ++ tailWord_3136670).sum := by decide
  have hdescent : baseEnd_3136670 < baseStart_3136670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136696 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_3136696 : Nat := 118140960795 + 3136696 * 2 ^ 59
def prefixEnd_3136696 : Nat := 4983230072969 + 3 ^ 40 * 3136696 * 2
def baseEnd_3136696 : Nat := 1073755143356909930783069

theorem tailTrace_3136696 : CollatzResearch.WordTrace tailWord_3136696 prefixEnd_3136696 1073755143356909930783069 := by
  unfold tailWord_3136696
  simp only [CollatzResearch.WordTrace]
  refine ⟨57202350922146785936126971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76269801229529047914835961 57202350922146785936126971)
  ·
    refine ⟨85803526383220178904190457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57202350922146785936126971 85803526383220178904190457)
    ·
      refine ⟨64352644787415134178142843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85803526383220178904190457 64352644787415134178142843)
      ·
        refine ⟨96528967181122701267214265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64352644787415134178142843 96528967181122701267214265)
        ·
          refine ⟨72396725385842025950410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96528967181122701267214265 72396725385842025950410699)
          ·
            refine ⟨108595088078763038925616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72396725385842025950410699 108595088078763038925616049)
            ·
              refine ⟨81446316059072279194212037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108595088078763038925616049 81446316059072279194212037)
              ·
                refine ⟨15271184261076052348914757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81446316059072279194212037 15271184261076052348914757)
                ·
                  refine ⟨2863347048951759815421517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15271184261076052348914757 2863347048951759815421517)
                  ·
                    refine ⟨1073755143356909930783069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863347048951759815421517 1073755143356909930783069)
                    ·
                      rfl

theorem cell22_3136696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_3136696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136696 prefixEnd_3136696 := by exact prefixLift 3136696
  have htrace : WordTrace (prefixWord ++ tailWord_3136696) baseStart_3136696 baseEnd_3136696 := by
    simpa [prefixWord, tailWord_3136696, baseEnd_3136696] using wordTrace_append hprefix tailTrace_3136696
  have hstable : (prefixWord ++ tailWord_3136696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136696).length < 2 ^ (prefixWord ++ tailWord_3136696).sum := by decide
  have hdescent : baseEnd_3136696 < baseStart_3136696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136700 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3136700 : Nat := 118140960795 + 3136700 * 2 ^ 59
def prefixEnd_3136700 : Nat := 4983230072969 + 3 ^ 40 * 3136700 * 2
def baseEnd_3136700 : Nat := 1073756512638655253683057

theorem tailTrace_3136700 : CollatzResearch.WordTrace tailWord_3136700 prefixEnd_3136700 1073756512638655253683057 := by
  unfold tailWord_3136700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57202423868139540277699777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76269898490852720370266369 57202423868139540277699777)
  ·
    refine ⟨42901817901104655208274833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57202423868139540277699777 42901817901104655208274833)
    ·
      refine ⟨32176363425828491406206125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42901817901104655208274833 32176363425828491406206125)
      ·
        refine ⟨12066136284685684277327297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32176363425828491406206125 12066136284685684277327297)
        ·
          refine ⟨9049602213514263207995473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12066136284685684277327297 9049602213514263207995473)
          ·
            refine ⟨6787201660135697405996605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9049602213514263207995473 6787201660135697405996605)
            ·
              refine ⟨2545200622550886527248727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6787201660135697405996605 2545200622550886527248727)
              ·
                refine ⟨3817800933826329790873091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545200622550886527248727 3817800933826329790873091)
                ·
                  refine ⟨5726701400739494686309637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817800933826329790873091 5726701400739494686309637)
                  ·
                    refine ⟨1073756512638655253683057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726701400739494686309637 1073756512638655253683057)
                    ·
                      rfl

theorem cell22_3136700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3136700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136700 prefixEnd_3136700 := by exact prefixLift 3136700
  have htrace : WordTrace (prefixWord ++ tailWord_3136700) baseStart_3136700 baseEnd_3136700 := by
    simpa [prefixWord, tailWord_3136700, baseEnd_3136700] using wordTrace_append hprefix tailTrace_3136700
  have hstable : (prefixWord ++ tailWord_3136700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136700).length < 2 ^ (prefixWord ++ tailWord_3136700).sum := by decide
  have hdescent : baseEnd_3136700 < baseStart_3136700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136758 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3136758 : Nat := 118140960795 + 3136758 * 2 ^ 59
def prefixEnd_3136758 : Nat := 4983230072969 + 3 ^ 40 * 3136758 * 2
def baseEnd_3136758 : Nat := 1073776367223962435732879

theorem tailTrace_3136758 : CollatzResearch.WordTrace tailWord_3136758 prefixEnd_3136758 1073776367223962435732879 := by
  unfold tailWord_3136758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7150435198129309778813183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76271308780045970974007285 7150435198129309778813183)
  ·
    refine ⟨10725652797193964668219775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7150435198129309778813183 10725652797193964668219775)
    ·
      refine ⟨16088479195790947002329663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725652797193964668219775 16088479195790947002329663)
      ·
        refine ⟨24132718793686420503494495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16088479195790947002329663 24132718793686420503494495)
        ·
          refine ⟨36199078190529630755241743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24132718793686420503494495 36199078190529630755241743)
          ·
            refine ⟨54298617285794446132862615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36199078190529630755241743 54298617285794446132862615)
            ·
              refine ⟨81447925928691669199293923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54298617285794446132862615 81447925928691669199293923)
              ·
                refine ⟨122171888893037503798940885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81447925928691669199293923 122171888893037503798940885)
                ·
                  refine ⟨2863403645930566495287677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122171888893037503798940885 2863403645930566495287677)
                  ·
                    refine ⟨1073776367223962435732879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863403645930566495287677 1073776367223962435732879)
                    ·
                      rfl

theorem cell22_3136758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3136758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136758 prefixEnd_3136758 := by exact prefixLift 3136758
  have htrace : WordTrace (prefixWord ++ tailWord_3136758) baseStart_3136758 baseEnd_3136758 := by
    simpa [prefixWord, tailWord_3136758, baseEnd_3136758] using wordTrace_append hprefix tailTrace_3136758
  have hstable : (prefixWord ++ tailWord_3136758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136758).length < 2 ^ (prefixWord ++ tailWord_3136758).sum := by decide
  have hdescent : baseEnd_3136758 < baseStart_3136758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136771 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 7]
def baseStart_3136771 : Nat := 118140960795 + 3136771 * 2 ^ 59
def prefixEnd_3136771 : Nat := 4983230072969 + 3 ^ 40 * 3136771 * 2
def baseEnd_3136771 : Nat := 357926939129878245052613

theorem tailTrace_3136771 : CollatzResearch.WordTrace tailWord_3136771 prefixEnd_3136771 357926939129878245052613 := by
  unfold tailWord_3136771
  simp only [CollatzResearch.WordTrace]
  refine ⟨114407437319021859681234167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76271624879347906454156111 114407437319021859681234167)
  ·
    refine ⟨171611155978532789521851251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114407437319021859681234167 171611155978532789521851251)
    ·
      refine ⟨257416733967799184282776877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171611155978532789521851251 257416733967799184282776877)
      ·
        refine ⟨96531275237924694106041329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257416733967799184282776877 96531275237924694106041329)
        ·
          refine ⟨72398456428443520579530997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96531275237924694106041329 72398456428443520579530997)
          ·
            refine ⟨6787355290166580054331031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72398456428443520579530997 6787355290166580054331031)
            ·
              refine ⟨10181032935249870081496547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787355290166580054331031 10181032935249870081496547)
              ·
                refine ⟨15271549402874805122244821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10181032935249870081496547 15271549402874805122244821)
                ·
                  refine ⟨357926939129878245052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15271549402874805122244821 357926939129878245052613)
                  ·
                    rfl

theorem cell22_3136771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_3136771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136771 prefixEnd_3136771 := by exact prefixLift 3136771
  have htrace : WordTrace (prefixWord ++ tailWord_3136771) baseStart_3136771 baseEnd_3136771 := by
    simpa [prefixWord, tailWord_3136771, baseEnd_3136771] using wordTrace_append hprefix tailTrace_3136771
  have hstable : (prefixWord ++ tailWord_3136771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136771).length < 2 ^ (prefixWord ++ tailWord_3136771).sum := by decide
  have hdescent : baseEnd_3136771 < baseStart_3136771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136878 : List Nat := [4, 1, 2, 4, 11]
def baseStart_3136878 : Nat := 118140960795 + 3136878 * 2 ^ 59
def prefixEnd_3136878 : Nat := 4983230072969 + 3 ^ 40 * 3136878 * 2
def baseEnd_3136878 : Nat := 4419001834058938776677

theorem tailTrace_3136878 : CollatzResearch.WordTrace tailWord_3136878 prefixEnd_3136878 4419001834058938776677 := by
  unfold tailWord_3136878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301417491204277119422411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76274226619756144636919525 14301417491204277119422411)
  ·
    refine ⟨21452126236806415679133617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14301417491204277119422411 21452126236806415679133617)
    ·
      refine ⟨16089094677604811759350213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21452126236806415679133617 16089094677604811759350213)
      ·
        refine ⟨3016705252050902204878165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16089094677604811759350213 3016705252050902204878165)
        ·
          refine ⟨4419001834058938776677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3016705252050902204878165 4419001834058938776677)
          ·
            rfl

theorem cell22_3136878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 11].length) (baseStart_3136878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136878 prefixEnd_3136878 := by exact prefixLift 3136878
  have htrace : WordTrace (prefixWord ++ tailWord_3136878) baseStart_3136878 baseEnd_3136878 := by
    simpa [prefixWord, tailWord_3136878, baseEnd_3136878] using wordTrace_append hprefix tailTrace_3136878
  have hstable : (prefixWord ++ tailWord_3136878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136878).length < 2 ^ (prefixWord ++ tailWord_3136878).sum := by decide
  have hdescent : baseEnd_3136878 < baseStart_3136878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136891 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_3136891 : Nat := 118140960795 + 3136891 * 2 ^ 59
def prefixEnd_3136891 : Nat := 4983230072969 + 3 ^ 40 * 3136891 * 2
def baseEnd_3136891 : Nat := 1073821895841994422157471

theorem tailTrace_3136891 : CollatzResearch.WordTrace tailWord_3136891 prefixEnd_3136891 1073821895841994422157471 := by
  unfold tailWord_3136891
  simp only [CollatzResearch.WordTrace]
  refine ⟨114411814078587120175602527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76274542719058080117068351 114411814078587120175602527)
  ·
    refine ⟨171617721117880680263403791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114411814078587120175602527 171617721117880680263403791)
    ·
      refine ⟨257426581676821020395105687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171617721117880680263403791 257426581676821020395105687)
      ·
        refine ⟨386139872515231530592658531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257426581676821020395105687 386139872515231530592658531)
        ·
          refine ⟨579209808772847295888987797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386139872515231530592658531 579209808772847295888987797)
          ·
            refine ⟨27150459786227216994796303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 579209808772847295888987797 27150459786227216994796303)
            ·
              refine ⟨40725689679340825492194455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27150459786227216994796303 40725689679340825492194455)
              ·
                refine ⟨61088534519011238238291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40725689679340825492194455 61088534519011238238291683)
                ·
                  refine ⟨91632801778516857357437525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61088534519011238238291683 91632801778516857357437525)
                  ·
                    refine ⟨1073821895841994422157471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91632801778516857357437525 1073821895841994422157471)
                    ·
                      rfl

theorem cell22_3136891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_3136891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136891 prefixEnd_3136891 := by exact prefixLift 3136891
  have htrace : WordTrace (prefixWord ++ tailWord_3136891) baseStart_3136891 baseEnd_3136891 := by
    simpa [prefixWord, tailWord_3136891, baseEnd_3136891] using wordTrace_append hprefix tailTrace_3136891
  have hstable : (prefixWord ++ tailWord_3136891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136891).length < 2 ^ (prefixWord ++ tailWord_3136891).sum := by decide
  have hdescent : baseEnd_3136891 < baseStart_3136891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136914 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3136914 : Nat := 118140960795 + 3136914 * 2 ^ 59
def prefixEnd_3136914 : Nat := 4983230072969 + 3 ^ 40 * 3136914 * 2
def baseEnd_3136914 : Nat := 1073829769212030028832401

theorem tailTrace_3136914 : CollatzResearch.WordTrace tailWord_3136914 prefixEnd_3136914 1073829769212030028832401 := by
  unfold tailWord_3136914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603163239375948775922449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76275101971669196735793197 28603163239375948775922449)
  ·
    refine ⟨21452372429531961581941837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28603163239375948775922449 21452372429531961581941837)
    ·
      refine ⟨8044639661074485593228189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21452372429531961581941837 8044639661074485593228189)
      ·
        refine ⟨3016739872902932097460571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8044639661074485593228189 3016739872902932097460571)
        ·
          refine ⟨4525109809354398146190857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016739872902932097460571 4525109809354398146190857)
          ·
            refine ⟨3393832357015798609643143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525109809354398146190857 3393832357015798609643143)
            ·
              refine ⟨5090748535523697914464715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393832357015798609643143 5090748535523697914464715)
              ·
                refine ⟨7636122803285546871697073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090748535523697914464715 7636122803285546871697073)
                ·
                  refine ⟨5727092102464160153772805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7636122803285546871697073 5727092102464160153772805)
                  ·
                    refine ⟨1073829769212030028832401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727092102464160153772805 1073829769212030028832401)
                    ·
                      rfl

theorem cell22_3136914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3136914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136914 prefixEnd_3136914 := by exact prefixLift 3136914
  have htrace : WordTrace (prefixWord ++ tailWord_3136914) baseStart_3136914 baseEnd_3136914 := by
    simpa [prefixWord, tailWord_3136914, baseEnd_3136914] using wordTrace_append hprefix tailTrace_3136914
  have hstable : (prefixWord ++ tailWord_3136914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136914).length < 2 ^ (prefixWord ++ tailWord_3136914).sum := by decide
  have hdescent : baseEnd_3136914 < baseStart_3136914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136927 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 1, 3]
def baseStart_3136927 : Nat := 118140960795 + 3136927 * 2 ^ 59
def prefixEnd_3136927 : Nat := 4983230072969 + 3 ^ 40 * 3136927 * 2
def baseEnd_3136927 : Nat := 1073834219377702328257361

theorem tailTrace_3136927 : CollatzResearch.WordTrace tailWord_3136927 prefixEnd_3136927 1073834219377702328257361 := by
  unfold tailWord_3136927
  simp only [CollatzResearch.WordTrace]
  refine ⟨114413127106456698323913035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76275418070971132215942023 114413127106456698323913035)
  ·
    refine ⟨171619690659685047485869553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114413127106456698323913035 171619690659685047485869553)
    ·
      refine ⟨128714767994763785614402165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171619690659685047485869553 128714767994763785614402165)
      ·
        refine ⟨12067009499509104901350203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128714767994763785614402165 12067009499509104901350203)
        ·
          refine ⟨18100514249263657352025305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067009499509104901350203 18100514249263657352025305)
          ·
            refine ⟨13575385686947743014018979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18100514249263657352025305 13575385686947743014018979)
            ·
              refine ⟨20363078530421614521028469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13575385686947743014018979 20363078530421614521028469)
              ·
                refine ⟨1909038612227026361346419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20363078530421614521028469 1909038612227026361346419)
                ·
                  refine ⟨2863557918340539542019629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909038612227026361346419 2863557918340539542019629)
                  ·
                    refine ⟨1073834219377702328257361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863557918340539542019629 1073834219377702328257361)
                    ·
                      rfl

theorem cell22_3136927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_3136927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136927 prefixEnd_3136927 := by exact prefixLift 3136927
  have htrace : WordTrace (prefixWord ++ tailWord_3136927) baseStart_3136927 baseEnd_3136927 := by
    simpa [prefixWord, tailWord_3136927, baseEnd_3136927] using wordTrace_append hprefix tailTrace_3136927
  have hstable : (prefixWord ++ tailWord_3136927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136927).length < 2 ^ (prefixWord ++ tailWord_3136927).sum := by decide
  have hdescent : baseEnd_3136927 < baseStart_3136927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136968 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_3136968 : Nat := 118140960795 + 3136968 * 2 ^ 59
def prefixEnd_3136968 : Nat := 4983230072969 + 3 ^ 40 * 3136968 * 2
def baseEnd_3136968 : Nat := 357949418171863962660745

theorem tailTrace_3136968 : CollatzResearch.WordTrace tailWord_3136968 prefixEnd_3136968 357949418171863962660745 := by
  unfold tailWord_3136968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207311249654081163077779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76276414999538774884103705 57207311249654081163077779)
  ·
    refine ⟨85810966874481121744616669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57207311249654081163077779 85810966874481121744616669)
    ·
      refine ⟨32179112577930420654231251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85810966874481121744616669 32179112577930420654231251)
      ·
        refine ⟨48268668866895630981346877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32179112577930420654231251 48268668866895630981346877)
        ·
          refine ⟨18100750825085861618005079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48268668866895630981346877 18100750825085861618005079)
          ·
            refine ⟨27151126237628792427007619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18100750825085861618005079 27151126237628792427007619)
            ·
              refine ⟨40726689356443188640511429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27151126237628792427007619 40726689356443188640511429)
              ·
                refine ⟨7636254254333097870095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40726689356443188640511429 7636254254333097870095893)
                ·
                  refine ⟨357949418171863962660745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7636254254333097870095893 357949418171863962660745)
                  ·
                    rfl

theorem cell22_3136968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_3136968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136968 prefixEnd_3136968 := by exact prefixLift 3136968
  have htrace : WordTrace (prefixWord ++ tailWord_3136968) baseStart_3136968 baseEnd_3136968 := by
    simpa [prefixWord, tailWord_3136968, baseEnd_3136968] using wordTrace_append hprefix tailTrace_3136968
  have hstable : (prefixWord ++ tailWord_3136968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136968).length < 2 ^ (prefixWord ++ tailWord_3136968).sum := by decide
  have hdescent : baseEnd_3136968 < baseStart_3136968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136970 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3136970 : Nat := 118140960795 + 3136970 * 2 ^ 59
def prefixEnd_3136970 : Nat := 4983230072969 + 3 ^ 40 * 3136970 * 2
def baseEnd_3136970 : Nat := 1073848939156464549432229

theorem tailTrace_3136970 : CollatzResearch.WordTrace tailWord_3136970 prefixEnd_3136970 1073848939156464549432229 := by
  unfold tailWord_3136970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603673861325229166932091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76276463630200611111818909 28603673861325229166932091)
  ·
    refine ⟨42905510791987843750398137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603673861325229166932091 42905510791987843750398137)
    ·
      refine ⟨32179133093990882812798603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42905510791987843750398137 32179133093990882812798603)
      ·
        refine ⟨48268699640986324219197905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32179133093990882812798603 48268699640986324219197905)
        ·
          refine ⟨36201524730739743164398429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48268699640986324219197905 36201524730739743164398429)
          ·
            refine ⟨13575571774027403686649411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36201524730739743164398429 13575571774027403686649411)
            ·
              refine ⟨20363357661041105529974117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13575571774027403686649411 20363357661041105529974117)
              ·
                refine ⟨3818129561445207286870147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20363357661041105529974117 3818129561445207286870147)
                ·
                  refine ⟨5727194342167810930305221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818129561445207286870147 5727194342167810930305221)
                  ·
                    refine ⟨1073848939156464549432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727194342167810930305221 1073848939156464549432229)
                    ·
                      rfl

theorem cell22_3136970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3136970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136970 prefixEnd_3136970 := by exact prefixLift 3136970
  have htrace : WordTrace (prefixWord ++ tailWord_3136970) baseStart_3136970 baseEnd_3136970 := by
    simpa [prefixWord, tailWord_3136970, baseEnd_3136970] using wordTrace_append hprefix tailTrace_3136970
  have hstable : (prefixWord ++ tailWord_3136970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136970).length < 2 ^ (prefixWord ++ tailWord_3136970).sum := by decide
  have hdescent : baseEnd_3136970 < baseStart_3136970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136983 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3136983 : Nat := 118140960795 + 3136983 * 2 ^ 59
def prefixEnd_3136983 : Nat := 4983230072969 + 3 ^ 40 * 3136983 * 2
def baseEnd_3136983 : Nat := 1073853389322136848857189

theorem tailTrace_3136983 : CollatzResearch.WordTrace tailWord_3136983 prefixEnd_3136983 1073853389322136848857189 := by
  unfold tailWord_3136983
  simp only [CollatzResearch.WordTrace]
  refine ⟨114415169594253819887951603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76276779729502546591967735 114415169594253819887951603)
  ·
    refine ⟨171622754391380729831927405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114415169594253819887951603 171622754391380729831927405)
    ·
      refine ⟨64358532896767773686972777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171622754391380729831927405 64358532896767773686972777)
      ·
        refine ⟨48268899672575830265229583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64358532896767773686972777 48268899672575830265229583)
        ·
          refine ⟨72403349508863745397844375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48268899672575830265229583 72403349508863745397844375)
          ·
            refine ⟨108605024263295618096766563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72403349508863745397844375 108605024263295618096766563)
            ·
              refine ⟨162907536394943427145149845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108605024263295618096766563 162907536394943427145149845)
              ·
                refine ⟨7636290768512973147428899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162907536394943427145149845 7636290768512973147428899)
                ·
                  refine ⟨11454436152769459721143349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7636290768512973147428899 11454436152769459721143349)
                  ·
                    refine ⟨1073853389322136848857189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11454436152769459721143349 1073853389322136848857189)
                    ·
                      rfl

theorem cell22_3136983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3136983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3136983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3136983 prefixEnd_3136983 := by exact prefixLift 3136983
  have htrace : WordTrace (prefixWord ++ tailWord_3136983) baseStart_3136983 baseEnd_3136983 := by
    simpa [prefixWord, tailWord_3136983, baseEnd_3136983] using wordTrace_append hprefix tailTrace_3136983
  have hstable : (prefixWord ++ tailWord_3136983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136983).length < 2 ^ (prefixWord ++ tailWord_3136983).sum := by decide
  have hdescent : baseEnd_3136983 < baseStart_3136983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137000 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3137000 : Nat := 118140960795 + 3137000 * 2 ^ 59
def prefixEnd_3137000 : Nat := 4983230072969 + 3 ^ 40 * 3137000 * 2
def baseEnd_3137000 : Nat := 1073859208769554471182137

theorem tailTrace_3137000 : CollatzResearch.WordTrace tailWord_3137000 prefixEnd_3137000 1073859208769554471182137 := by
  unfold tailWord_3137000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207894817596115895660227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76277193090128154527546969 57207894817596115895660227)
  ·
    refine ⟨85811842226394173843490341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57207894817596115895660227 85811842226394173843490341)
    ·
      refine ⟨16089720417448907595654439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85811842226394173843490341 16089720417448907595654439)
      ·
        refine ⟨24134580626173361393481659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089720417448907595654439 24134580626173361393481659)
        ·
          refine ⟨36201870939260042090222489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24134580626173361393481659 36201870939260042090222489)
          ·
            refine ⟨27151403204445031567666867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36201870939260042090222489 27151403204445031567666867)
            ·
              refine ⟨40727104806667547351500301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27151403204445031567666867 40727104806667547351500301)
              ·
                refine ⟨15272664302500330256812613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40727104806667547351500301 15272664302500330256812613)
                ·
                  refine ⟨2863624556718811923152365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15272664302500330256812613 2863624556718811923152365)
                  ·
                    refine ⟨1073859208769554471182137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863624556718811923152365 1073859208769554471182137)
                    ·
                      rfl

theorem cell22_3137000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3137000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137000 prefixEnd_3137000 := by exact prefixLift 3137000
  have htrace : WordTrace (prefixWord ++ tailWord_3137000) baseStart_3137000 baseEnd_3137000 := by
    simpa [prefixWord, tailWord_3137000, baseEnd_3137000] using wordTrace_append hprefix tailTrace_3137000
  have hstable : (prefixWord ++ tailWord_3137000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137000).length < 2 ^ (prefixWord ++ tailWord_3137000).sum := by decide
  have hdescent : baseEnd_3137000 < baseStart_3137000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137002 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_3137002 : Nat := 118140960795 + 3137002 * 2 ^ 59
def prefixEnd_3137002 : Nat := 4983230072969 + 3 ^ 40 * 3137002 * 2
def baseEnd_3137002 : Nat := 357953297803475710877377

theorem tailTrace_3137002 : CollatzResearch.WordTrace tailWord_3137002 prefixEnd_3137002 357953297803475710877377 := by
  unfold tailWord_3137002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603965645296246533223315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76277241720789990755262173 28603965645296246533223315)
  ·
    refine ⟨42905948467944369799834973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603965645296246533223315 42905948467944369799834973)
    ·
      refine ⟨16089730675479138674938115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42905948467944369799834973 16089730675479138674938115)
      ·
        refine ⟨24134596013218708012407173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089730675479138674938115 24134596013218708012407173)
        ·
          refine ⟨4525236752478507752326345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24134596013218708012407173 4525236752478507752326345)
          ·
            refine ⟨3393927564358880814244759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525236752478507752326345 3393927564358880814244759)
            ·
              refine ⟨5090891346538321221367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393927564358880814244759 5090891346538321221367139)
              ·
                refine ⟨7636337019807481832050709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090891346538321221367139 7636337019807481832050709)
                ·
                  refine ⟨357953297803475710877377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7636337019807481832050709 357953297803475710877377)
                  ·
                    rfl

theorem cell22_3137002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_3137002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137002 prefixEnd_3137002 := by exact prefixLift 3137002
  have htrace : WordTrace (prefixWord ++ tailWord_3137002) baseStart_3137002 baseEnd_3137002 := by
    simpa [prefixWord, tailWord_3137002, baseEnd_3137002] using wordTrace_append hprefix tailTrace_3137002
  have hstable : (prefixWord ++ tailWord_3137002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137002).length < 2 ^ (prefixWord ++ tailWord_3137002).sum := by decide
  have hdescent : baseEnd_3137002 < baseStart_3137002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137064 : List Nat := [2, 1, 5, 2, 3, 1, 1, 7]
def baseStart_3137064 : Nat := 118140960795 + 3137064 * 2 ^ 59
def prefixEnd_3137064 : Nat := 4983230072969 + 3 ^ 40 * 3137064 * 2
def baseEnd_3137064 : Nat := 119320124141942181953549

theorem tailTrace_3137064 : CollatzResearch.WordTrace tailWord_3137064 prefixEnd_3137064 119320124141942181953549 := by
  unfold tailWord_3137064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57209061953480185360825123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76278749271306913814433497 57209061953480185360825123)
  ·
    refine ⟨85813592930220278041237685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57209061953480185360825123 85813592930220278041237685)
    ·
      refine ⟨8045024337208151066366033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85813592930220278041237685 8045024337208151066366033)
      ·
        refine ⟨6033768252906113299774525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045024337208151066366033 6033768252906113299774525)
        ·
          refine ⟨2262663094839792487415447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6033768252906113299774525 2262663094839792487415447)
          ·
            refine ⟨3393994642259688731123171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262663094839792487415447 3393994642259688731123171)
            ·
              refine ⟨5090991963389533096684757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393994642259688731123171 5090991963389533096684757)
              ·
                refine ⟨119320124141942181953549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5090991963389533096684757 119320124141942181953549)
                ·
                  rfl

theorem cell22_3137064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_3137064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137064 prefixEnd_3137064 := by exact prefixLift 3137064
  have htrace : WordTrace (prefixWord ++ tailWord_3137064) baseStart_3137064 baseEnd_3137064 := by
    simpa [prefixWord, tailWord_3137064, baseEnd_3137064] using wordTrace_append hprefix tailTrace_3137064
  have hstable : (prefixWord ++ tailWord_3137064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137064).length < 2 ^ (prefixWord ++ tailWord_3137064).sum := by decide
  have hdescent : baseEnd_3137064 < baseStart_3137064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137075 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 5]
def baseStart_3137075 : Nat := 118140960795 + 3137075 * 2 ^ 59
def prefixEnd_3137075 : Nat := 4983230072969 + 3 ^ 40 * 3137075 * 2
def baseEnd_3137075 : Nat := 357961627600759758518969

theorem tailTrace_3137075 : CollatzResearch.WordTrace tailWord_3137075 prefixEnd_3137075 357961627600759758518969 := by
  unfold tailWord_3137075
  simp only [CollatzResearch.WordTrace]
  refine ⟨114418525109920519600300679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76279016739947013066867119 114418525109920519600300679)
  ·
    refine ⟨171627787664880779400451019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114418525109920519600300679 171627787664880779400451019)
    ·
      refine ⟨257441681497321169100676529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171627787664880779400451019 257441681497321169100676529)
      ·
        refine ⟨193081261122990876825507397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257441681497321169100676529 193081261122990876825507397)
        ·
          refine ⟨36202736460560789404782637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193081261122990876825507397 36202736460560789404782637)
          ·
            refine ⟨13576026172710296026793489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36202736460560789404782637 13576026172710296026793489)
            ·
              refine ⟨10182019629532722020095117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13576026172710296026793489 10182019629532722020095117)
              ·
                refine ⟨3818257361074770757535669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10182019629532722020095117 3818257361074770757535669)
                ·
                  refine ⟨357961627600759758518969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818257361074770757535669 357961627600759758518969)
                  ·
                    rfl

theorem cell22_3137075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].length) (baseStart_3137075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137075 prefixEnd_3137075 := by exact prefixLift 3137075
  have htrace : WordTrace (prefixWord ++ tailWord_3137075) baseStart_3137075 baseEnd_3137075 := by
    simpa [prefixWord, tailWord_3137075, baseEnd_3137075] using wordTrace_append hprefix tailTrace_3137075
  have hstable : (prefixWord ++ tailWord_3137075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137075).length < 2 ^ (prefixWord ++ tailWord_3137075).sum := by decide
  have hdescent : baseEnd_3137075 < baseStart_3137075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137103 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 10]
def baseStart_3137103 : Nat := 118140960795 + 3137103 * 2 ^ 59
def prefixEnd_3137103 : Nat := 4983230072969 + 3 ^ 40 * 3137103 * 2
def baseEnd_3137103 : Nat := 357964822591498845285607

theorem tailTrace_3137103 : CollatzResearch.WordTrace tailWord_3137103 prefixEnd_3137103 357964822591498845285607 := by
  unfold tailWord_3137103
  simp only [CollatzResearch.WordTrace]
  refine ⟨114419546353819080382319963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76279697569212720254879975 114419546353819080382319963)
  ·
    refine ⟨171629319530728620573479945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114419546353819080382319963 171629319530728620573479945)
    ·
      refine ⟨128721989648046465430109959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171629319530728620573479945 128721989648046465430109959)
      ·
        refine ⟨193082984472069698145164939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128721989648046465430109959 193082984472069698145164939)
        ·
          refine ⟨289624476708104547217747409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193082984472069698145164939 289624476708104547217747409)
          ·
            refine ⟨217218357531078410413310557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289624476708104547217747409 217218357531078410413310557)
            ·
              refine ⟨81456884074154403904991459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217218357531078410413310557 81456884074154403904991459)
              ·
                refine ⟨122185326111231605857487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81456884074154403904991459 122185326111231605857487189)
                ·
                  refine ⟨357964822591498845285607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122185326111231605857487189 357964822591498845285607)
                  ·
                    rfl

theorem cell22_3137103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_3137103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137103 prefixEnd_3137103 := by exact prefixLift 3137103
  have htrace : WordTrace (prefixWord ++ tailWord_3137103) baseStart_3137103 baseEnd_3137103 := by
    simpa [prefixWord, tailWord_3137103, baseEnd_3137103] using wordTrace_append hprefix tailTrace_3137103
  have hstable : (prefixWord ++ tailWord_3137103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137103).length < 2 ^ (prefixWord ++ tailWord_3137103).sum := by decide
  have hdescent : baseEnd_3137103 < baseStart_3137103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137182 : List Nat := [4, 3, 1, 1, 1, 2, 1, 9]
def baseStart_3137182 : Nat := 118140960795 + 3137182 * 2 ^ 59
def prefixEnd_3137182 : Nat := 4983230072969 + 3 ^ 40 * 3137182 * 2
def baseEnd_3137182 : Nat := 119324612343218518125731

theorem tailTrace_3137182 : CollatzResearch.WordTrace tailWord_3137182 prefixEnd_3137182 119324612343218518125731 := by
  unfold tailWord_3137182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302803465066609609305725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76281618480355251249630533 14302803465066609609305725)
  ·
    refine ⟨5363551299399978603489647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14302803465066609609305725 5363551299399978603489647)
    ·
      refine ⟨8045326949099967905234471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5363551299399978603489647 8045326949099967905234471)
      ·
        refine ⟨12067990423649951857851707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8045326949099967905234471 12067990423649951857851707)
        ·
          refine ⟨18101985635474927786777561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067990423649951857851707 18101985635474927786777561)
          ·
            refine ⟨13576489226606195840083171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18101985635474927786777561 13576489226606195840083171)
            ·
              refine ⟨20364733839909293760124757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576489226606195840083171 20364733839909293760124757)
              ·
                refine ⟨119324612343218518125731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20364733839909293760124757 119324612343218518125731)
                ·
                  rfl

theorem cell22_3137182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_3137182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137182 prefixEnd_3137182 := by exact prefixLift 3137182
  have htrace : WordTrace (prefixWord ++ tailWord_3137182) baseStart_3137182 baseEnd_3137182 := by
    simpa [prefixWord, tailWord_3137182, baseEnd_3137182] using wordTrace_append hprefix tailTrace_3137182
  have hstable : (prefixWord ++ tailWord_3137182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137182).length < 2 ^ (prefixWord ++ tailWord_3137182).sum := by decide
  have hdescent : baseEnd_3137182 < baseStart_3137182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137229 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3137229 : Nat := 118140960795 + 3137229 * 2 ^ 59
def prefixEnd_3137229 : Nat := 4983230072969 + 3 ^ 40 * 3137229 * 2
def baseEnd_3137229 : Nat := 1073937600149474207206435

theorem tailTrace_3137229 : CollatzResearch.WordTrace tailWord_3137229 prefixEnd_3137229 1073937600149474207206435 := by
  unfold tailWord_3137229
  simp only [CollatzResearch.WordTrace]
  refine ⟨114424141951362603901406741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76282761300908402600937827 114424141951362603901406741)
  ·
    refine ⟨5363631653970122057878441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114424141951362603901406741 5363631653970122057878441)
    ·
      refine ⟨4022723740477591543408831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5363631653970122057878441 4022723740477591543408831)
      ·
        refine ⟨6034085610716387315113247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022723740477591543408831 6034085610716387315113247)
        ·
          refine ⟨9051128416074580972669871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034085610716387315113247 9051128416074580972669871)
          ·
            refine ⟨13576692624111871459004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051128416074580972669871 13576692624111871459004807)
            ·
              refine ⟨20365038936167807188507211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576692624111871459004807 20365038936167807188507211)
              ·
                refine ⟨30547558404251710782760817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20365038936167807188507211 30547558404251710782760817)
                ·
                  refine ⟨22910668803188783087070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30547558404251710782760817 22910668803188783087070613)
                  ·
                    refine ⟨1073937600149474207206435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22910668803188783087070613 1073937600149474207206435)
                    ·
                      rfl

theorem cell22_3137229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3137229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137229 prefixEnd_3137229 := by exact prefixLift 3137229
  have htrace : WordTrace (prefixWord ++ tailWord_3137229) baseStart_3137229 baseEnd_3137229 := by
    simpa [prefixWord, tailWord_3137229, baseEnd_3137229] using wordTrace_append hprefix tailTrace_3137229
  have hstable : (prefixWord ++ tailWord_3137229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137229).length < 2 ^ (prefixWord ++ tailWord_3137229).sum := by decide
  have hdescent : baseEnd_3137229 < baseStart_3137229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137242 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_3137242 : Nat := 118140960795 + 3137242 * 2 ^ 59
def prefixEnd_3137242 : Nat := 4983230072969 + 3 ^ 40 * 3137242 * 2
def baseEnd_3137242 : Nat := 1073942050315146506631395

theorem tailTrace_3137242 : CollatzResearch.WordTrace tailWord_3137242 prefixEnd_3137242 1073942050315146506631395 := by
  unfold tailWord_3137242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28606154025078876780407495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76283077400210338081086653 28606154025078876780407495)
  ·
    refine ⟨42909231037618315170611243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28606154025078876780407495 42909231037618315170611243)
    ·
      refine ⟨64363846556427472755916865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42909231037618315170611243 64363846556427472755916865)
      ·
        refine ⟨48272884917320604566937649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64363846556427472755916865 48272884917320604566937649)
        ·
          refine ⟨36204663687990453425203237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48272884917320604566937649 36204663687990453425203237)
          ·
            refine ⟨6788374441498210017225607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36204663687990453425203237 6788374441498210017225607)
            ·
              refine ⟨10182561662247315025838411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788374441498210017225607 10182561662247315025838411)
              ·
                refine ⟨15273842493370972538757617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10182561662247315025838411 15273842493370972538757617)
                ·
                  refine ⟨11455381870028229404068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15273842493370972538757617 11455381870028229404068213)
                  ·
                    refine ⟨1073942050315146506631395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11455381870028229404068213 1073942050315146506631395)
                    ·
                      rfl

theorem cell22_3137242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_3137242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137242 prefixEnd_3137242 := by exact prefixLift 3137242
  have htrace : WordTrace (prefixWord ++ tailWord_3137242) baseStart_3137242 baseEnd_3137242 := by
    simpa [prefixWord, tailWord_3137242, baseEnd_3137242] using wordTrace_append hprefix tailTrace_3137242
  have hstable : (prefixWord ++ tailWord_3137242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137242).length < 2 ^ (prefixWord ++ tailWord_3137242).sum := by decide
  have hdescent : baseEnd_3137242 < baseStart_3137242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137257 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_3137257 : Nat := 118140960795 + 3137257 * 2 ^ 59
def prefixEnd_3137257 : Nat := 4983230072969 + 3 ^ 40 * 3137257 * 2
def baseEnd_3137257 : Nat := 1073947185121691467506349

theorem tailTrace_3137257 : CollatzResearch.WordTrace tailWord_3137257 prefixEnd_3137257 1073947185121691467506349 := by
  unfold tailWord_3137257
  simp only [CollatzResearch.WordTrace]
  refine ⟨114425163195261164683426025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76283442130174109788950683 114425163195261164683426025)
  ·
    refine ⟨85818872396445873512569519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114425163195261164683426025 85818872396445873512569519)
    ·
      refine ⟨128728308594668810268854279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85818872396445873512569519 128728308594668810268854279)
      ·
        refine ⟨193092462892003215403281419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128728308594668810268854279 193092462892003215403281419)
        ·
          refine ⟨289638694338004823104922129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193092462892003215403281419 289638694338004823104922129)
          ·
            refine ⟨217229020753503617328691597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289638694338004823104922129 217229020753503617328691597)
            ·
              refine ⟨81460882782563856498259349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217229020753503617328691597 81460882782563856498259349)
              ·
                refine ⟨3818478880432680773355907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81460882782563856498259349 3818478880432680773355907)
                ·
                  refine ⟨5727718320649021160033861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818478880432680773355907 5727718320649021160033861)
                  ·
                    refine ⟨1073947185121691467506349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727718320649021160033861 1073947185121691467506349)
                    ·
                      rfl

theorem cell22_3137257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_3137257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137257 prefixEnd_3137257 := by exact prefixLift 3137257
  have htrace : WordTrace (prefixWord ++ tailWord_3137257) baseStart_3137257 baseEnd_3137257 := by
    simpa [prefixWord, tailWord_3137257, baseEnd_3137257] using wordTrace_append hprefix tailTrace_3137257
  have hstable : (prefixWord ++ tailWord_3137257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137257).length < 2 ^ (prefixWord ++ tailWord_3137257).sum := by decide
  have hdescent : baseEnd_3137257 < baseStart_3137257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137278 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3137278 : Nat := 118140960795 + 3137278 * 2 ^ 59
def prefixEnd_3137278 : Nat := 4983230072969 + 3 ^ 40 * 3137278 * 2
def baseEnd_3137278 : Nat := 357984791283618137577095

theorem tailTrace_3137278 : CollatzResearch.WordTrace tailWord_3137278 prefixEnd_3137278 357984791283618137577095 := by
  unfold tailWord_3137278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303241141023135658742561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76283952752123390179960325 14303241141023135658742561)
  ·
    refine ⟨10727430855767351744056921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14303241141023135658742561 10727430855767351744056921)
    ·
      refine ⟨8045573141825513808042691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727430855767351744056921 8045573141825513808042691)
      ·
        refine ⟨12068359712738270712064037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8045573141825513808042691 12068359712738270712064037)
        ·
          refine ⟨2262817446138425758512007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12068359712738270712064037 2262817446138425758512007)
          ·
            refine ⟨3394226169207638637768011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262817446138425758512007 3394226169207638637768011)
            ·
              refine ⟨5091339253811457956652017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394226169207638637768011 5091339253811457956652017)
              ·
                refine ⟨3818504440358593467489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091339253811457956652017 3818504440358593467489013)
                ·
                  refine ⟨357984791283618137577095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818504440358593467489013 357984791283618137577095)
                  ·
                    rfl

theorem cell22_3137278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3137278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137278 prefixEnd_3137278 := by exact prefixLift 3137278
  have htrace : WordTrace (prefixWord ++ tailWord_3137278) baseStart_3137278 baseEnd_3137278 := by
    simpa [prefixWord, tailWord_3137278, baseEnd_3137278] using wordTrace_append hprefix tailTrace_3137278
  have hstable : (prefixWord ++ tailWord_3137278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137278).length < 2 ^ (prefixWord ++ tailWord_3137278).sum := by decide
  have hdescent : baseEnd_3137278 < baseStart_3137278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137304 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_3137304 : Nat := 118140960795 + 3137304 * 2 ^ 59
def prefixEnd_3137304 : Nat := 4983230072969 + 3 ^ 40 * 3137304 * 2
def baseEnd_3137304 : Nat := 1073963274182199011581205

theorem tailTrace_3137304 : CollatzResearch.WordTrace tailWord_3137304 prefixEnd_3137304 1073963274182199011581205 := by
  unfold tailWord_3137304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57213438713045445855193483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76284584950727261140257977 57213438713045445855193483)
  ·
    refine ⟨85820158069568168782790225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57213438713045445855193483 85820158069568168782790225)
    ·
      refine ⟨64365118552176126587092669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85820158069568168782790225 64365118552176126587092669)
      ·
        refine ⟨24136919457066047470159751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64365118552176126587092669 24136919457066047470159751)
        ·
          refine ⟨36205379185599071205239627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24136919457066047470159751 36205379185599071205239627)
          ·
            refine ⟨54308068778398606807859441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36205379185599071205239627 54308068778398606807859441)
            ·
              refine ⟨40731051583798955105894581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54308068778398606807859441 40731051583798955105894581)
              ·
                refine ⟨3818536085981152041177617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40731051583798955105894581 3818536085981152041177617)
                ·
                  refine ⟨2863902064485864030883213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3818536085981152041177617 2863902064485864030883213)
                  ·
                    refine ⟨1073963274182199011581205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863902064485864030883213 1073963274182199011581205)
                    ·
                      rfl

theorem cell22_3137304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_3137304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137304 prefixEnd_3137304 := by exact prefixLift 3137304
  have htrace : WordTrace (prefixWord ++ tailWord_3137304) baseStart_3137304 baseEnd_3137304 := by
    simpa [prefixWord, tailWord_3137304, baseEnd_3137304] using wordTrace_append hprefix tailTrace_3137304
  have hstable : (prefixWord ++ tailWord_3137304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137304).length < 2 ^ (prefixWord ++ tailWord_3137304).sum := by decide
  have hdescent : baseEnd_3137304 < baseStart_3137304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137317 : List Nat := [1, 3, 1, 2, 3, 3, 1, 8]
def baseStart_3137317 : Nat := 118140960795 + 3137317 * 2 ^ 59
def prefixEnd_3137317 : Nat := 4983230072969 + 3 ^ 40 * 3137317 * 2
def baseEnd_3137317 : Nat := 119329747149763479000685

theorem tailTrace_3137317 : CollatzResearch.WordTrace tailWord_3137317 prefixEnd_3137317 119329747149763479000685 := by
  unfold tailWord_3137317
  simp only [CollatzResearch.WordTrace]
  refine ⟨114427351575043794930610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76284901050029196620406803 114427351575043794930610205)
  ·
    refine ⟨42910256840641423098978827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114427351575043794930610205 42910256840641423098978827)
    ·
      refine ⟨64365385260962134648468241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42910256840641423098978827 64365385260962134648468241)
      ·
        refine ⟨48274038945721600986351181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64365385260962134648468241 48274038945721600986351181)
        ·
          refine ⟨18102764604645600369881693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48274038945721600986351181 18102764604645600369881693)
          ·
            refine ⟨6788536726742100138705635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18102764604645600369881693 6788536726742100138705635)
            ·
              refine ⟨10182805090113150208058453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788536726742100138705635 10182805090113150208058453)
              ·
                refine ⟨119329747149763479000685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10182805090113150208058453 119329747149763479000685)
                ·
                  rfl

theorem cell22_3137317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 8].length) (baseStart_3137317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137317 prefixEnd_3137317 := by exact prefixLift 3137317
  have htrace : WordTrace (prefixWord ++ tailWord_3137317) baseStart_3137317 baseEnd_3137317 := by
    simpa [prefixWord, tailWord_3137317, baseEnd_3137317] using wordTrace_append hprefix tailTrace_3137317
  have hstable : (prefixWord ++ tailWord_3137317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137317).length < 2 ^ (prefixWord ++ tailWord_3137317).sum := by decide
  have hdescent : baseEnd_3137317 < baseStart_3137317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137334 : List Nat := [5, 1, 2, 2, 1, 1, 10]
def baseStart_3137334 : Nat := 118140960795 + 3137334 * 2 ^ 59
def prefixEnd_3137334 : Nat := 4983230072969 + 3 ^ 40 * 3137334 * 2
def baseEnd_3137334 : Nat := 39776797918344034567819

theorem tailTrace_3137334 : CollatzResearch.WordTrace tailWord_3137334 prefixEnd_3137334 39776797918344034567819 := by
  unfold tailWord_3137334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151748225998887927123691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76285314410654804555986037 7151748225998887927123691)
  ·
    refine ⟨10727622338998331890685537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7151748225998887927123691 10727622338998331890685537)
    ·
      refine ⟨8045716754248748918014153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727622338998331890685537 8045716754248748918014153)
      ·
        refine ⟨6034287565686561688510615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045716754248748918014153 6034287565686561688510615)
        ·
          refine ⟨9051431348529842532765923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034287565686561688510615 9051431348529842532765923)
          ·
            refine ⟨13577147022794763799148885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051431348529842532765923 13577147022794763799148885)
            ·
              refine ⟨39776797918344034567819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13577147022794763799148885 39776797918344034567819)
              ·
                rfl

theorem cell22_3137334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 10].length) (baseStart_3137334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137334 prefixEnd_3137334 := by exact prefixLift 3137334
  have htrace : WordTrace (prefixWord ++ tailWord_3137334) baseStart_3137334 baseEnd_3137334 := by
    simpa [prefixWord, tailWord_3137334, baseEnd_3137334] using wordTrace_append hprefix tailTrace_3137334
  have hstable : (prefixWord ++ tailWord_3137334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137334).length < 2 ^ (prefixWord ++ tailWord_3137334).sum := by decide
  have hdescent : baseEnd_3137334 < baseStart_3137334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137407 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 6]
def baseStart_3137407 : Nat := 118140960795 + 3137407 * 2 ^ 59
def prefixEnd_3137407 : Nat := 4983230072969 + 3 ^ 40 * 3137407 * 2
def baseEnd_3137407 : Nat := 357999511062380358751963

theorem tailTrace_3137407 : CollatzResearch.WordTrace tailWord_3137407 prefixEnd_3137407 357999511062380358751963 := by
  unfold tailWord_3137407
  simp only [CollatzResearch.WordTrace]
  refine ⟨114430634144717740301386475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76287089429811826867590983 114430634144717740301386475)
  ·
    refine ⟨171645951217076610452079713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114430634144717740301386475 171645951217076610452079713)
    ·
      refine ⟨128734463412807457839059785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171645951217076610452079713 128734463412807457839059785)
      ·
        refine ⟨96550847559605593379294839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128734463412807457839059785 96550847559605593379294839)
        ·
          refine ⟨144826271339408390068942259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96550847559605593379294839 144826271339408390068942259)
          ·
            refine ⟨217239407009112585103413389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144826271339408390068942259 217239407009112585103413389)
            ·
              refine ⟨81464777628417219413780021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217239407009112585103413389 81464777628417219413780021)
              ·
                refine ⟨7637322902664114320041877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81464777628417219413780021 7637322902664114320041877)
                ·
                  refine ⟨357999511062380358751963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7637322902664114320041877 357999511062380358751963)
                  ·
                    rfl

theorem cell22_3137407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_3137407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137407 prefixEnd_3137407 := by exact prefixLift 3137407
  have htrace : WordTrace (prefixWord ++ tailWord_3137407) baseStart_3137407 baseEnd_3137407 := by
    simpa [prefixWord, tailWord_3137407, baseEnd_3137407] using wordTrace_append hprefix tailTrace_3137407
  have hstable : (prefixWord ++ tailWord_3137407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137407).length < 2 ^ (prefixWord ++ tailWord_3137407).sum := by decide
  have hdescent : baseEnd_3137407 < baseStart_3137407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137426 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3137426 : Nat := 118140960795 + 3137426 * 2 ^ 59
def prefixEnd_3137426 : Nat := 4983230072969 + 3 ^ 40 * 3137426 * 2
def baseEnd_3137426 : Nat := 1074005037275431360030831

theorem tailTrace_3137426 : CollatzResearch.WordTrace tailWord_3137426 prefixEnd_3137426 1074005037275431360030831 := by
  unfold tailWord_3137426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28607831782912226636582033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76287551421099271030885421 28607831782912226636582033)
  ·
    refine ⟨21455873837184169977436525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28607831782912226636582033 21455873837184169977436525)
    ·
      refine ⟨8045952688944063741538697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21455873837184169977436525 8045952688944063741538697)
      ·
        refine ⟨6034464516708047806154023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045952688944063741538697 6034464516708047806154023)
        ·
          refine ⟨9051696775062071709231035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034464516708047806154023 9051696775062071709231035)
          ·
            refine ⟨13577545162593107563846553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051696775062071709231035 13577545162593107563846553)
            ·
              refine ⟨10183158871944830672884915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13577545162593107563846553 10183158871944830672884915)
              ·
                refine ⟨15274738307917246009327373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10183158871944830672884915 15274738307917246009327373)
                ·
                  refine ⟨5728026865468967253497765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15274738307917246009327373 5728026865468967253497765)
                  ·
                    refine ⟨1074005037275431360030831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728026865468967253497765 1074005037275431360030831)
                    ·
                      rfl

theorem cell22_3137426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3137426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137426 prefixEnd_3137426 := by exact prefixLift 3137426
  have htrace : WordTrace (prefixWord ++ tailWord_3137426) baseStart_3137426 baseEnd_3137426 := by
    simpa [prefixWord, tailWord_3137426, baseEnd_3137426] using wordTrace_append hprefix tailTrace_3137426
  have hstable : (prefixWord ++ tailWord_3137426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137426).length < 2 ^ (prefixWord ++ tailWord_3137426).sum := by decide
  have hdescent : baseEnd_3137426 < baseStart_3137426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137467 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_3137467 : Nat := 118140960795 + 3137467 * 2 ^ 59
def prefixEnd_3137467 : Nat := 4983230072969 + 3 ^ 40 * 3137467 * 2
def baseEnd_3137467 : Nat := 1074019072413320919755705

theorem tailTrace_3137467 : CollatzResearch.WordTrace tailWord_3137467 prefixEnd_3137467 1074019072413320919755705 := by
  unfold tailWord_3137467
  simp only [CollatzResearch.WordTrace]
  refine ⟨114432822524500370548570655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76288548349666913699047103 114432822524500370548570655)
  ·
    refine ⟨171649233786750555822855983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114432822524500370548570655 171649233786750555822855983)
    ·
      refine ⟨257473850680125833734283975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171649233786750555822855983 257473850680125833734283975)
      ·
        refine ⟨386210776020188750601425963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257473850680125833734283975 386210776020188750601425963)
        ·
          refine ⟨579316164030283125902138945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386210776020188750601425963 579316164030283125902138945)
          ·
            refine ⟨434487123022712344426604209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579316164030283125902138945 434487123022712344426604209)
            ·
              refine ⟨325865342267034258319953157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434487123022712344426604209 325865342267034258319953157)
              ·
                refine ⟨61099751675068923434991217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325865342267034258319953157 61099751675068923434991217)
                ·
                  refine ⟨45824813756301692576243413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61099751675068923434991217 45824813756301692576243413)
                  ·
                    refine ⟨1074019072413320919755705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45824813756301692576243413 1074019072413320919755705)
                    ·
                      rfl

theorem cell22_3137467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_3137467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137467 prefixEnd_3137467 := by exact prefixLift 3137467
  have htrace : WordTrace (prefixWord ++ tailWord_3137467) baseStart_3137467 baseEnd_3137467 := by
    simpa [prefixWord, tailWord_3137467, baseEnd_3137467] using wordTrace_append hprefix tailTrace_3137467
  have hstable : (prefixWord ++ tailWord_3137467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137467).length < 2 ^ (prefixWord ++ tailWord_3137467).sum := by decide
  have hdescent : baseEnd_3137467 < baseStart_3137467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137514 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_3137514 : Nat := 118140960795 + 3137514 * 2 ^ 59
def prefixEnd_3137514 : Nat := 4983230072969 + 3 ^ 40 * 3137514 * 2
def baseEnd_3137514 : Nat := 358011720491276154610187

theorem tailTrace_3137514 : CollatzResearch.WordTrace tailWord_3137514 prefixEnd_3137514 358011720491276154610187 := by
  unfold tailWord_3137514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608634188832524393882899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76289691170220065050354397 28608634188832524393882899)
  ·
    refine ⟨42912951283248786590824349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608634188832524393882899 42912951283248786590824349)
    ·
      refine ⟨16092356731218294971559131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42912951283248786590824349 16092356731218294971559131)
      ·
        refine ⟨24138535096827442457338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092356731218294971559131 24138535096827442457338697)
        ·
          refine ⟨18103901322620581843004023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24138535096827442457338697 18103901322620581843004023)
          ·
            refine ⟨27155851983930872764506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18103901322620581843004023 27155851983930872764506035)
            ·
              refine ⟨40733777975896309146759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27155851983930872764506035 40733777975896309146759053)
              ·
                refine ⟨15275166740961115930034645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40733777975896309146759053 15275166740961115930034645)
                ·
                  refine ⟨358011720491276154610187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15275166740961115930034645 358011720491276154610187)
                  ·
                    rfl

theorem cell22_3137514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_3137514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137514 prefixEnd_3137514 := by exact prefixLift 3137514
  have htrace : WordTrace (prefixWord ++ tailWord_3137514) baseStart_3137514 baseEnd_3137514 := by
    simpa [prefixWord, tailWord_3137514, baseEnd_3137514] using wordTrace_append hprefix tailTrace_3137514
  have hstable : (prefixWord ++ tailWord_3137514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137514).length < 2 ^ (prefixWord ++ tailWord_3137514).sum := by decide
  have hdescent : baseEnd_3137514 < baseStart_3137514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137518 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3137518 : Nat := 118140960795 + 3137518 * 2 ^ 59
def prefixEnd_3137518 : Nat := 4983230072969 + 3 ^ 40 * 3137518 * 2
def baseEnd_3137518 : Nat := 1074036530755573786730549

theorem tailTrace_3137518 : CollatzResearch.WordTrace tailWord_3137518 prefixEnd_3137518 1074036530755573786730549 := by
  unfold tailWord_3137518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304335330914450782334651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76289788431543737505784805 14304335330914450782334651)
  ·
    refine ⟨21456502996371676173501977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304335330914450782334651 21456502996371676173501977)
    ·
      refine ⟨16092377247278757130126483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21456502996371676173501977 16092377247278757130126483)
      ·
        refine ⟨24138565870918135695189725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092377247278757130126483 24138565870918135695189725)
        ·
          refine ⟨9051962201594300885696147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24138565870918135695189725 9051962201594300885696147)
          ·
            refine ⟨13577943302391451328544221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051962201594300885696147 13577943302391451328544221)
            ·
              refine ⟨5091728738396794248204083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13577943302391451328544221 5091728738396794248204083)
              ·
                refine ⟨7637593107595191372306125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091728738396794248204083 7637593107595191372306125)
                ·
                  refine ⟨2864097415348196764614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7637593107595191372306125 2864097415348196764614797)
                  ·
                    refine ⟨1074036530755573786730549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864097415348196764614797 1074036530755573786730549)
                    ·
                      rfl

theorem cell22_3137518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3137518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137518 prefixEnd_3137518 := by exact prefixLift 3137518
  have htrace : WordTrace (prefixWord ++ tailWord_3137518) baseStart_3137518 baseEnd_3137518 := by
    simpa [prefixWord, tailWord_3137518, baseEnd_3137518] using wordTrace_append hprefix tailTrace_3137518
  have hstable : (prefixWord ++ tailWord_3137518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137518).length < 2 ^ (prefixWord ++ tailWord_3137518).sum := by decide
  have hdescent : baseEnd_3137518 < baseStart_3137518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137531 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 5]
def baseStart_3137531 : Nat := 118140960795 + 3137531 * 2 ^ 59
def prefixEnd_3137531 : Nat := 4983230072969 + 3 ^ 40 * 3137531 * 2
def baseEnd_3137531 : Nat := 358013660307082028718503

theorem tailTrace_3137531 : CollatzResearch.WordTrace tailWord_3137531 prefixEnd_3137531 358013660307082028718503 := by
  unfold tailWord_3137531
  simp only [CollatzResearch.WordTrace]
  refine ⟨114435156796268509478900447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76290104530845672985933631 114435156796268509478900447)
  ·
    refine ⟨171652735194402764218350671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114435156796268509478900447 171652735194402764218350671)
    ·
      refine ⟨257479102791604146327526007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171652735194402764218350671 257479102791604146327526007)
      ·
        refine ⟨386218654187406219491289011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257479102791604146327526007 386218654187406219491289011)
        ·
          refine ⟨579327981281109329236933517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386218654187406219491289011 579327981281109329236933517)
          ·
            refine ⟨217247992980415998463850069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579327981281109329236933517 217247992980415998463850069)
            ·
              refine ⟨2545874917739249981998243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 217247992980415998463850069 2545874917739249981998243)
              ·
                refine ⟨3818812376608874972997365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545874917739249981998243 3818812376608874972997365)
                ·
                  refine ⟨358013660307082028718503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818812376608874972997365 358013660307082028718503)
                  ·
                    rfl

theorem cell22_3137531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 5].length) (baseStart_3137531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137531 prefixEnd_3137531 := by exact prefixLift 3137531
  have htrace : WordTrace (prefixWord ++ tailWord_3137531) baseStart_3137531 baseEnd_3137531 := by
    simpa [prefixWord, tailWord_3137531, baseEnd_3137531] using wordTrace_append hprefix tailTrace_3137531
  have hstable : (prefixWord ++ tailWord_3137531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137531).length < 2 ^ (prefixWord ++ tailWord_3137531).sum := by decide
  have hdescent : baseEnd_3137531 < baseStart_3137531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137569 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3137569 : Nat := 118140960795 + 3137569 * 2 ^ 59
def prefixEnd_3137569 : Nat := 4983230072969 + 3 ^ 40 * 3137569 * 2
def baseEnd_3137569 : Nat := 1074053989097826653705393

theorem tailTrace_3137569 : CollatzResearch.WordTrace tailWord_3137569 prefixEnd_3137569 1074053989097826653705393 := by
  unfold tailWord_3137569
  simp only [CollatzResearch.WordTrace]
  refine ⟨114436542770130841968783761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76291028513420561312522507 114436542770130841968783761)
  ·
    refine ⟨85827407077598131476587821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114436542770130841968783761 85827407077598131476587821)
    ·
      refine ⟨32185277654099299303720433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85827407077598131476587821 32185277654099299303720433)
      ·
        refine ⟨24138958240574474477790325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32185277654099299303720433 24138958240574474477790325)
        ·
          refine ⟨2263027335053856982292843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24138958240574474477790325 2263027335053856982292843)
          ·
            refine ⟨3394541002580785473439265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263027335053856982292843 3394541002580785473439265)
            ·
              refine ⟨2545905751935589105079449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3394541002580785473439265 2545905751935589105079449)
              ·
                refine ⟨1909429313951691828809587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545905751935589105079449 1909429313951691828809587)
                ·
                  refine ⟨2864143970927537743214381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909429313951691828809587 2864143970927537743214381)
                  ·
                    refine ⟨1074053989097826653705393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864143970927537743214381 1074053989097826653705393)
                    ·
                      rfl

theorem cell22_3137569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3137569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137569 prefixEnd_3137569 := by exact prefixLift 3137569
  have htrace : WordTrace (prefixWord ++ tailWord_3137569) baseStart_3137569 baseEnd_3137569 := by
    simpa [prefixWord, tailWord_3137569, baseEnd_3137569] using wordTrace_append hprefix tailTrace_3137569
  have hstable : (prefixWord ++ tailWord_3137569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137569).length < 2 ^ (prefixWord ++ tailWord_3137569).sum := by decide
  have hdescent : baseEnd_3137569 < baseStart_3137569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137642 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3137642 : Nat := 118140960795 + 3137642 * 2 ^ 59
def prefixEnd_3137642 : Nat := 4983230072969 + 3 ^ 40 * 3137642 * 2
def baseEnd_3137642 : Nat := 1074078978489678796630169

theorem tailTrace_3137642 : CollatzResearch.WordTrace tailWord_3137642 prefixEnd_3137642 1074078978489678796630169 := by
  unfold tailWord_3137642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28609801324716593859047795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76292803532577583624127453 28609801324716593859047795)
  ·
    refine ⟨42914701987074890788571693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28609801324716593859047795 42914701987074890788571693)
    ·
      refine ⟨16093013245153084045714385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42914701987074890788571693 16093013245153084045714385)
      ·
        refine ⟨12069759933864813034285789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093013245153084045714385 12069759933864813034285789)
        ·
          refine ⟨4526159975199304887857171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12069759933864813034285789 4526159975199304887857171)
          ·
            refine ⟨6789239962798957331785757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526159975199304887857171 6789239962798957331785757)
            ·
              refine ⟨2545964986049608999419659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6789239962798957331785757 2545964986049608999419659)
              ·
                refine ⟨3818947479074413499129489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545964986049608999419659 3818947479074413499129489)
                ·
                  refine ⟨2864210609305810124347117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3818947479074413499129489 2864210609305810124347117)
                  ·
                    refine ⟨1074078978489678796630169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864210609305810124347117 1074078978489678796630169)
                    ·
                      rfl

theorem cell22_3137642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3137642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137642 prefixEnd_3137642 := by exact prefixLift 3137642
  have htrace : WordTrace (prefixWord ++ tailWord_3137642) baseStart_3137642 baseEnd_3137642 := by
    simpa [prefixWord, tailWord_3137642, baseEnd_3137642] using wordTrace_append hprefix tailTrace_3137642
  have hstable : (prefixWord ++ tailWord_3137642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137642).length < 2 ^ (prefixWord ++ tailWord_3137642).sum := by decide
  have hdescent : baseEnd_3137642 < baseStart_3137642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137687 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 3, 3]
def baseStart_3137687 : Nat := 118140960795 + 3137687 * 2 ^ 59
def prefixEnd_3137687 : Nat := 4983230072969 + 3 ^ 40 * 3137687 * 2
def baseEnd_3137687 : Nat := 1074094382909313679255031

theorem tailTrace_3137687 : CollatzResearch.WordTrace tailWord_3137687 prefixEnd_3137687 1074094382909313679255031 := by
  unfold tailWord_3137687
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440846583703348121579315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76293897722468898747719543 114440846583703348121579315)
  ·
    refine ⟨171661269875555022182368973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114440846583703348121579315 171661269875555022182368973)
    ·
      refine ⟨64372976203333133318388365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171661269875555022182368973 64372976203333133318388365)
      ·
        refine ⟨24139866076249924994395637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64372976203333133318388365 24139866076249924994395637)
        ·
          refine ⟨2263112444648430468224591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24139866076249924994395637 2263112444648430468224591)
          ·
            refine ⟨3394668666972645702336887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263112444648430468224591 3394668666972645702336887)
            ·
              refine ⟨5092003000458968553505331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394668666972645702336887 5092003000458968553505331)
              ·
                refine ⟨7638004500688452830257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092003000458968553505331 7638004500688452830257997)
                ·
                  refine ⟨2864251687758169811346749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7638004500688452830257997 2864251687758169811346749)
                  ·
                    refine ⟨1074094382909313679255031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864251687758169811346749 1074094382909313679255031)
                    ·
                      rfl

theorem cell22_3137687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_3137687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137687 prefixEnd_3137687 := by exact prefixLift 3137687
  have htrace : WordTrace (prefixWord ++ tailWord_3137687) baseStart_3137687 baseEnd_3137687 := by
    simpa [prefixWord, tailWord_3137687, baseEnd_3137687] using wordTrace_append hprefix tailTrace_3137687
  have hstable : (prefixWord ++ tailWord_3137687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137687).length < 2 ^ (prefixWord ++ tailWord_3137687).sum := by decide
  have hdescent : baseEnd_3137687 < baseStart_3137687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137745 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 4]
def baseStart_3137745 : Nat := 118140960795 + 3137745 * 2 ^ 59
def prefixEnd_3137745 : Nat := 4983230072969 + 3 ^ 40 * 3137745 * 2
def baseEnd_3137745 : Nat := 358038079164873620434951

theorem tailTrace_3137745 : CollatzResearch.WordTrace tailWord_3137745 prefixEnd_3137745 358038079164873620434951 := by
  unfold tailWord_3137745
  simp only [CollatzResearch.WordTrace]
  refine ⟨114442962017493224027190689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76295308011662149351460459 114442962017493224027190689)
  ·
    refine ⟨85832221513119918020393017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114442962017493224027190689 85832221513119918020393017)
    ·
      refine ⟨64374166134839938515294763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85832221513119918020393017 64374166134839938515294763)
      ·
        refine ⟨96561249202259907772942145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64374166134839938515294763 96561249202259907772942145)
        ·
          refine ⟨72420936901694930829706609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96561249202259907772942145 72420936901694930829706609)
          ·
            refine ⟨54315702676271198122279957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72420936901694930829706609 54315702676271198122279957)
            ·
              refine ⟨2546048562950212411981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54315702676271198122279957 2546048562950212411981873)
              ·
                refine ⟨1909536422212659308986405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546048562950212411981873 1909536422212659308986405)
                ·
                  refine ⟨358038079164873620434951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909536422212659308986405 358038079164873620434951)
                  ·
                    rfl

theorem cell22_3137745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_3137745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137745 prefixEnd_3137745 := by exact prefixLift 3137745
  have htrace : WordTrace (prefixWord ++ tailWord_3137745) baseStart_3137745 baseEnd_3137745 := by
    simpa [prefixWord, tailWord_3137745, baseEnd_3137745] using wordTrace_append hprefix tailTrace_3137745
  have hstable : (prefixWord ++ tailWord_3137745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137745).length < 2 ^ (prefixWord ++ tailWord_3137745).sum := by decide
  have hdescent : baseEnd_3137745 < baseStart_3137745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137775 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 2, 4]
def baseStart_3137775 : Nat := 118140960795 + 3137775 * 2 ^ 59
def prefixEnd_3137775 : Nat := 4983230072969 + 3 ^ 40 * 3137775 * 2
def baseEnd_3137775 : Nat := 1074124507107710783054761

theorem tailTrace_3137775 : CollatzResearch.WordTrace tailWord_3137775 prefixEnd_3137775 1074124507107710783054761 := by
  unfold tailWord_3137775
  simp only [CollatzResearch.WordTrace]
  refine ⟨114444056207384539150782779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76296037471589692767188519 114444056207384539150782779)
  ·
    refine ⟨171666084311076808726174169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114444056207384539150782779 171666084311076808726174169)
    ·
      refine ⟨128749563233307606544630627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171666084311076808726174169 128749563233307606544630627)
      ·
        refine ⟨193124344849961409816945941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128749563233307606544630627 193124344849961409816945941)
        ·
          refine ⟨9052703664841941085169341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193124344849961409816945941 9052703664841941085169341)
          ·
            refine ⟨3394763874315727906938503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9052703664841941085169341 3394763874315727906938503)
            ·
              refine ⟨5092145811473591860407755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394763874315727906938503 5092145811473591860407755)
              ·
                refine ⟨7638218717210387790611633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092145811473591860407755 7638218717210387790611633)
                ·
                  refine ⟨5728664037907790842958725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638218717210387790611633 5728664037907790842958725)
                  ·
                    refine ⟨1074124507107710783054761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728664037907790842958725 1074124507107710783054761)
                    ·
                      rfl

theorem cell22_3137775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_3137775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137775 prefixEnd_3137775 := by exact prefixLift 3137775
  have htrace : WordTrace (prefixWord ++ tailWord_3137775) baseStart_3137775 baseEnd_3137775 := by
    simpa [prefixWord, tailWord_3137775, baseEnd_3137775] using wordTrace_append hprefix tailTrace_3137775
  have hstable : (prefixWord ++ tailWord_3137775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137775).length < 2 ^ (prefixWord ++ tailWord_3137775).sum := by decide
  have hdescent : baseEnd_3137775 < baseStart_3137775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137794 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3137794 : Nat := 118140960795 + 3137794 * 2 ^ 59
def prefixEnd_3137794 : Nat := 4983230072969 + 3 ^ 40 * 3137794 * 2
def baseEnd_3137794 : Nat := 1074131011196001066829703

theorem tailTrace_3137794 : CollatzResearch.WordTrace tailWord_3137794 prefixEnd_3137794 1074131011196001066829703 := by
  unfold tailWord_3137794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28611187298578926348931109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76296499462877136930482957 28611187298578926348931109)
  ·
    refine ⟨5364597618483548690424583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28611187298578926348931109 5364597618483548690424583)
    ·
      refine ⟨8046896427725323035636875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364597618483548690424583 8046896427725323035636875)
      ·
        refine ⟨12070344641587984553455313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8046896427725323035636875 12070344641587984553455313)
        ·
          refine ⟨9052758481190988415091485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12070344641587984553455313 9052758481190988415091485)
          ·
            refine ⟨3394784430446620655659307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9052758481190988415091485 3394784430446620655659307)
            ·
              refine ⟨5092176645669930983488961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394784430446620655659307 5092176645669930983488961)
              ·
                refine ⟨3819132484252448237616721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092176645669930983488961 3819132484252448237616721)
                ·
                  refine ⟨2864349363189336178212541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819132484252448237616721 2864349363189336178212541)
                  ·
                    refine ⟨1074131011196001066829703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864349363189336178212541 1074131011196001066829703)
                    ·
                      rfl

theorem cell22_3137794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3137794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137794 prefixEnd_3137794 := by exact prefixLift 3137794
  have htrace : WordTrace (prefixWord ++ tailWord_3137794) baseStart_3137794 baseEnd_3137794 := by
    simpa [prefixWord, tailWord_3137794, baseEnd_3137794] using wordTrace_append hprefix tailTrace_3137794
  have hstable : (prefixWord ++ tailWord_3137794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137794).length < 2 ^ (prefixWord ++ tailWord_3137794).sum := by decide
  have hdescent : baseEnd_3137794 < baseStart_3137794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137895 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3137895 : Nat := 118140960795 + 3137895 * 2 ^ 59
def prefixEnd_3137895 : Nat := 4983230072969 + 3 ^ 40 * 3137895 * 2
def baseEnd_3137895 : Nat := 1074165585560070470054393

theorem tailTrace_3137895 : CollatzResearch.WordTrace tailWord_3137895 prefixEnd_3137895 1074165585560070470054393 := by
  unfold tailWord_3137895
  simp only [CollatzResearch.WordTrace]
  refine ⟨114448432966949799645151139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76298955311299866430100759 114448432966949799645151139)
  ·
    refine ⟨171672649450424699467726709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114448432966949799645151139 171672649450424699467726709)
    ·
      refine ⟨16094310885977315575099379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171672649450424699467726709 16094310885977315575099379)
      ·
        refine ⟨24141466328965973362649069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16094310885977315575099379 24141466328965973362649069)
        ·
          refine ⟨9053049873362240010993401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24141466328965973362649069 9053049873362240010993401)
          ·
            refine ⟨6789787405021680008245051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9053049873362240010993401 6789787405021680008245051)
            ·
              refine ⟨10184681107532520012367577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789787405021680008245051 10184681107532520012367577)
              ·
                refine ⟨7638510830649390009275683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10184681107532520012367577 7638510830649390009275683)
                ·
                  refine ⟨11457766245974085013913525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7638510830649390009275683 11457766245974085013913525)
                  ·
                    refine ⟨1074165585560070470054393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11457766245974085013913525 1074165585560070470054393)
                    ·
                      rfl

theorem cell22_3137895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3137895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3137895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3137895 prefixEnd_3137895 := by exact prefixLift 3137895
  have htrace : WordTrace (prefixWord ++ tailWord_3137895) baseStart_3137895 baseEnd_3137895 := by
    simpa [prefixWord, tailWord_3137895, baseEnd_3137895] using wordTrace_append hprefix tailTrace_3137895
  have hstable : (prefixWord ++ tailWord_3137895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137895).length < 2 ^ (prefixWord ++ tailWord_3137895).sum := by decide
  have hdescent : baseEnd_3137895 < baseStart_3137895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138045 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3138045 : Nat := 118140960795 + 3138045 * 2 ^ 59
def prefixEnd_3138045 : Nat := 4983230072969 + 3 ^ 40 * 3138045 * 2
def baseEnd_3138045 : Nat := 1074216933625520078803933

theorem tailTrace_3138045 : CollatzResearch.WordTrace tailWord_3138045 prefixEnd_3138045 1074216933625520078803933 := by
  unfold tailWord_3138045
  simp only [CollatzResearch.WordTrace]
  refine ⟨114453903916406375263111589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76302602610937583508741059 114453903916406375263111589)
  ·
    refine ⟨21460106984326195361833423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114453903916406375263111589 21460106984326195361833423)
    ·
      refine ⟨32190160476489293042750135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460106984326195361833423 32190160476489293042750135)
      ·
        refine ⟨48285240714733939564125203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32190160476489293042750135 48285240714733939564125203)
        ·
          refine ⟨72427861072100909346187805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48285240714733939564125203 72427861072100909346187805)
          ·
            refine ⟨27160447902037841004820427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72427861072100909346187805 27160447902037841004820427)
            ·
              refine ⟨40740671853056761507230641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27160447902037841004820427 40740671853056761507230641)
              ·
                refine ⟨30555503889792571130422981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40740671853056761507230641 30555503889792571130422981)
                ·
                  refine ⟨5729156979336107086954309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30555503889792571130422981 5729156979336107086954309)
                  ·
                    refine ⟨1074216933625520078803933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729156979336107086954309 1074216933625520078803933)
                    ·
                      rfl

theorem cell22_3138045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3138045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138045 prefixEnd_3138045 := by exact prefixLift 3138045
  have htrace : WordTrace (prefixWord ++ tailWord_3138045) baseStart_3138045 baseEnd_3138045 := by
    simpa [prefixWord, tailWord_3138045, baseEnd_3138045] using wordTrace_append hprefix tailTrace_3138045
  have hstable : (prefixWord ++ tailWord_3138045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138045).length < 2 ^ (prefixWord ++ tailWord_3138045).sum := by decide
  have hdescent : baseEnd_3138045 < baseStart_3138045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138047 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 2, 3]
def baseStart_3138047 : Nat := 118140960795 + 3138047 * 2 ^ 59
def prefixEnd_3138047 : Nat := 4983230072969 + 3 ^ 40 * 3138047 * 2
def baseEnd_3138047 : Nat := 1074217618266392740253927

theorem tailTrace_3138047 : CollatzResearch.WordTrace tailWord_3138047 prefixEnd_3138047 1074217618266392740253927 := by
  unfold tailWord_3138047
  simp only [CollatzResearch.WordTrace]
  refine ⟨114453976862399129604684395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76302651241599419736456263 114453976862399129604684395)
  ·
    refine ⟨171680965293598694407026593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114453976862399129604684395 171680965293598694407026593)
    ·
      refine ⟨128760723970199020805269945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171680965293598694407026593 128760723970199020805269945)
      ·
        refine ⟨96570542977649265603952459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128760723970199020805269945 96570542977649265603952459)
        ·
          refine ⟨144855814466473898405928689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96570542977649265603952459 144855814466473898405928689)
          ·
            refine ⟨108641860849855423804446517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144855814466473898405928689 108641860849855423804446517)
            ·
              refine ⟨10185174454673945981666861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108641860849855423804446517 10185174454673945981666861)
              ·
                refine ⟨3819440420502729743125073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10185174454673945981666861 3819440420502729743125073)
                ·
                  refine ⟨2864580315377047307343805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819440420502729743125073 2864580315377047307343805)
                  ·
                    refine ⟨1074217618266392740253927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864580315377047307343805 1074217618266392740253927)
                    ·
                      rfl

theorem cell22_3138047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_3138047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138047 prefixEnd_3138047 := by exact prefixLift 3138047
  have htrace : WordTrace (prefixWord ++ tailWord_3138047) baseStart_3138047 baseEnd_3138047 := by
    simpa [prefixWord, tailWord_3138047, baseEnd_3138047] using wordTrace_append hprefix tailTrace_3138047
  have hstable : (prefixWord ++ tailWord_3138047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138047).length < 2 ^ (prefixWord ++ tailWord_3138047).sum := by decide
  have hdescent : baseEnd_3138047 < baseStart_3138047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138060 : List Nat := [2, 2, 1, 2, 4, 1, 2, 8]
def baseStart_3138060 : Nat := 118140960795 + 3138060 * 2 ^ 59
def prefixEnd_3138060 : Nat := 4983230072969 + 3 ^ 40 * 3138060 * 2
def baseEnd_3138060 : Nat := 119358007603562782186543

theorem tailTrace_3138060 : CollatzResearch.WordTrace tailWord_3138060 prefixEnd_3138060 119358007603562782186543 := by
  unfold tailWord_3138060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57227225505676016412453817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76302967340901355216605089 57227225505676016412453817)
  ·
    refine ⟨42920419129257012309340363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57227225505676016412453817 42920419129257012309340363)
    ·
      refine ⟨64380628693885518464010545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42920419129257012309340363 64380628693885518464010545)
      ·
        refine ⟨48285471520414138848007909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64380628693885518464010545 48285471520414138848007909)
        ·
          refine ⟨9053525910077651034001483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48285471520414138848007909 9053525910077651034001483)
          ·
            refine ⟨13580288865116476551002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053525910077651034001483 13580288865116476551002225)
            ·
              refine ⟨10185216648837357413251669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13580288865116476551002225 10185216648837357413251669)
              ·
                refine ⟨119358007603562782186543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10185216648837357413251669 119358007603562782186543)
                ·
                  rfl

theorem cell22_3138060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_3138060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138060 prefixEnd_3138060 := by exact prefixLift 3138060
  have htrace : WordTrace (prefixWord ++ tailWord_3138060) baseStart_3138060 baseEnd_3138060 := by
    simpa [prefixWord, tailWord_3138060, baseEnd_3138060] using wordTrace_append hprefix tailTrace_3138060
  have hstable : (prefixWord ++ tailWord_3138060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138060).length < 2 ^ (prefixWord ++ tailWord_3138060).sum := by decide
  have hdescent : baseEnd_3138060 < baseStart_3138060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138062 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3138062 : Nat := 118140960795 + 3138062 * 2 ^ 59
def prefixEnd_3138062 : Nat := 4983230072969 + 3 ^ 40 * 3138062 * 2
def baseEnd_3138062 : Nat := 1074222753072937701128881

theorem tailTrace_3138062 : CollatzResearch.WordTrace tailWord_3138062 prefixEnd_3138062 1074222753072937701128881 := by
  unfold tailWord_3138062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306815494668098395810055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76303015971563191444320293 14306815494668098395810055)
  ·
    refine ⟨21460223242002147593715083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14306815494668098395810055 21460223242002147593715083)
    ·
      refine ⟨32190334863003221390572625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460223242002147593715083 32190334863003221390572625)
      ·
        refine ⟨24142751147252416042929469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32190334863003221390572625 24142751147252416042929469)
        ·
          refine ⟨9053531680219656016098551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24142751147252416042929469 9053531680219656016098551)
          ·
            refine ⟨13580297520329484024147827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053531680219656016098551 13580297520329484024147827)
            ·
              refine ⟨20370446280494226036221741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580297520329484024147827 20370446280494226036221741)
              ·
                refine ⟨7638917355185334763583153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20370446280494226036221741 7638917355185334763583153)
                ·
                  refine ⟨5729188016389001072687365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638917355185334763583153 5729188016389001072687365)
                  ·
                    refine ⟨1074222753072937701128881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729188016389001072687365 1074222753072937701128881)
                    ·
                      rfl

theorem cell22_3138062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3138062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138062 prefixEnd_3138062 := by exact prefixLift 3138062
  have htrace : WordTrace (prefixWord ++ tailWord_3138062) baseStart_3138062 baseEnd_3138062 := by
    simpa [prefixWord, tailWord_3138062, baseEnd_3138062] using wordTrace_append hprefix tailTrace_3138062
  have hstable : (prefixWord ++ tailWord_3138062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138062).length < 2 ^ (prefixWord ++ tailWord_3138062).sum := by decide
  have hdescent : baseEnd_3138062 < baseStart_3138062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138094 : List Nat := [4, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3138094 : Nat := 118140960795 + 3138094 * 2 ^ 59
def prefixEnd_3138094 : Nat := 4983230072969 + 3 ^ 40 * 3138094 * 2
def baseEnd_3138094 : Nat := 119359300814100031592087

theorem tailTrace_3138094 : CollatzResearch.WordTrace tailWord_3138094 prefixEnd_3138094 119359300814100031592087 := by
  unfold tailWord_3138094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306961386653607078955667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76303794062152571087763557 14306961386653607078955667)
  ·
    refine ⟨21460442079980410618433501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14306961386653607078955667 21460442079980410618433501)
    ·
      refine ⟨8047665779992653981912563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21460442079980410618433501 8047665779992653981912563)
      ·
        refine ⟨12071498669988980972868845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047665779992653981912563 12071498669988980972868845)
        ·
          refine ⟨4526812001245867864825817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071498669988980972868845 4526812001245867864825817)
          ·
            refine ⟨3395109000934400898619363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526812001245867864825817 3395109000934400898619363)
            ·
              refine ⟨5092663501401601347929045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395109000934400898619363 5092663501401601347929045)
              ·
                refine ⟨119359300814100031592087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5092663501401601347929045 119359300814100031592087)
                ·
                  rfl

theorem cell22_3138094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3138094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138094 prefixEnd_3138094 := by exact prefixLift 3138094
  have htrace : WordTrace (prefixWord ++ tailWord_3138094) baseStart_3138094 baseEnd_3138094 := by
    simpa [prefixWord, tailWord_3138094, baseEnd_3138094] using wordTrace_append hprefix tailTrace_3138094
  have hstable : (prefixWord ++ tailWord_3138094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138094).length < 2 ^ (prefixWord ++ tailWord_3138094).sum := by decide
  have hdescent : baseEnd_3138094 < baseStart_3138094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138109 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_3138109 : Nat := 118140960795 + 3138109 * 2 ^ 59
def prefixEnd_3138109 : Nat := 4983230072969 + 3 ^ 40 * 3138109 * 2
def baseEnd_3138109 : Nat := 1074238842133445245203737

theorem tailTrace_3138109 : CollatzResearch.WordTrace tailWord_3138109 prefixEnd_3138109 1074238842133445245203737 := by
  unfold tailWord_3138109
  simp only [CollatzResearch.WordTrace]
  refine ⟨114456238188174514193441381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76304158792116342795627587 114456238188174514193441381)
  ·
    refine ⟨21460544660282721411270259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114456238188174514193441381 21460544660282721411270259)
    ·
      refine ⟨32190816990424082116905389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460544660282721411270259 32190816990424082116905389)
      ·
        refine ⟨12071556371409030793839521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32190816990424082116905389 12071556371409030793839521)
        ·
          refine ⟨9053667278556773095379641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12071556371409030793839521 9053667278556773095379641)
          ·
            refine ⟨6790250458917579821534731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9053667278556773095379641 6790250458917579821534731)
            ·
              refine ⟨10185375688376369732302097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790250458917579821534731 10185375688376369732302097)
              ·
                refine ⟨7639031766282277299226573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10185375688376369732302097 7639031766282277299226573)
                ·
                  refine ⟨2864636912355853987209965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7639031766282277299226573 2864636912355853987209965)
                  ·
                    refine ⟨1074238842133445245203737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864636912355853987209965 1074238842133445245203737)
                    ·
                      rfl

theorem cell22_3138109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_3138109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138109 prefixEnd_3138109 := by exact prefixLift 3138109
  have htrace : WordTrace (prefixWord ++ tailWord_3138109) baseStart_3138109 baseEnd_3138109 := by
    simpa [prefixWord, tailWord_3138109, baseEnd_3138109] using wordTrace_append hprefix tailTrace_3138109
  have hstable : (prefixWord ++ tailWord_3138109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138109).length < 2 ^ (prefixWord ++ tailWord_3138109).sum := by decide
  have hdescent : baseEnd_3138109 < baseStart_3138109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138169 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_3138169 : Nat := 118140960795 + 3138169 * 2 ^ 59
def prefixEnd_3138169 : Nat := 4983230072969 + 3 ^ 40 * 3138169 * 2
def baseEnd_3138169 : Nat := 1074259381359625088703553

theorem tailTrace_3138169 : CollatzResearch.WordTrace tailWord_3138169 prefixEnd_3138169 1074259381359625088703553 := by
  unfold tailWord_3138169
  simp only [CollatzResearch.WordTrace]
  refine ⟨114458426567957144440625561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76305617711971429627083707 114458426567957144440625561)
  ·
    refine ⟨85843819925967858330469171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114458426567957144440625561 85843819925967858330469171)
    ·
      refine ⟨128765729888951787495703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85843819925967858330469171 128765729888951787495703757)
      ·
        refine ⟨48287148708356920310888909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128765729888951787495703757 48287148708356920310888909)
        ·
          refine ⟨18107680765633845116583341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48287148708356920310888909 18107680765633845116583341)
          ·
            refine ⟨6790380287112691918718753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18107680765633845116583341 6790380287112691918718753)
            ·
              refine ⟨5092785215334518939039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790380287112691918718753 5092785215334518939039065)
              ·
                refine ⟨3819588911500889204279299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092785215334518939039065 3819588911500889204279299)
                ·
                  refine ⟨5729383367251333806418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819588911500889204279299 5729383367251333806418949)
                  ·
                    refine ⟨1074259381359625088703553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729383367251333806418949 1074259381359625088703553)
                    ·
                      rfl

theorem cell22_3138169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_3138169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138169 prefixEnd_3138169 := by exact prefixLift 3138169
  have htrace : WordTrace (prefixWord ++ tailWord_3138169) baseStart_3138169 baseEnd_3138169 := by
    simpa [prefixWord, tailWord_3138169, baseEnd_3138169] using wordTrace_append hprefix tailTrace_3138169
  have hstable : (prefixWord ++ tailWord_3138169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138169).length < 2 ^ (prefixWord ++ tailWord_3138169).sum := by decide
  have hdescent : baseEnd_3138169 < baseStart_3138169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138199 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 2, 3]
def baseStart_3138199 : Nat := 118140960795 + 3138199 * 2 ^ 59
def prefixEnd_3138199 : Nat := 4983230072969 + 3 ^ 40 * 3138199 * 2
def baseEnd_3138199 : Nat := 1074269650972715010453461

theorem tailTrace_3138199 : CollatzResearch.WordTrace tailWord_3138199 prefixEnd_3138199 1074269650972715010453461 := by
  unfold tailWord_3138199
  simp only [CollatzResearch.WordTrace]
  refine ⟨114459520757848459564217651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76306347171898973042811767 114459520757848459564217651)
  ·
    refine ⟨171689281136772689346326477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114459520757848459564217651 171689281136772689346326477)
    ·
      refine ⟨64383480426289758504872429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171689281136772689346326477 64383480426289758504872429)
      ·
        refine ⟨24143805159858659439327161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64383480426289758504872429 24143805159858659439327161)
        ·
          refine ⟨18107853869893994579495371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24143805159858659439327161 18107853869893994579495371)
          ·
            refine ⟨27161780804840991869243057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107853869893994579495371 27161780804840991869243057)
            ·
              refine ⟨20371335603630743901932293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27161780804840991869243057 20371335603630743901932293)
              ·
                refine ⟨3819625425680764481612305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20371335603630743901932293 3819625425680764481612305)
                ·
                  refine ⟨2864719069260573361209229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819625425680764481612305 2864719069260573361209229)
                  ·
                    refine ⟨1074269650972715010453461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864719069260573361209229 1074269650972715010453461)
                    ·
                      rfl

theorem cell22_3138199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_3138199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138199 prefixEnd_3138199 := by exact prefixLift 3138199
  have htrace : WordTrace (prefixWord ++ tailWord_3138199) baseStart_3138199 baseEnd_3138199 := by
    simpa [prefixWord, tailWord_3138199, baseEnd_3138199] using wordTrace_append hprefix tailTrace_3138199
  have hstable : (prefixWord ++ tailWord_3138199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138199).length < 2 ^ (prefixWord ++ tailWord_3138199).sum := by decide
  have hdescent : baseEnd_3138199 < baseStart_3138199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138212 : List Nat := [2, 3, 1, 2, 2, 1, 4, 7]
def baseStart_3138212 : Nat := 118140960795 + 3138212 * 2 ^ 59
def prefixEnd_3138212 : Nat := 4983230072969 + 3 ^ 40 * 3138212 * 2
def baseEnd_3138212 : Nat := 119363789015376367764269

theorem tailTrace_3138212 : CollatzResearch.WordTrace tailWord_3138212 prefixEnd_3138212 119363789015376367764269 := by
  unfold tailWord_3138212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57229997453400681392220445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76306663271200908522960593 57229997453400681392220445)
  ·
    refine ⟨21461249045025255522082667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57229997453400681392220445 21461249045025255522082667)
    ·
      refine ⟨32191873567537883283124001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461249045025255522082667 32191873567537883283124001)
      ·
        refine ⟨24143905175653412462343001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32191873567537883283124001 24143905175653412462343001)
        ·
          refine ⟨18107928881740059346757251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24143905175653412462343001 18107928881740059346757251)
          ·
            refine ⟨27161893322610089020135877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107928881740059346757251 27161893322610089020135877)
            ·
              refine ⟨5092854997989391691275477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27161893322610089020135877 5092854997989391691275477)
              ·
                refine ⟨119363789015376367764269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5092854997989391691275477 119363789015376367764269)
                ·
                  rfl

theorem cell22_3138212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_3138212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138212 prefixEnd_3138212 := by exact prefixLift 3138212
  have htrace : WordTrace (prefixWord ++ tailWord_3138212) baseStart_3138212 baseEnd_3138212 := by
    simpa [prefixWord, tailWord_3138212, baseEnd_3138212] using wordTrace_append hprefix tailTrace_3138212
  have hstable : (prefixWord ++ tailWord_3138212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138212).length < 2 ^ (prefixWord ++ tailWord_3138212).sum := by decide
  have hdescent : baseEnd_3138212 < baseStart_3138212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138246 : List Nat := [6, 1, 2, 1, 2, 10]
def baseStart_3138246 : Nat := 118140960795 + 3138246 * 2 ^ 59
def prefixEnd_3138246 : Nat := 4983230072969 + 3 ^ 40 * 3138246 * 2
def baseEnd_3138246 : Nat := 13262786913990401907757

theorem tailTrace_3138246 : CollatzResearch.WordTrace tailWord_3138246 prefixEnd_3138246 13262786913990401907757 := by
  unfold tailWord_3138246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576913593396193330974331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76307489992452124394119061 3576913593396193330974331)
  ·
    refine ⟨5365370390094289996461497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3576913593396193330974331 5365370390094289996461497)
    ·
      refine ⟨4024027792570717497346123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5365370390094289996461497 4024027792570717497346123)
      ·
        refine ⟨6036041688856076246019185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024027792570717497346123 6036041688856076246019185)
        ·
          refine ⟨4527031266642057184514389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6036041688856076246019185 4527031266642057184514389)
          ·
            refine ⟨13262786913990401907757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4527031266642057184514389 13262786913990401907757)
            ·
              rfl

theorem cell22_3138246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 10].length) (baseStart_3138246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138246 prefixEnd_3138246 := by exact prefixLift 3138246
  have htrace : WordTrace (prefixWord ++ tailWord_3138246) baseStart_3138246 baseEnd_3138246 := by
    simpa [prefixWord, tailWord_3138246, baseEnd_3138246] using wordTrace_append hprefix tailTrace_3138246
  have hstable : (prefixWord ++ tailWord_3138246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138246).length < 2 ^ (prefixWord ++ tailWord_3138246).sum := by decide
  have hdescent : baseEnd_3138246 < baseStart_3138246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138319 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 4]
def baseStart_3138319 : Nat := 118140960795 + 3138319 * 2 ^ 59
def prefixEnd_3138319 : Nat := 4983230072969 + 3 ^ 40 * 3138319 * 2
def baseEnd_3138319 : Nat := 358103576475024899151031

theorem tailTrace_3138319 : CollatzResearch.WordTrace tailWord_3138319 prefixEnd_3138319 358103576475024899151031 := by
  unfold tailWord_3138319
  simp only [CollatzResearch.WordTrace]
  refine ⟨114463897517413720058586011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76309265011609146705724007 114463897517413720058586011)
  ·
    refine ⟨171695846276120580087879017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114463897517413720058586011 171695846276120580087879017)
    ·
      refine ⟨128771884707090435065909263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171695846276120580087879017 128771884707090435065909263)
      ·
        refine ⟨193157827060635652598863895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128771884707090435065909263 193157827060635652598863895)
        ·
          refine ⟨289736740590953478898295843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193157827060635652598863895 289736740590953478898295843)
          ·
            refine ⟨434605110886430218347443765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289736740590953478898295843 434605110886430218347443765)
            ·
              refine ⟨40744229145602832970072853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 434605110886430218347443765 40744229145602832970072853)
              ·
                refine ⟨1909885741200132795472165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40744229145602832970072853 1909885741200132795472165)
                ·
                  refine ⟨358103576475024899151031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909885741200132795472165 358103576475024899151031)
                  ·
                    rfl

theorem cell22_3138319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 4].length) (baseStart_3138319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138319 prefixEnd_3138319 := by exact prefixLift 3138319
  have htrace : WordTrace (prefixWord ++ tailWord_3138319) baseStart_3138319 baseEnd_3138319 := by
    simpa [prefixWord, tailWord_3138319, baseEnd_3138319] using wordTrace_append hprefix tailTrace_3138319
  have hstable : (prefixWord ++ tailWord_3138319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138319).length < 2 ^ (prefixWord ++ tailWord_3138319).sum := by decide
  have hdescent : baseEnd_3138319 < baseStart_3138319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138385 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_3138385 : Nat := 118140960795 + 3138385 * 2 ^ 59
def prefixEnd_3138385 : Nat := 4983230072969 + 3 ^ 40 * 3138385 * 2
def baseEnd_3138385 : Nat := 1074333322573872525302891

theorem tailTrace_3138385 : CollatzResearch.WordTrace tailWord_3138385 prefixEnd_3138385 1074333322573872525302891 := by
  unfold tailWord_3138385
  simp only [CollatzResearch.WordTrace]
  refine ⟨114466304735174613330488609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76310869823449742220325739 114466304735174613330488609)
  ·
    refine ⟨85849728551380959997866457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114466304735174613330488609 85849728551380959997866457)
    ·
      refine ⟨64387296413535719998399843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85849728551380959997866457 64387296413535719998399843)
      ·
        refine ⟨96580944620303579997599765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64387296413535719998399843 96580944620303579997599765)
        ·
          refine ⟨4527231779076730312387489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96580944620303579997599765 4527231779076730312387489)
          ·
            refine ⟨3395423834307547734290617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527231779076730312387489 3395423834307547734290617)
            ·
              refine ⟨2546567875730660800717963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395423834307547734290617 2546567875730660800717963)
              ·
                refine ⟨3819851813595991201076945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546567875730660800717963 3819851813595991201076945)
                ·
                  refine ⟨2864888860196993400807709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819851813595991201076945 2864888860196993400807709)
                  ·
                    refine ⟨1074333322573872525302891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864888860196993400807709 1074333322573872525302891)
                    ·
                      rfl

theorem cell22_3138385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_3138385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138385 prefixEnd_3138385 := by exact prefixLift 3138385
  have htrace : WordTrace (prefixWord ++ tailWord_3138385) baseStart_3138385 baseEnd_3138385 := by
    simpa [prefixWord, tailWord_3138385, baseEnd_3138385] using wordTrace_append hprefix tailTrace_3138385
  have hstable : (prefixWord ++ tailWord_3138385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138385).length < 2 ^ (prefixWord ++ tailWord_3138385).sum := by decide
  have hdescent : baseEnd_3138385 < baseStart_3138385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138413 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3138413 : Nat := 118140960795 + 3138413 * 2 ^ 59
def prefixEnd_3138413 : Nat := 4983230072969 + 3 ^ 40 * 3138413 * 2
def baseEnd_3138413 : Nat := 1074342907546089785602805

theorem tailTrace_3138413 : CollatzResearch.WordTrace tailWord_3138413 prefixEnd_3138413 1074342907546089785602805 := by
  unfold tailWord_3138413
  simp only [CollatzResearch.WordTrace]
  refine ⟨114467325979073174112507893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76311550652715449408338595 114467325979073174112507893)
  ·
    refine ⟨10731311810538110073047615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114467325979073174112507893 10731311810538110073047615)
    ·
      refine ⟨16096967715807165109571423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10731311810538110073047615 16096967715807165109571423)
      ·
        refine ⟨24145451573710747664357135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16096967715807165109571423 24145451573710747664357135)
        ·
          refine ⟨36218177360566121496535703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24145451573710747664357135 36218177360566121496535703)
          ·
            refine ⟨54327266040849182244803555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36218177360566121496535703 54327266040849182244803555)
            ·
              refine ⟨81490899061273773367205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54327266040849182244803555 81490899061273773367205333)
              ·
                refine ⟨1909942946748604063293875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81490899061273773367205333 1909942946748604063293875)
                ·
                  refine ⟨2864914420122906094940813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909942946748604063293875 2864914420122906094940813)
                  ·
                    refine ⟨1074342907546089785602805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864914420122906094940813 1074342907546089785602805)
                    ·
                      rfl

theorem cell22_3138413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3138413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138413 prefixEnd_3138413 := by exact prefixLift 3138413
  have htrace : WordTrace (prefixWord ++ tailWord_3138413) baseStart_3138413 baseEnd_3138413 := by
    simpa [prefixWord, tailWord_3138413, baseEnd_3138413] using wordTrace_append hprefix tailTrace_3138413
  have hstable : (prefixWord ++ tailWord_3138413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138413).length < 2 ^ (prefixWord ++ tailWord_3138413).sum := by decide
  have hdescent : baseEnd_3138413 < baseStart_3138413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138477 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3138477 : Nat := 118140960795 + 3138477 * 2 ^ 59
def prefixEnd_3138477 : Nat := 4983230072969 + 3 ^ 40 * 3138477 * 2
def baseEnd_3138477 : Nat := 358121605351338317334203

theorem tailTrace_3138477 : CollatzResearch.WordTrace tailWord_3138477 prefixEnd_3138477 358121605351338317334203 := by
  unfold tailWord_3138477
  simp only [CollatzResearch.WordTrace]
  refine ⟨114469660250841313042837685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76313106833894208695225123 114469660250841313042837685)
  ·
    refine ⟨10731530648516373097766033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114469660250841313042837685 10731530648516373097766033)
    ·
      refine ⟨8048647986387279823324525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10731530648516373097766033 8048647986387279823324525)
      ·
        refine ⟨3018242994895229933746697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8048647986387279823324525 3018242994895229933746697)
        ·
          refine ⟨2263682246171422450310023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018242994895229933746697 2263682246171422450310023)
          ·
            refine ⟨3395523369257133675465035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263682246171422450310023 3395523369257133675465035)
            ·
              refine ⟨5093285053885700513197553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395523369257133675465035 5093285053885700513197553)
              ·
                refine ⟨3819963790414275384898165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093285053885700513197553 3819963790414275384898165)
                ·
                  refine ⟨358121605351338317334203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3819963790414275384898165 358121605351338317334203)
                  ·
                    rfl

theorem cell22_3138477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3138477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138477 prefixEnd_3138477 := by exact prefixLift 3138477
  have htrace : WordTrace (prefixWord ++ tailWord_3138477) baseStart_3138477 baseEnd_3138477 := by
    simpa [prefixWord, tailWord_3138477, baseEnd_3138477] using wordTrace_append hprefix tailTrace_3138477
  have hstable : (prefixWord ++ tailWord_3138477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138477).length < 2 ^ (prefixWord ++ tailWord_3138477).sum := by decide
  have hdescent : baseEnd_3138477 < baseStart_3138477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138516 : List Nat := [2, 4, 1, 2, 1, 3, 1, 8]
def baseStart_3138516 : Nat := 118140960795 + 3138516 * 2 ^ 59
def prefixEnd_3138516 : Nat := 4983230072969 + 3 ^ 40 * 3138516 * 2
def baseEnd_3138516 : Nat := 119375351839003538919721

theorem tailTrace_3138516 : CollatzResearch.WordTrace tailWord_3138516 prefixEnd_3138516 119375351839003538919721 := by
  unfold tailWord_3138516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57235541348850011351753701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76314055131800015135671601 57235541348850011351753701)
  ·
    refine ⟨10731664002909377128453819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57235541348850011351753701 10731664002909377128453819)
    ·
      refine ⟨16097496004364065692680729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10731664002909377128453819 16097496004364065692680729)
      ·
        refine ⟨12073122003273049269510547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16097496004364065692680729 12073122003273049269510547)
        ·
          refine ⟨18109683004909573904265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12073122003273049269510547 18109683004909573904265821)
          ·
            refine ⟨6791131126841090214099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18109683004909573904265821 6791131126841090214099683)
            ·
              refine ⟨10186696690261635321149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791131126841090214099683 10186696690261635321149525)
              ·
                refine ⟨119375351839003538919721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10186696690261635321149525 119375351839003538919721)
                ·
                  rfl

theorem cell22_3138516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_3138516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138516 prefixEnd_3138516 := by exact prefixLift 3138516
  have htrace : WordTrace (prefixWord ++ tailWord_3138516) baseStart_3138516 baseEnd_3138516 := by
    simpa [prefixWord, tailWord_3138516, baseEnd_3138516] using wordTrace_append hprefix tailTrace_3138516
  have hstable : (prefixWord ++ tailWord_3138516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138516).length < 2 ^ (prefixWord ++ tailWord_3138516).sum := by decide
  have hdescent : baseEnd_3138516 < baseStart_3138516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138518 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3138518 : Nat := 118140960795 + 3138518 * 2 ^ 59
def prefixEnd_3138518 : Nat := 4983230072969 + 3 ^ 40 * 3138518 * 2
def baseEnd_3138518 : Nat := 1074378851191904511727483

theorem tailTrace_3138518 : CollatzResearch.WordTrace tailWord_3138518 prefixEnd_3138518 1074378851191904511727483 := by
  unfold tailWord_3138518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154447227730798565317513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76314103762461851363386805 7154447227730798565317513)
  ·
    refine ⟨5365835420798098923988135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7154447227730798565317513 5365835420798098923988135)
    ·
      refine ⟨8048753131197148385982203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365835420798098923988135 8048753131197148385982203)
      ·
        refine ⟨12073129696795722578973305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8048753131197148385982203 12073129696795722578973305)
        ·
          refine ⟨9054847272596791934229979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12073129696795722578973305 9054847272596791934229979)
          ·
            refine ⟨13582270908895187901344969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054847272596791934229979 13582270908895187901344969)
            ·
              refine ⟨10186703181671390926008727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13582270908895187901344969 10186703181671390926008727)
              ·
                refine ⟨15280054772507086389013091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186703181671390926008727 15280054772507086389013091)
                ·
                  refine ⟨22920082158760629583519637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15280054772507086389013091 22920082158760629583519637)
                  ·
                    refine ⟨1074378851191904511727483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22920082158760629583519637 1074378851191904511727483)
                    ·
                      rfl

theorem cell22_3138518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3138518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138518 prefixEnd_3138518 := by exact prefixLift 3138518
  have htrace : WordTrace (prefixWord ++ tailWord_3138518) baseStart_3138518 baseEnd_3138518 := by
    simpa [prefixWord, tailWord_3138518, baseEnd_3138518] using wordTrace_append hprefix tailTrace_3138518
  have hstable : (prefixWord ++ tailWord_3138518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138518).length < 2 ^ (prefixWord ++ tailWord_3138518).sum := by decide
  have hdescent : baseEnd_3138518 < baseStart_3138518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138529 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3138529 : Nat := 118140960795 + 3138529 * 2 ^ 59
def prefixEnd_3138529 : Nat := 4983230072969 + 3 ^ 40 * 3138529 * 2
def baseEnd_3138529 : Nat := 1074382616716704149702449

theorem tailTrace_3138529 : CollatzResearch.WordTrace tailWord_3138529 prefixEnd_3138529 1074382616716704149702449 := by
  unfold tailWord_3138529
  simp only [CollatzResearch.WordTrace]
  refine ⟨114471556846652925923730641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76314371231101950615820427 114471556846652925923730641)
  ·
    refine ⟨85853667634989694442797981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114471556846652925923730641 85853667634989694442797981)
    ·
      refine ⟨32195125363121135416049243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85853667634989694442797981 32195125363121135416049243)
      ·
        refine ⟨48292688044681703124073865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32195125363121135416049243 48292688044681703124073865)
        ·
          refine ⟨36219516033511277343055399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48292688044681703124073865 36219516033511277343055399)
          ·
            refine ⟨54329274050266916014583099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36219516033511277343055399 54329274050266916014583099)
            ·
              refine ⟨81493911075400374021874649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54329274050266916014583099 81493911075400374021874649)
              ·
                refine ⟨61120433306550280516405987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81493911075400374021874649 61120433306550280516405987)
                ·
                  refine ⟨91680649959825420774608981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61120433306550280516405987 91680649959825420774608981)
                  ·
                    refine ⟨1074382616716704149702449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91680649959825420774608981 1074382616716704149702449)
                    ·
                      rfl

theorem cell22_3138529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3138529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138529 prefixEnd_3138529 := by exact prefixLift 3138529
  have htrace : WordTrace (prefixWord ++ tailWord_3138529) baseStart_3138529 baseEnd_3138529 := by
    simpa [prefixWord, tailWord_3138529, baseEnd_3138529] using wordTrace_append hprefix tailTrace_3138529
  have hstable : (prefixWord ++ tailWord_3138529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138529).length < 2 ^ (prefixWord ++ tailWord_3138529).sum := by decide
  have hdescent : baseEnd_3138529 < baseStart_3138529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138533 : List Nat := [1, 3, 1, 6, 1, 2, 8]
def baseStart_3138533 : Nat := 118140960795 + 3138533 * 2 ^ 59
def prefixEnd_3138533 : Nat := 4983230072969 + 3 ^ 40 * 3138533 * 2
def baseEnd_3138533 : Nat := 39791999481424054540831

theorem tailTrace_3138533 : CollatzResearch.WordTrace tailWord_3138533 prefixEnd_3138533 39791999481424054540831 := by
  unfold tailWord_3138533
  simp only [CollatzResearch.WordTrace]
  refine ⟨114471702738638434606876253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76314468492425623071250835 114471702738638434606876253)
  ·
    refine ⟨42926888526989412977578595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114471702738638434606876253 42926888526989412977578595)
    ·
      refine ⟨64390332790484119466367893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42926888526989412977578595 64390332790484119466367893)
      ·
        refine ⟨3018296849553943099985995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64390332790484119466367893 3018296849553943099985995)
        ·
          refine ⟨4527445274330914649978993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018296849553943099985995 4527445274330914649978993)
          ·
            refine ⟨3395583955748185987484245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527445274330914649978993 3395583955748185987484245)
            ·
              refine ⟨39791999481424054540831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3395583955748185987484245 39791999481424054540831)
              ·
                rfl

theorem cell22_3138533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 8].length) (baseStart_3138533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138533 prefixEnd_3138533 := by exact prefixLift 3138533
  have htrace : WordTrace (prefixWord ++ tailWord_3138533) baseStart_3138533 baseEnd_3138533 := by
    simpa [prefixWord, tailWord_3138533, baseEnd_3138533] using wordTrace_append hprefix tailTrace_3138533
  have hstable : (prefixWord ++ tailWord_3138533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138533).length < 2 ^ (prefixWord ++ tailWord_3138533).sum := by decide
  have hdescent : baseEnd_3138533 < baseStart_3138533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138599 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3138599 : Nat := 118140960795 + 3138599 * 2 ^ 59
def prefixEnd_3138599 : Nat := 4983230072969 + 3 ^ 40 * 3138599 * 2
def baseEnd_3138599 : Nat := 1074406579147247300452235

theorem tailTrace_3138599 : CollatzResearch.WordTrace tailWord_3138599 prefixEnd_3138599 1074406579147247300452235 := by
  unfold tailWord_3138599
  simp only [CollatzResearch.WordTrace]
  refine ⟨114474109956399327878778851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76316073304266218585852567 114474109956399327878778851)
  ·
    refine ⟨171711164934598991818168277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114474109956399327878778851 171711164934598991818168277)
    ·
      refine ⟨4024480428154663870738319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171711164934598991818168277 4024480428154663870738319)
      ·
        refine ⟨6036720642231995806107479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024480428154663870738319 6036720642231995806107479)
        ·
          refine ⟨9055080963347993709161219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036720642231995806107479 9055080963347993709161219)
          ·
            refine ⟨13582621445021990563741829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055080963347993709161219 13582621445021990563741829)
            ·
              refine ⟨2546741520941623230701593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13582621445021990563741829 2546741520941623230701593)
              ·
                refine ⟨1910056140706217423026195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546741520941623230701593 1910056140706217423026195)
                ·
                  refine ⟨2865084211059326134539293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910056140706217423026195 2865084211059326134539293)
                  ·
                    refine ⟨1074406579147247300452235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865084211059326134539293 1074406579147247300452235)
                    ·
                      rfl

theorem cell22_3138599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3138599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138599 prefixEnd_3138599 := by exact prefixLift 3138599
  have htrace : WordTrace (prefixWord ++ tailWord_3138599) baseStart_3138599 baseEnd_3138599 := by
    simpa [prefixWord, tailWord_3138599, baseEnd_3138599] using wordTrace_append hprefix tailTrace_3138599
  have hstable : (prefixWord ++ tailWord_3138599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138599).length < 2 ^ (prefixWord ++ tailWord_3138599).sum := by decide
  have hdescent : baseEnd_3138599 < baseStart_3138599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138638 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3138638 : Nat := 118140960795 + 3138638 * 2 ^ 59
def prefixEnd_3138638 : Nat := 4983230072969 + 3 ^ 40 * 3138638 * 2
def baseEnd_3138638 : Nat := 1074419929644264198727115

theorem tailTrace_3138638 : CollatzResearch.WordTrace tailWord_3138638 prefixEnd_3138638 1074419929644264198727115 := by
  unfold tailWord_3138638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309441550407254692431071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76317021602172025026299045 14309441550407254692431071)
  ·
    refine ⟨21464162325610882038646607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14309441550407254692431071 21464162325610882038646607)
    ·
      refine ⟨32196243488416323057969911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21464162325610882038646607 32196243488416323057969911)
      ·
        refine ⟨48294365232624484586954867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32196243488416323057969911 48294365232624484586954867)
        ·
          refine ⟨72441547848936726880432301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48294365232624484586954867 72441547848936726880432301)
          ·
            refine ⟨27165580443351272580162113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72441547848936726880432301 27165580443351272580162113)
            ·
              refine ⟨20374185332513454435121585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27165580443351272580162113 20374185332513454435121585)
              ·
                refine ⟨15280638999385090826341189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20374185332513454435121585 15280638999385090826341189)
                ·
                  refine ⟨2865119812384704529938973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15280638999385090826341189 2865119812384704529938973)
                  ·
                    refine ⟨1074419929644264198727115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865119812384704529938973 1074419929644264198727115)
                    ·
                      rfl

theorem cell22_3138638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3138638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138638 prefixEnd_3138638 := by exact prefixLift 3138638
  have htrace : WordTrace (prefixWord ++ tailWord_3138638) baseStart_3138638 baseEnd_3138638 := by
    simpa [prefixWord, tailWord_3138638, baseEnd_3138638] using wordTrace_append hprefix tailTrace_3138638
  have hstable : (prefixWord ++ tailWord_3138638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138638).length < 2 ^ (prefixWord ++ tailWord_3138638).sum := by decide
  have hdescent : baseEnd_3138638 < baseStart_3138638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138642 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3138642 : Nat := 118140960795 + 3138642 * 2 ^ 59
def prefixEnd_3138642 : Nat := 4983230072969 + 3 ^ 40 * 3138642 * 2
def baseEnd_3138642 : Nat := 1074421298926009521627103

theorem tailTrace_3138642 : CollatzResearch.WordTrace tailWord_3138642 prefixEnd_3138642 1074421298926009521627103 := by
  unfold tailWord_3138642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28618919573810886555648545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76317118863495697481729453 28618919573810886555648545)
  ·
    refine ⟨21464189680358164916736409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28618919573810886555648545 21464189680358164916736409)
    ·
      refine ⟨16098142260268623687552307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21464189680358164916736409 16098142260268623687552307)
      ·
        refine ⟨24147213390402935531328461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16098142260268623687552307 24147213390402935531328461)
        ·
          refine ⟨9055205021401100824248173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24147213390402935531328461 9055205021401100824248173)
          ·
            refine ⟨3395701883025412809093065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9055205021401100824248173 3395701883025412809093065)
            ·
              refine ⟨2546776412269059606819799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395701883025412809093065 2546776412269059606819799)
              ·
                refine ⟨3820164618403589410229699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546776412269059606819799 3820164618403589410229699)
                ·
                  refine ⟨5730246927605384115344549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820164618403589410229699 5730246927605384115344549)
                  ·
                    refine ⟨1074421298926009521627103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730246927605384115344549 1074421298926009521627103)
                    ·
                      rfl

theorem cell22_3138642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3138642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138642 prefixEnd_3138642 := by exact prefixLift 3138642
  have htrace : WordTrace (prefixWord ++ tailWord_3138642) baseStart_3138642 baseEnd_3138642 := by
    simpa [prefixWord, tailWord_3138642, baseEnd_3138642] using wordTrace_append hprefix tailTrace_3138642
  have hstable : (prefixWord ++ tailWord_3138642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138642).length < 2 ^ (prefixWord ++ tailWord_3138642).sum := by decide
  have hdescent : baseEnd_3138642 < baseStart_3138642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138743 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3138743 : Nat := 118140960795 + 3138743 * 2 ^ 59
def prefixEnd_3138743 : Nat := 4983230072969 + 3 ^ 40 * 3138743 * 2
def baseEnd_3138743 : Nat := 1074455873290078924851793

theorem tailTrace_3138743 : CollatzResearch.WordTrace tailWord_3138743 prefixEnd_3138743 1074455873290078924851793 := by
  unfold tailWord_3138743
  simp only [CollatzResearch.WordTrace]
  refine ⟨114479362067877640472020883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76319574711918426981347255 114479362067877640472020883)
  ·
    refine ⟨171719043101816460708031325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114479362067877640472020883 171719043101816460708031325)
    ·
      refine ⟨64394641163181172765511747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171719043101816460708031325 64394641163181172765511747)
      ·
        refine ⟨96591961744771759148267621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64394641163181172765511747 96591961744771759148267621)
        ·
          refine ⟨18110992827144704840300179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96591961744771759148267621 18110992827144704840300179)
          ·
            refine ⟨27166489240717057260450269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18110992827144704840300179 27166489240717057260450269)
            ·
              refine ⟨10187433465268896472668851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27166489240717057260450269 10187433465268896472668851)
              ·
                refine ⟨15281150197903344709003277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10187433465268896472668851 15281150197903344709003277)
                ·
                  refine ⟨5730431324213754265876229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15281150197903344709003277 5730431324213754265876229)
                  ·
                    refine ⟨1074455873290078924851793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730431324213754265876229 1074455873290078924851793)
                    ·
                      rfl

theorem cell22_3138743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3138743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138743 prefixEnd_3138743 := by exact prefixLift 3138743
  have htrace : WordTrace (prefixWord ++ tailWord_3138743) baseStart_3138743 baseEnd_3138743 := by
    simpa [prefixWord, tailWord_3138743, baseEnd_3138743] using wordTrace_append hprefix tailTrace_3138743
  have hstable : (prefixWord ++ tailWord_3138743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138743).length < 2 ^ (prefixWord ++ tailWord_3138743).sum := by decide
  have hdescent : baseEnd_3138743 < baseStart_3138743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138788 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3138788 : Nat := 118140960795 + 3138788 * 2 ^ 59
def prefixEnd_3138788 : Nat := 4983230072969 + 3 ^ 40 * 3138788 * 2
def baseEnd_3138788 : Nat := 1074471277709713807476655

theorem tailTrace_3138788 : CollatzResearch.WordTrace tailWord_3138788 prefixEnd_3138788 1074471277709713807476655 := by
  unfold tailWord_3138788
  simp only [CollatzResearch.WordTrace]
  refine ⟨57240501676357306578704509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76320668901809742104939345 57240501676357306578704509)
  ·
    refine ⟨21465188128633989967014191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57240501676357306578704509 21465188128633989967014191)
    ·
      refine ⟨32197782192950984950521287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21465188128633989967014191 32197782192950984950521287)
      ·
        refine ⟨48296673289426477425781931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32197782192950984950521287 48296673289426477425781931)
        ·
          refine ⟨72445009934139716138672897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48296673289426477425781931 72445009934139716138672897)
          ·
            refine ⟨54333757450604787104004673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72445009934139716138672897 54333757450604787104004673)
            ·
              refine ⟨40750318087953590328003505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54333757450604787104004673 40750318087953590328003505)
              ·
                refine ⟨30562738565965192746002629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40750318087953590328003505 30562738565965192746002629)
                ·
                  refine ⟨5730513481118473639875493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30562738565965192746002629 5730513481118473639875493)
                  ·
                    refine ⟨1074471277709713807476655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730513481118473639875493 1074471277709713807476655)
                    ·
                      rfl

theorem cell22_3138788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3138788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138788 prefixEnd_3138788 := by exact prefixLift 3138788
  have htrace : WordTrace (prefixWord ++ tailWord_3138788) baseStart_3138788 baseEnd_3138788 := by
    simpa [prefixWord, tailWord_3138788, baseEnd_3138788] using wordTrace_append hprefix tailTrace_3138788
  have hstable : (prefixWord ++ tailWord_3138788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138788).length < 2 ^ (prefixWord ++ tailWord_3138788).sum := by decide
  have hdescent : baseEnd_3138788 < baseStart_3138788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138824 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3138824 : Nat := 118140960795 + 3138824 * 2 ^ 59
def prefixEnd_3138824 : Nat := 4983230072969 + 3 ^ 40 * 3138824 * 2
def baseEnd_3138824 : Nat := 1074483601245421713576545

theorem tailTrace_3138824 : CollatzResearch.WordTrace tailWord_3138824 prefixEnd_3138824 1074483601245421713576545 := by
  unfold tailWord_3138824
  simp only [CollatzResearch.WordTrace]
  refine ⟨57241158190292095652859763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76321544253722794203813017 57241158190292095652859763)
  ·
    refine ⟨85861737285438143479289645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57241158190292095652859763 85861737285438143479289645)
    ·
      refine ⟨32198151482039303804733617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85861737285438143479289645 32198151482039303804733617)
      ·
        refine ⟨24148613611529477853550213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32198151482039303804733617 24148613611529477853550213)
        ·
          refine ⟨4527865052161777097540665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24148613611529477853550213 4527865052161777097540665)
          ·
            refine ⟨3395898789121332823155499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527865052161777097540665 3395898789121332823155499)
            ·
              refine ⟨5093848183681999234733249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395898789121332823155499 5093848183681999234733249)
              ·
                refine ⟨3820386137761499426049937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093848183681999234733249 3820386137761499426049937)
                ·
                  refine ⟨2865289603321124569537453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3820386137761499426049937 2865289603321124569537453)
                  ·
                    refine ⟨1074483601245421713576545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865289603321124569537453 1074483601245421713576545)
                    ·
                      rfl

theorem cell22_3138824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3138824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138824 prefixEnd_3138824 := by exact prefixLift 3138824
  have htrace : WordTrace (prefixWord ++ tailWord_3138824) baseStart_3138824 baseEnd_3138824 := by
    simpa [prefixWord, tailWord_3138824, baseEnd_3138824] using wordTrace_append hprefix tailTrace_3138824
  have hstable : (prefixWord ++ tailWord_3138824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138824).length < 2 ^ (prefixWord ++ tailWord_3138824).sum := by decide
  have hdescent : baseEnd_3138824 < baseStart_3138824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138869 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_3138869 : Nat := 118140960795 + 3138869 * 2 ^ 59
def prefixEnd_3138869 : Nat := 4983230072969 + 3 ^ 40 * 3138869 * 2
def baseEnd_3138869 : Nat := 1074499005665056596201407

theorem tailTrace_3138869 : CollatzResearch.WordTrace tailWord_3138869 prefixEnd_3138869 1074499005665056596201407 := by
  unfold tailWord_3138869
  simp only [CollatzResearch.WordTrace]
  refine ⟨114483957665421163991107661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76322638443614109327405107 114483957665421163991107661)
  ·
    refine ⟨42931484124532936496665373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114483957665421163991107661 42931484124532936496665373)
    ·
      refine ⟨16099306546699851186249515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42931484124532936496665373 16099306546699851186249515)
      ·
        refine ⟨24148959820049776779374273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16099306546699851186249515 24148959820049776779374273)
        ·
          refine ⟨18111719865037332584530705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24148959820049776779374273 18111719865037332584530705)
          ·
            refine ⟨13583789898777999438398029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18111719865037332584530705 13583789898777999438398029)
            ·
              refine ⟨5093921212041749789399261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13583789898777999438398029 5093921212041749789399261)
              ·
                refine ⟨1910220454515656171024723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5093921212041749789399261 1910220454515656171024723)
                ·
                  refine ⟨2865330681773484256537085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910220454515656171024723 2865330681773484256537085)
                  ·
                    refine ⟨1074499005665056596201407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865330681773484256537085 1074499005665056596201407)
                    ·
                      rfl

theorem cell22_3138869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_3138869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138869 prefixEnd_3138869 := by exact prefixLift 3138869
  have htrace : WordTrace (prefixWord ++ tailWord_3138869) baseStart_3138869 baseEnd_3138869 := by
    simpa [prefixWord, tailWord_3138869, baseEnd_3138869] using wordTrace_append hprefix tailTrace_3138869
  have hstable : (prefixWord ++ tailWord_3138869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138869).length < 2 ^ (prefixWord ++ tailWord_3138869).sum := by decide
  have hdescent : baseEnd_3138869 < baseStart_3138869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138912 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_3138912 : Nat := 118140960795 + 3138912 * 2 ^ 59
def prefixEnd_3138912 : Nat := 4983230072969 + 3 ^ 40 * 3138912 * 2
def baseEnd_3138912 : Nat := 1074513725443818817376275

theorem tailTrace_3138912 : CollatzResearch.WordTrace tailWord_3138912 prefixEnd_3138912 1074513725443818817376275 := by
  unfold tailWord_3138912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57242763002132691167461495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76323684002843588223281993 57242763002132691167461495)
  ·
    refine ⟨85864144503199036751192243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57242763002132691167461495 85864144503199036751192243)
    ·
      refine ⟨128796216754798555126788365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85864144503199036751192243 128796216754798555126788365)
      ·
        refine ⟨48298581283049458172545637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128796216754798555126788365 48298581283049458172545637)
        ·
          refine ⟨9055983990571773407352307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48298581283049458172545637 9055983990571773407352307)
          ·
            refine ⟨13583975985857660111028461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055983990571773407352307 13583975985857660111028461)
            ·
              refine ⟨5093990994696622541635673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13583975985857660111028461 5093990994696622541635673)
              ·
                refine ⟨3820493246022466906226755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093990994696622541635673 3820493246022466906226755)
                ·
                  refine ⟨5730739869033700359340133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820493246022466906226755 5730739869033700359340133)
                  ·
                    refine ⟨1074513725443818817376275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730739869033700359340133 1074513725443818817376275)
                    ·
                      rfl

theorem cell22_3138912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_3138912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138912 prefixEnd_3138912 := by exact prefixLift 3138912
  have htrace : WordTrace (prefixWord ++ tailWord_3138912) baseStart_3138912 baseEnd_3138912 := by
    simpa [prefixWord, tailWord_3138912, baseEnd_3138912] using wordTrace_append hprefix tailTrace_3138912
  have hstable : (prefixWord ++ tailWord_3138912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138912).length < 2 ^ (prefixWord ++ tailWord_3138912).sum := by decide
  have hdescent : baseEnd_3138912 < baseStart_3138912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138925 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3138925 : Nat := 118140960795 + 3138925 * 2 ^ 59
def prefixEnd_3138925 : Nat := 4983230072969 + 3 ^ 40 * 3138925 * 2
def baseEnd_3138925 : Nat := 1074518175609491116801235

theorem tailTrace_3138925 : CollatzResearch.WordTrace tailWord_3138925 prefixEnd_3138925 1074518175609491116801235 := by
  unfold tailWord_3138925
  simp only [CollatzResearch.WordTrace]
  refine ⟨114486000153218285555146229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76324000102145523703430819 114486000153218285555146229)
  ·
    refine ⟨10733062514364214270794959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114486000153218285555146229 10733062514364214270794959)
    ·
      refine ⟨16099593771546321406192439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10733062514364214270794959 16099593771546321406192439)
      ·
        refine ⟨24149390657319482109288659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16099593771546321406192439 24149390657319482109288659)
        ·
          refine ⟨36224085985979223163932989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24149390657319482109288659 36224085985979223163932989)
          ·
            refine ⟨13584032244742208686474871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36224085985979223163932989 13584032244742208686474871)
            ·
              refine ⟨20376048367113313029712307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13584032244742208686474871 20376048367113313029712307)
              ·
                refine ⟨30564072550669969544568461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20376048367113313029712307 30564072550669969544568461)
                ·
                  refine ⟨11461527206501238579213173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30564072550669969544568461 11461527206501238579213173)
                  ·
                    refine ⟨1074518175609491116801235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11461527206501238579213173 1074518175609491116801235)
                    ·
                      rfl

theorem cell22_3138925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3138925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138925 prefixEnd_3138925 := by exact prefixLift 3138925
  have htrace : WordTrace (prefixWord ++ tailWord_3138925) baseStart_3138925 baseEnd_3138925 := by
    simpa [prefixWord, tailWord_3138925, baseEnd_3138925] using wordTrace_append hprefix tailTrace_3138925
  have hstable : (prefixWord ++ tailWord_3138925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138925).length < 2 ^ (prefixWord ++ tailWord_3138925).sum := by decide
  have hdescent : baseEnd_3138925 < baseStart_3138925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138940 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3138940 : Nat := 118140960795 + 3138940 * 2 ^ 59
def prefixEnd_3138940 : Nat := 4983230072969 + 3 ^ 40 * 3138940 * 2
def baseEnd_3138940 : Nat := 1074523310416036077676189

theorem tailTrace_3138940 : CollatzResearch.WordTrace tailWord_3138940 prefixEnd_3138940 1074523310416036077676189 := by
  unfold tailWord_3138940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57243273624081971558471137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76324364832109295411294849 57243273624081971558471137)
  ·
    refine ⟨42932455218061478668853353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57243273624081971558471137 42932455218061478668853353)
    ·
      refine ⟨32199341413546109001640015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42932455218061478668853353 32199341413546109001640015)
      ·
        refine ⟨48299012120319163502460023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32199341413546109001640015 48299012120319163502460023)
        ·
          refine ⟨72448518180478745253690035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48299012120319163502460023 72448518180478745253690035)
          ·
            refine ⟨108672777270718117880535053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72448518180478745253690035 108672777270718117880535053)
            ·
              refine ⟨40752291476519294205200645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108672777270718117880535053 40752291476519294205200645)
              ·
                refine ⟨7641054651847367663475121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40752291476519294205200645 7641054651847367663475121)
                ·
                  refine ⟨5730790988885525747606341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7641054651847367663475121 5730790988885525747606341)
                  ·
                    refine ⟨1074523310416036077676189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730790988885525747606341 1074523310416036077676189)
                    ·
                      rfl

theorem cell22_3138940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3138940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138940 prefixEnd_3138940 := by exact prefixLift 3138940
  have htrace : WordTrace (prefixWord ++ tailWord_3138940) baseStart_3138940 baseEnd_3138940 := by
    simpa [prefixWord, tailWord_3138940, baseEnd_3138940] using wordTrace_append hprefix tailTrace_3138940
  have hstable : (prefixWord ++ tailWord_3138940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138940).length < 2 ^ (prefixWord ++ tailWord_3138940).sum := by decide
  have hdescent : baseEnd_3138940 < baseStart_3138940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138974 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3138974 : Nat := 118140960795 + 3138974 * 2 ^ 59
def prefixEnd_3138974 : Nat := 4983230072969 + 3 ^ 40 * 3138974 * 2
def baseEnd_3138974 : Nat := 1074534949310871322326085

theorem tailTrace_3138974 : CollatzResearch.WordTrace tailWord_3138974 prefixEnd_3138974 1074534949310871322326085 := by
  unfold tailWord_3138974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310973416255095865459997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76325191553360511282453317 14310973416255095865459997)
  ·
    refine ⟨5366615031095660949547499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14310973416255095865459997 5366615031095660949547499)
    ·
      refine ⟨8049922546643491424321249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366615031095660949547499 8049922546643491424321249)
      ·
        refine ⟨6037441909982618568240937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8049922546643491424321249 6037441909982618568240937)
        ·
          refine ⟨4528081432486963926180703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6037441909982618568240937 4528081432486963926180703)
          ·
            refine ⟨6792122148730445889271055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528081432486963926180703 6792122148730445889271055)
            ·
              refine ⟨10188183223095668833906583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792122148730445889271055 10188183223095668833906583)
              ·
                refine ⟨15282274834643503250859875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10188183223095668833906583 15282274834643503250859875)
                ·
                  refine ⟨22923412251965254876289813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15282274834643503250859875 22923412251965254876289813)
                  ·
                    refine ⟨1074534949310871322326085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22923412251965254876289813 1074534949310871322326085)
                    ·
                      rfl

theorem cell22_3138974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3138974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3138974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3138974 prefixEnd_3138974 := by exact prefixLift 3138974
  have htrace : WordTrace (prefixWord ++ tailWord_3138974) baseStart_3138974 baseEnd_3138974 := by
    simpa [prefixWord, tailWord_3138974, baseEnd_3138974] using wordTrace_append hprefix tailTrace_3138974
  have hstable : (prefixWord ++ tailWord_3138974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138974).length < 2 ^ (prefixWord ++ tailWord_3138974).sum := by decide
  have hdescent : baseEnd_3138974 < baseStart_3138974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139010 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3139010 : Nat := 118140960795 + 3139010 * 2 ^ 59
def prefixEnd_3139010 : Nat := 4983230072969 + 3 ^ 40 * 3139010 * 2
def baseEnd_3139010 : Nat := 1074547272846579228425975

theorem tailTrace_3139010 : CollatzResearch.WordTrace tailWord_3139010 prefixEnd_3139010 1074547272846579228425975 := by
  unfold tailWord_3139010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622275089477586267997621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76326066905273563381326989 28622275089477586267997621)
  ·
    refine ⟨2683338289638523712624777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28622275089477586267997621 2683338289638523712624777)
    ·
      refine ⟨2012503717228892784468583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2683338289638523712624777 2012503717228892784468583)
      ·
        refine ⟨3018755575843339176702875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012503717228892784468583 3018755575843339176702875)
        ·
          refine ⟨4528133363765008765054313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018755575843339176702875 4528133363765008765054313)
          ·
            refine ⟨3396100022823756573790735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528133363765008765054313 3396100022823756573790735)
            ·
              refine ⟨5094150034235634860686103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396100022823756573790735 5094150034235634860686103)
              ·
                refine ⟨7641225051353452291029155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094150034235634860686103 7641225051353452291029155)
                ·
                  refine ⟨11461837577030178436543733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641225051353452291029155 11461837577030178436543733)
                  ·
                    refine ⟨1074547272846579228425975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11461837577030178436543733 1074547272846579228425975)
                    ·
                      rfl

theorem cell22_3139010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3139010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139010 prefixEnd_3139010 := by exact prefixLift 3139010
  have htrace : WordTrace (prefixWord ++ tailWord_3139010) baseStart_3139010 baseEnd_3139010 := by
    simpa [prefixWord, tailWord_3139010, baseEnd_3139010] using wordTrace_append hprefix tailTrace_3139010
  have hstable : (prefixWord ++ tailWord_3139010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139010).length < 2 ^ (prefixWord ++ tailWord_3139010).sum := by decide
  have hdescent : baseEnd_3139010 < baseStart_3139010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139015 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3139015 : Nat := 118140960795 + 3139015 * 2 ^ 59
def prefixEnd_3139015 : Nat := 4983230072969 + 3 ^ 40 * 3139015 * 2
def baseEnd_3139015 : Nat := 1074548984448760882050959

theorem tailTrace_3139015 : CollatzResearch.WordTrace tailWord_3139015 prefixEnd_3139015 1074548984448760882050959 := by
  unfold tailWord_3139015
  simp only [CollatzResearch.WordTrace]
  refine ⟨114489282722892230925922499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76326188481928153950614999 114489282722892230925922499)
  ·
    refine ⟨171733924084338346388883749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114489282722892230925922499 171733924084338346388883749)
    ·
      refine ⟨32200110765813439947915703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171733924084338346388883749 32200110765813439947915703)
      ·
        refine ⟨48300166148720159921873555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32200110765813439947915703 48300166148720159921873555)
        ·
          refine ⟨72450249223080239882810333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48300166148720159921873555 72450249223080239882810333)
          ·
            refine ⟨27168843458655089956053875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72450249223080239882810333 27168843458655089956053875)
            ·
              refine ⟨40753265187982634934080813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27168843458655089956053875 40753265187982634934080813)
              ·
                refine ⟨15282474445493488100280305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40753265187982634934080813 15282474445493488100280305)
                ·
                  refine ⟨11461855834120116075210229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15282474445493488100280305 11461855834120116075210229)
                  ·
                    refine ⟨1074548984448760882050959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11461855834120116075210229 1074548984448760882050959)
                    ·
                      rfl

theorem cell22_3139015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3139015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139015 prefixEnd_3139015 := by exact prefixLift 3139015
  have htrace : WordTrace (prefixWord ++ tailWord_3139015) baseStart_3139015 baseEnd_3139015 := by
    simpa [prefixWord, tailWord_3139015, baseEnd_3139015] using wordTrace_append hprefix tailTrace_3139015
  have hstable : (prefixWord ++ tailWord_3139015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139015).length < 2 ^ (prefixWord ++ tailWord_3139015).sum := by decide
  have hdescent : baseEnd_3139015 < baseStart_3139015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139075 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_3139075 : Nat := 118140960795 + 3139075 * 2 ^ 59
def prefixEnd_3139075 : Nat := 4983230072969 + 3 ^ 40 * 3139075 * 2
def baseEnd_3139075 : Nat := 1074569523674940725550775

theorem tailTrace_3139075 : CollatzResearch.WordTrace tailWord_3139075 prefixEnd_3139075 1074569523674940725550775 := by
  unfold tailWord_3139075
  simp only [CollatzResearch.WordTrace]
  refine ⟨114491471102674861173106679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76327647401783240782071119 114491471102674861173106679)
  ·
    refine ⟨171737206654012291759660019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114491471102674861173106679 171737206654012291759660019)
    ·
      refine ⟨257605809981018437639490029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171737206654012291759660019 257605809981018437639490029)
      ·
        refine ⟨96602178742881914114808761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257605809981018437639490029 96602178742881914114808761)
        ·
          refine ⟨72451634057161435586106571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96602178742881914114808761 72451634057161435586106571)
          ·
            refine ⟨108677451085742153379159857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72451634057161435586106571 108677451085742153379159857)
            ·
              refine ⟨81508088314306615034369893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108677451085742153379159857 81508088314306615034369893)
              ·
                refine ⟨15282766558932490318944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81508088314306615034369893 15282766558932490318944355)
                ·
                  refine ⟨22924149838398735478416533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15282766558932490318944355 22924149838398735478416533)
                  ·
                    refine ⟨1074569523674940725550775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22924149838398735478416533 1074569523674940725550775)
                    ·
                      rfl

theorem cell22_3139075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_3139075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139075 prefixEnd_3139075 := by exact prefixLift 3139075
  have htrace : WordTrace (prefixWord ++ tailWord_3139075) baseStart_3139075 baseEnd_3139075 := by
    simpa [prefixWord, tailWord_3139075, baseEnd_3139075] using wordTrace_append hprefix tailTrace_3139075
  have hstable : (prefixWord ++ tailWord_3139075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139075).length < 2 ^ (prefixWord ++ tailWord_3139075).sum := by decide
  have hdescent : baseEnd_3139075 < baseStart_3139075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139107 : List Nat := [1, 1, 1, 4, 6, 9]
def baseStart_3139107 : Nat := 118140960795 + 3139107 * 2 ^ 59
def prefixEnd_3139107 : Nat := 4983230072969 + 3 ^ 40 * 3139107 * 2
def baseEnd_3139107 : Nat := 13266425653443250725317

theorem tailTrace_3139107 : CollatzResearch.WordTrace tailWord_3139107 prefixEnd_3139107 13266425653443250725317 := by
  unfold tailWord_3139107
  simp only [CollatzResearch.WordTrace]
  refine ⟨114492638238558930638271575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76328425492372620425514383 114492638238558930638271575)
  ·
    refine ⟨171738957357838395957407363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114492638238558930638271575 171738957357838395957407363)
    ·
      refine ⟨257608436036757593936111045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171738957357838395957407363 257608436036757593936111045)
      ·
        refine ⟨48301581756892048863020821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257608436036757593936111045 48301581756892048863020821)
        ·
          refine ⟨2264136644854314790454101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48301581756892048863020821 2264136644854314790454101)
          ·
            refine ⟨13266425653443250725317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2264136644854314790454101 13266425653443250725317)
            ·
              rfl

theorem cell22_3139107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 9].length) (baseStart_3139107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139107 prefixEnd_3139107 := by exact prefixLift 3139107
  have htrace : WordTrace (prefixWord ++ tailWord_3139107) baseStart_3139107 baseEnd_3139107 := by
    simpa [prefixWord, tailWord_3139107, baseEnd_3139107] using wordTrace_append hprefix tailTrace_3139107
  have hstable : (prefixWord ++ tailWord_3139107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139107).length < 2 ^ (prefixWord ++ tailWord_3139107).sum := by decide
  have hdescent : baseEnd_3139107 < baseStart_3139107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139137 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3139137 : Nat := 118140960795 + 3139137 * 2 ^ 59
def prefixEnd_3139137 : Nat := 4983230072969 + 3 ^ 40 * 3139137 * 2
def baseEnd_3139137 : Nat := 1074590747541993230500585

theorem tailTrace_3139137 : CollatzResearch.WordTrace tailWord_3139137 prefixEnd_3139137 1074590747541993230500585 := by
  unfold tailWord_3139137
  simp only [CollatzResearch.WordTrace]
  refine ⟨114493732428450245761863665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76329154952300163841242443 114493732428450245761863665)
  ·
    refine ⟨85870299321337684321397749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114493732428450245761863665 85870299321337684321397749)
    ·
      refine ⟨8050340561375407905131039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85870299321337684321397749 8050340561375407905131039)
      ·
        refine ⟨12075510842063111857696559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050340561375407905131039 12075510842063111857696559)
        ·
          refine ⟨18113266263094667786544839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075510842063111857696559 18113266263094667786544839)
          ·
            refine ⟨27169899394642001679817259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18113266263094667786544839 27169899394642001679817259)
            ·
              refine ⟨40754849091963002519725889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27169899394642001679817259 40754849091963002519725889)
              ·
                refine ⟨30566136818972251889794417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40754849091963002519725889 30566136818972251889794417)
                ·
                  refine ⟨22924602614229188917345813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30566136818972251889794417 22924602614229188917345813)
                  ·
                    refine ⟨1074590747541993230500585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22924602614229188917345813 1074590747541993230500585)
                    ·
                      rfl

theorem cell22_3139137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3139137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139137 prefixEnd_3139137 := by exact prefixLift 3139137
  have htrace : WordTrace (prefixWord ++ tailWord_3139137) baseStart_3139137 baseEnd_3139137 := by
    simpa [prefixWord, tailWord_3139137, baseEnd_3139137] using wordTrace_append hprefix tailTrace_3139137
  have hstable : (prefixWord ++ tailWord_3139137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139137).length < 2 ^ (prefixWord ++ tailWord_3139137).sum := by decide
  have hdescent : baseEnd_3139137 < baseStart_3139137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139186 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3139186 : Nat := 118140960795 + 3139186 * 2 ^ 59
def prefixEnd_3139186 : Nat := 4983230072969 + 3 ^ 40 * 3139186 * 2
def baseEnd_3139186 : Nat := 358202507081124478675145

theorem tailTrace_3139186 : CollatzResearch.WordTrace tailWord_3139186 prefixEnd_3139186 358202507081124478675145 := by
  unfold tailWord_3139186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623879901318181782599353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76330346403515151420264941 28623879901318181782599353)
  ·
    refine ⟨21467909925988636336949515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28623879901318181782599353 21467909925988636336949515)
    ·
      refine ⟨32201864888982954505424273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21467909925988636336949515 32201864888982954505424273)
      ·
        refine ⟨24151398666737215879068205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32201864888982954505424273 24151398666737215879068205)
        ·
          refine ⟨9056774500026455954650577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24151398666737215879068205 9056774500026455954650577)
          ·
            refine ⟨6792580875019841965987933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056774500026455954650577 6792580875019841965987933)
            ·
              refine ⟨2547217828132440737245475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6792580875019841965987933 2547217828132440737245475)
              ·
                refine ⟨3820826742198661105868213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547217828132440737245475 3820826742198661105868213)
                ·
                  refine ⟨358202507081124478675145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820826742198661105868213 358202507081124478675145)
                  ·
                    rfl

theorem cell22_3139186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3139186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139186 prefixEnd_3139186 := by exact prefixLift 3139186
  have htrace : WordTrace (prefixWord ++ tailWord_3139186) baseStart_3139186 baseEnd_3139186 := by
    simpa [prefixWord, tailWord_3139186, baseEnd_3139186] using wordTrace_append hprefix tailTrace_3139186
  have hstable : (prefixWord ++ tailWord_3139186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139186).length < 2 ^ (prefixWord ++ tailWord_3139186).sum := by decide
  have hdescent : baseEnd_3139186 < baseStart_3139186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139212 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_3139212 : Nat := 118140960795 + 3139212 * 2 ^ 59
def prefixEnd_3139212 : Nat := 4983230072969 + 3 ^ 40 * 3139212 * 2
def baseEnd_3139212 : Nat := 1074616421574718034875355

theorem tailTrace_3139212 : CollatzResearch.WordTrace tailWord_3139212 prefixEnd_3139212 1074616421574718034875355 := by
  unfold tailWord_3139212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57248233951589266785421945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76330978602119022380562593 57248233951589266785421945)
  ·
    refine ⟨42936175463691950089066459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57248233951589266785421945 42936175463691950089066459)
    ·
      refine ⟨64404263195537925133599689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42936175463691950089066459 64404263195537925133599689)
      ·
        refine ⟨48303197396653443850199767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64404263195537925133599689 48303197396653443850199767)
        ·
          refine ⟨72454796094980165775299651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48303197396653443850199767 72454796094980165775299651)
          ·
            refine ⟨108682194142470248662949477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72454796094980165775299651 108682194142470248662949477)
            ·
              refine ⟨20377911401713171624303027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108682194142470248662949477 20377911401713171624303027)
              ·
                refine ⟨30566867102569757436454541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20377911401713171624303027 30566867102569757436454541)
                ·
                  refine ⟨11462575163463659038670453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30566867102569757436454541 11462575163463659038670453)
                  ·
                    refine ⟨1074616421574718034875355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11462575163463659038670453 1074616421574718034875355)
                    ·
                      rfl

theorem cell22_3139212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_3139212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139212 prefixEnd_3139212 := by exact prefixLift 3139212
  have htrace : WordTrace (prefixWord ++ tailWord_3139212) baseStart_3139212 baseEnd_3139212 := by
    simpa [prefixWord, tailWord_3139212, baseEnd_3139212] using wordTrace_append hprefix tailTrace_3139212
  have hstable : (prefixWord ++ tailWord_3139212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139212).length < 2 ^ (prefixWord ++ tailWord_3139212).sum := by decide
  have hdescent : baseEnd_3139212 < baseStart_3139212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139257 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3139257 : Nat := 118140960795 + 3139257 * 2 ^ 59
def prefixEnd_3139257 : Nat := 4983230072969 + 3 ^ 40 * 3139257 * 2
def baseEnd_3139257 : Nat := 1074631825994352917500217

theorem tailTrace_3139257 : CollatzResearch.WordTrace tailWord_3139257 prefixEnd_3139257 1074631825994352917500217 := by
  unfold tailWord_3139257
  simp only [CollatzResearch.WordTrace]
  refine ⟨114498109188015506256232025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76332072792010337504154683 114498109188015506256232025)
  ·
    refine ⟨85873581891011629692174019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114498109188015506256232025 85873581891011629692174019)
    ·
      refine ⟨128810372836517444538261029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85873581891011629692174019 128810372836517444538261029)
      ·
        refine ⟨24151944906847020850923943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128810372836517444538261029 24151944906847020850923943)
        ·
          refine ⟨36227917360270531276385915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24151944906847020850923943 36227917360270531276385915)
          ·
            refine ⟨54341876040405796914578873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36227917360270531276385915 54341876040405796914578873)
            ·
              refine ⟨40756407030304347685934155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54341876040405796914578873 40756407030304347685934155)
              ·
                refine ⟨61134610545456521528901233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40756407030304347685934155 61134610545456521528901233)
                ·
                  refine ⟨45850957909092391146675925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61134610545456521528901233 45850957909092391146675925)
                  ·
                    refine ⟨1074631825994352917500217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45850957909092391146675925 1074631825994352917500217)
                    ·
                      rfl

theorem cell22_3139257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3139257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139257 prefixEnd_3139257 := by exact prefixLift 3139257
  have htrace : WordTrace (prefixWord ++ tailWord_3139257) baseStart_3139257 baseEnd_3139257 := by
    simpa [prefixWord, tailWord_3139257, baseEnd_3139257] using wordTrace_append hprefix tailTrace_3139257
  have hstable : (prefixWord ++ tailWord_3139257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139257).length < 2 ^ (prefixWord ++ tailWord_3139257).sum := by decide
  have hdescent : baseEnd_3139257 < baseStart_3139257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139293 : List Nat := [1, 4, 3, 3, 1, 2, 1, 7]
def baseStart_3139293 : Nat := 118140960795 + 3139293 * 2 ^ 59
def prefixEnd_3139293 : Nat := 4983230072969 + 3 ^ 40 * 3139293 * 2
def baseEnd_3139293 : Nat := 119404905503340091511123

theorem tailTrace_3139293 : CollatzResearch.WordTrace tailWord_3139293 prefixEnd_3139293 119404905503340091511123 := by
  unfold tailWord_3139293
  simp only [CollatzResearch.WordTrace]
  refine ⟨114499422215885084404542533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76332948143923389603028355 114499422215885084404542533)
  ·
    refine ⟨21468641665478453325851725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114499422215885084404542533 21468641665478453325851725)
    ·
      refine ⟨8050740624554419997194397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21468641665478453325851725 8050740624554419997194397)
      ·
        refine ⟨3019027734207907498947899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8050740624554419997194397 3019027734207907498947899)
        ·
          refine ⟨4528541601311861248421849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019027734207907498947899 4528541601311861248421849)
          ·
            refine ⟨3396406200983895936316387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528541601311861248421849 3396406200983895936316387)
            ·
              refine ⟨5094609301475843904474581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396406200983895936316387 5094609301475843904474581)
              ·
                refine ⟨119404905503340091511123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5094609301475843904474581 119404905503340091511123)
                ·
                  rfl

theorem cell22_3139293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 7].length) (baseStart_3139293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139293 prefixEnd_3139293 := by exact prefixLift 3139293
  have htrace : WordTrace (prefixWord ++ tailWord_3139293) baseStart_3139293 baseEnd_3139293 := by
    simpa [prefixWord, tailWord_3139293, baseEnd_3139293] using wordTrace_append hprefix tailTrace_3139293
  have hstable : (prefixWord ++ tailWord_3139293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139293).length < 2 ^ (prefixWord ++ tailWord_3139293).sum := by decide
  have hdescent : baseEnd_3139293 < baseStart_3139293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139349 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 6]
def baseStart_3139349 : Nat := 118140960795 + 3139349 * 2 ^ 59
def prefixEnd_3139349 : Nat := 4983230072969 + 3 ^ 40 * 3139349 * 2
def baseEnd_3139349 : Nat := 358221106491498448066645

theorem tailTrace_3139349 : CollatzResearch.WordTrace tailWord_3139349 prefixEnd_3139349 358221106491498448066645 := by
  unfold tailWord_3139349
  simp only [CollatzResearch.WordTrace]
  refine ⟨114501464703682205968581101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76334309802454803979054067 114501464703682205968581101)
  ·
    refine ⟨42938049263880827238217913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114501464703682205968581101 42938049263880827238217913)
    ·
      refine ⟨32203536947910620428663435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42938049263880827238217913 32203536947910620428663435)
      ·
        refine ⟨48305305421865930642995153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32203536947910620428663435 48305305421865930642995153)
        ·
          refine ⟨36228979066399447982246365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48305305421865930642995153 36228979066399447982246365)
          ·
            refine ⟨13585867149899792993342387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36228979066399447982246365 13585867149899792993342387)
            ·
              refine ⟨20378800724849689490013581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585867149899792993342387 20378800724849689490013581)
              ·
                refine ⟨7642050271818633558755093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20378800724849689490013581 7642050271818633558755093)
                ·
                  refine ⟨358221106491498448066645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7642050271818633558755093 358221106491498448066645)
                  ·
                    rfl

theorem cell22_3139349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_3139349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139349 prefixEnd_3139349 := by exact prefixLift 3139349
  have htrace : WordTrace (prefixWord ++ tailWord_3139349) baseStart_3139349 baseEnd_3139349 := by
    simpa [prefixWord, tailWord_3139349, baseEnd_3139349] using wordTrace_append hprefix tailTrace_3139349
  have hstable : (prefixWord ++ tailWord_3139349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139349).length < 2 ^ (prefixWord ++ tailWord_3139349).sum := by decide
  have hdescent : baseEnd_3139349 < baseStart_3139349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139368 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3139368 : Nat := 118140960795 + 3139368 * 2 ^ 59
def prefixEnd_3139368 : Nat := 4983230072969 + 3 ^ 40 * 3139368 * 2
def baseEnd_3139368 : Nat := 1074669823562785627974877

theorem tailTrace_3139368 : CollatzResearch.WordTrace tailWord_3139368 prefixEnd_3139368 1074669823562785627974877 := by
  unfold tailWord_3139368
  simp only [CollatzResearch.WordTrace]
  refine ⟨57251078845306686106761379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76334771793742248142348505 57251078845306686106761379)
  ·
    refine ⟨85876618267960029160142069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57251078845306686106761379 85876618267960029160142069)
    ·
      refine ⟨8050932962621252733763319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85876618267960029160142069 8050932962621252733763319)
      ·
        refine ⟨12076399443931879100644979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050932962621252733763319 12076399443931879100644979)
        ·
          refine ⟨18114599165897818650967469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076399443931879100644979 18114599165897818650967469)
          ·
            refine ⟨6792974687211681994112801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18114599165897818650967469 6792974687211681994112801)
            ·
              refine ⟨5094731015408761495584601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6792974687211681994112801 5094731015408761495584601)
              ·
                refine ⟨3821048261556571121688451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5094731015408761495584601 3821048261556571121688451)
                ·
                  refine ⟨5731572392334856682532677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821048261556571121688451 5731572392334856682532677)
                  ·
                    refine ⟨1074669823562785627974877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731572392334856682532677 1074669823562785627974877)
                    ·
                      rfl

theorem cell22_3139368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3139368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139368 prefixEnd_3139368 := by exact prefixLift 3139368
  have htrace : WordTrace (prefixWord ++ tailWord_3139368) baseStart_3139368 baseEnd_3139368 := by
    simpa [prefixWord, tailWord_3139368, baseEnd_3139368] using wordTrace_append hprefix tailTrace_3139368
  have hstable : (prefixWord ++ tailWord_3139368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139368).length < 2 ^ (prefixWord ++ tailWord_3139368).sum := by decide
  have hdescent : baseEnd_3139368 < baseStart_3139368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139443 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 1, 3]
def baseStart_3139443 : Nat := 118140960795 + 3139443 * 2 ^ 59
def prefixEnd_3139443 : Nat := 4983230072969 + 3 ^ 40 * 3139443 * 2
def baseEnd_3139443 : Nat := 1074695497595510432349647

theorem tailTrace_3139443 : CollatzResearch.WordTrace tailWord_3139443 prefixEnd_3139443 1074695497595510432349647 := by
  unfold tailWord_3139443
  simp only [CollatzResearch.WordTrace]
  refine ⟨114504893165341660022502983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76336595443561106681668655 114504893165341660022502983)
  ·
    refine ⟨171757339748012490033754475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114504893165341660022502983 171757339748012490033754475)
    ·
      refine ⟨257636009622018735050631713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171757339748012490033754475 257636009622018735050631713)
      ·
        refine ⟨193227007216514051287973785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257636009622018735050631713 193227007216514051287973785)
        ·
          refine ⟨144920255412385538465980339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193227007216514051287973785 144920255412385538465980339)
          ·
            refine ⟨217380383118578307698970509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144920255412385538465980339 217380383118578307698970509)
            ·
              refine ⟨81517643669466865387113941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217380383118578307698970509 81517643669466865387113941)
              ·
                refine ⟨1910569773503129657510483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81517643669466865387113941 1910569773503129657510483)
                ·
                  refine ⟨2865854660254694486265725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910569773503129657510483 2865854660254694486265725)
                  ·
                    refine ⟨1074695497595510432349647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865854660254694486265725 1074695497595510432349647)
                    ·
                      rfl

theorem cell22_3139443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 3].length) (baseStart_3139443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139443 prefixEnd_3139443 := by exact prefixLift 3139443
  have htrace : WordTrace (prefixWord ++ tailWord_3139443) baseStart_3139443 baseEnd_3139443 := by
    simpa [prefixWord, tailWord_3139443, baseEnd_3139443] using wordTrace_append hprefix tailTrace_3139443
  have hstable : (prefixWord ++ tailWord_3139443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139443).length < 2 ^ (prefixWord ++ tailWord_3139443).sum := by decide
  have hdescent : baseEnd_3139443 < baseStart_3139443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139456 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_3139456 : Nat := 118140960795 + 3139456 * 2 ^ 59
def prefixEnd_3139456 : Nat := 4983230072969 + 3 ^ 40 * 3139456 * 2
def baseEnd_3139456 : Nat := 358233315920394243924869

theorem tailTrace_3139456 : CollatzResearch.WordTrace tailWord_3139456 prefixEnd_3139456 358233315920394243924869 := by
  unfold tailWord_3139456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57252683657147281621363111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76336911542863042161817481 57252683657147281621363111)
  ·
    refine ⟨85879025485720922432044667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57252683657147281621363111 85879025485720922432044667)
    ·
      refine ⟨128818538228581383648067001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85879025485720922432044667 128818538228581383648067001)
      ·
        refine ⟨96613903671436037736050251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128818538228581383648067001 96613903671436037736050251)
        ·
          refine ⟨144920855507154056604075377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96613903671436037736050251 144920855507154056604075377)
          ·
            refine ⟨108690641630365542453056533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144920855507154056604075377 108690641630365542453056533)
            ·
              refine ⟨5094873826423384802487025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108690641630365542453056533 5094873826423384802487025)
              ·
                refine ⟨3821155369817538601865269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5094873826423384802487025 3821155369817538601865269)
                ·
                  refine ⟨358233315920394243924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3821155369817538601865269 358233315920394243924869)
                  ·
                    rfl

theorem cell22_3139456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_3139456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139456 prefixEnd_3139456 := by exact prefixLift 3139456
  have htrace : WordTrace (prefixWord ++ tailWord_3139456) baseStart_3139456 baseEnd_3139456 := by
    simpa [prefixWord, tailWord_3139456, baseEnd_3139456] using wordTrace_append hprefix tailTrace_3139456
  have hstable : (prefixWord ++ tailWord_3139456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139456).length < 2 ^ (prefixWord ++ tailWord_3139456).sum := by decide
  have hdescent : baseEnd_3139456 < baseStart_3139456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139518 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3139518 : Nat := 118140960795 + 3139518 * 2 ^ 59
def prefixEnd_3139518 : Nat := 4983230072969 + 3 ^ 40 * 3139518 * 2
def baseEnd_3139518 : Nat := 358240390542745078908139

theorem tailTrace_3139518 : CollatzResearch.WordTrace tailWord_3139518 prefixEnd_3139518 358240390542745078908139 := by
  unfold tailWord_3139518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313453580008743478935401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76338419093379965220988805 14313453580008743478935401)
  ·
    refine ⟨10735090185006557609201551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14313453580008743478935401 10735090185006557609201551)
    ·
      refine ⟨16102635277509836413802327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735090185006557609201551 16102635277509836413802327)
      ·
        refine ⟨24153952916264754620703491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16102635277509836413802327 24153952916264754620703491)
        ·
          refine ⟨36230929374397131931055237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24153952916264754620703491 36230929374397131931055237)
          ·
            refine ⟨6793299257699462237072857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36230929374397131931055237 6793299257699462237072857)
            ·
              refine ⟨5094974443274596677804643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793299257699462237072857 5094974443274596677804643)
              ·
                refine ⟨7642461664911895016706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094974443274596677804643 7642461664911895016706965)
                ·
                  refine ⟨358240390542745078908139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7642461664911895016706965 358240390542745078908139)
                  ·
                    rfl

theorem cell22_3139518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3139518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139518 prefixEnd_3139518 := by exact prefixLift 3139518
  have htrace : WordTrace (prefixWord ++ tailWord_3139518) baseStart_3139518 baseEnd_3139518 := by
    simpa [prefixWord, tailWord_3139518, baseEnd_3139518] using wordTrace_append hprefix tailTrace_3139518
  have hstable : (prefixWord ++ tailWord_3139518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139518).length < 2 ^ (prefixWord ++ tailWord_3139518).sum := by decide
  have hdescent : baseEnd_3139518 < baseStart_3139518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139672 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_3139672 : Nat := 118140960795 + 3139672 * 2 ^ 59
def prefixEnd_3139672 : Nat := 4983230072969 + 3 ^ 40 * 3139672 * 2
def baseEnd_3139672 : Nat := 1074773888975430168373945

theorem tailTrace_3139672 : CollatzResearch.WordTrace tailWord_3139672 prefixEnd_3139672 1074773888975430168373945 := by
  unfold tailWord_3139672
  simp only [CollatzResearch.WordTrace]
  refine ⟨57256622740756016066294635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76342163654341354755059513 57256622740756016066294635)
  ·
    refine ⟨85884934111134024099441953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57256622740756016066294635 85884934111134024099441953)
    ·
      refine ⟨64413700583350518074581465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85884934111134024099441953 64413700583350518074581465)
      ·
        refine ⟨48310275437512888555936099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64413700583350518074581465 48310275437512888555936099)
        ·
          refine ⟨72465413156269332833904149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48310275437512888555936099 72465413156269332833904149)
          ·
            refine ⟨3396816241700124976589257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72465413156269332833904149 3396816241700124976589257)
            ·
              refine ⟨2547612181275093732441943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396816241700124976589257 2547612181275093732441943)
              ·
                refine ⟨3821418271912640598662915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547612181275093732441943 3821418271912640598662915)
                ·
                  refine ⟨5732127407868960897994373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821418271912640598662915 5732127407868960897994373)
                  ·
                    refine ⟨1074773888975430168373945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732127407868960897994373 1074773888975430168373945)
                    ·
                      rfl

theorem cell22_3139672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_3139672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139672 prefixEnd_3139672 := by exact prefixLift 3139672
  have htrace : WordTrace (prefixWord ++ tailWord_3139672) baseStart_3139672 baseEnd_3139672 := by
    simpa [prefixWord, tailWord_3139672, baseEnd_3139672] using wordTrace_append hprefix tailTrace_3139672
  have hstable : (prefixWord ++ tailWord_3139672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139672).length < 2 ^ (prefixWord ++ tailWord_3139672).sum := by decide
  have hdescent : baseEnd_3139672 < baseStart_3139672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139683 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_3139683 : Nat := 118140960795 + 3139683 * 2 ^ 59
def prefixEnd_3139683 : Nat := 4983230072969 + 3 ^ 40 * 3139683 * 2
def baseEnd_3139683 : Nat := 1074777654500229806348911

theorem tailTrace_3139683 : CollatzResearch.WordTrace tailWord_3139683 prefixEnd_3139683 1074777654500229806348911 := by
  unfold tailWord_3139683
  simp only [CollatzResearch.WordTrace]
  refine ⟨114513646684472181011239703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76342431122981454007493135 114513646684472181011239703)
  ·
    refine ⟨171770470026708271516859555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114513646684472181011239703 171770470026708271516859555)
    ·
      refine ⟨257655705040062407275289333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171770470026708271516859555 257655705040062407275289333)
      ·
        refine ⟨24155222347505850682058375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257655705040062407275289333 24155222347505850682058375)
        ·
          refine ⟨36232833521258776023087563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24155222347505850682058375 36232833521258776023087563)
          ·
            refine ⟨54349250281888164034631345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36232833521258776023087563 54349250281888164034631345)
            ·
              refine ⟨40761937711416123025973509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54349250281888164034631345 40761937711416123025973509)
              ·
                refine ⟨7642863320890523067370033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40761937711416123025973509 7642863320890523067370033)
                ·
                  refine ⟨5732147490667892300527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642863320890523067370033 5732147490667892300527525)
                  ·
                    refine ⟨1074777654500229806348911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732147490667892300527525 1074777654500229806348911)
                    ·
                      rfl

theorem cell22_3139683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_3139683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139683 prefixEnd_3139683 := by exact prefixLift 3139683
  have htrace : WordTrace (prefixWord ++ tailWord_3139683) baseStart_3139683 baseEnd_3139683 := by
    simpa [prefixWord, tailWord_3139683, baseEnd_3139683] using wordTrace_append hprefix tailTrace_3139683
  have hstable : (prefixWord ++ tailWord_3139683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139683).length < 2 ^ (prefixWord ++ tailWord_3139683).sum := by decide
  have hdescent : baseEnd_3139683 < baseStart_3139683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139685 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_3139685 : Nat := 118140960795 + 3139685 * 2 ^ 59
def prefixEnd_3139685 : Nat := 4983230072969 + 3 ^ 40 * 3139685 * 2
def baseEnd_3139685 : Nat := 1074778339141102467798905

theorem tailTrace_3139685 : CollatzResearch.WordTrace tailWord_3139685 prefixEnd_3139685 1074778339141102467798905 := by
  unfold tailWord_3139685
  simp only [CollatzResearch.WordTrace]
  refine ⟨114513719630464935352812509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76342479753643290235208339 114513719630464935352812509)
  ·
    refine ⟨42942644861424350757304691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114513719630464935352812509 42942644861424350757304691)
    ·
      refine ⟨64413967292136526135957037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42942644861424350757304691 64413967292136526135957037)
      ·
        refine ⟨24155237734551197300983889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64413967292136526135957037 24155237734551197300983889)
        ·
          refine ⟨18116428300913397975737917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24155237734551197300983889 18116428300913397975737917)
          ·
            refine ⟨6793660612842524240901719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18116428300913397975737917 6793660612842524240901719)
            ·
              refine ⟨10190490919263786361352579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793660612842524240901719 10190490919263786361352579)
              ·
                refine ⟨15285736378895679542028869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190490919263786361352579 15285736378895679542028869)
                ·
                  refine ⟨2866075571042939914130413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15285736378895679542028869 2866075571042939914130413)
                  ·
                    refine ⟨1074778339141102467798905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866075571042939914130413 1074778339141102467798905)
                    ·
                      rfl

theorem cell22_3139685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_3139685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139685 prefixEnd_3139685 := by exact prefixLift 3139685
  have htrace : WordTrace (prefixWord ++ tailWord_3139685) baseStart_3139685 baseEnd_3139685 := by
    simpa [prefixWord, tailWord_3139685, baseEnd_3139685] using wordTrace_append hprefix tailTrace_3139685
  have hstable : (prefixWord ++ tailWord_3139685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139685).length < 2 ^ (prefixWord ++ tailWord_3139685).sum := by decide
  have hdescent : baseEnd_3139685 < baseStart_3139685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139702 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3139702 : Nat := 118140960795 + 3139702 * 2 ^ 59
def prefixEnd_3139702 : Nat := 4983230072969 + 3 ^ 40 * 3139702 * 2
def baseEnd_3139702 : Nat := 1074784158588520090123853

theorem tailTrace_3139702 : CollatzResearch.WordTrace tailWord_3139702 prefixEnd_3139702 1074784158588520090123853 := by
  unfold tailWord_3139702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157146229462709203511335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76342893114268898170787573 7157146229462709203511335)
  ·
    refine ⟨10735719344194063805267003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7157146229462709203511335 10735719344194063805267003)
    ·
      refine ⟨16103579016291095707900505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735719344194063805267003 16103579016291095707900505)
      ·
        refine ⟨12077684262218321780925379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16103579016291095707900505 12077684262218321780925379)
        ·
          refine ⟨18116526393327482671388069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12077684262218321780925379 18116526393327482671388069)
          ·
            refine ⟨3396848698748903000885263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18116526393327482671388069 3396848698748903000885263)
            ·
              refine ⟨5095273048123354501327895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396848698748903000885263 5095273048123354501327895)
              ·
                refine ⟨7642909572185031751991843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095273048123354501327895 7642909572185031751991843)
                ·
                  refine ⟨11464364358277547627987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7642909572185031751991843 11464364358277547627987765)
                  ·
                    refine ⟨1074784158588520090123853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464364358277547627987765 1074784158588520090123853)
                    ·
                      rfl

theorem cell22_3139702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3139702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139702 prefixEnd_3139702 := by exact prefixLift 3139702
  have htrace : WordTrace (prefixWord ++ tailWord_3139702) baseStart_3139702 baseEnd_3139702 := by
    simpa [prefixWord, tailWord_3139702, baseEnd_3139702] using wordTrace_append hprefix tailTrace_3139702
  have hstable : (prefixWord ++ tailWord_3139702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139702).length < 2 ^ (prefixWord ++ tailWord_3139702).sum := by decide
  have hdescent : baseEnd_3139702 < baseStart_3139702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139715 : List Nat := [1, 1, 1, 3, 3, 5, 2, 6]
def baseStart_3139715 : Nat := 118140960795 + 3139715 * 2 ^ 59
def prefixEnd_3139715 : Nat := 4983230072969 + 3 ^ 40 * 3139715 * 2
def baseEnd_3139715 : Nat := 119420956528243598838757

theorem tailTrace_3139715 : CollatzResearch.WordTrace tailWord_3139715 prefixEnd_3139715 119420956528243598838757 := by
  unfold tailWord_3139715
  simp only [CollatzResearch.WordTrace]
  refine ⟨114514813820356250476404599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76343209213570833650936399 114514813820356250476404599)
  ·
    refine ⟨171772220730534375714606899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114514813820356250476404599 171772220730534375714606899)
    ·
      refine ⟨257658331095801563571910349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171772220730534375714606899 257658331095801563571910349)
      ·
        refine ⟨96621874160925586339466381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257658331095801563571910349 96621874160925586339466381)
        ·
          refine ⟨36233202810347094877299893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96621874160925586339466381 36233202810347094877299893)
          ·
            refine ⟨3396862763470040144746865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36233202810347094877299893 3396862763470040144746865)
            ·
              refine ⟨2547647072602530108560149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396862763470040144746865 2547647072602530108560149)
              ·
                refine ⟨119420956528243598838757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2547647072602530108560149 119420956528243598838757)
                ·
                  rfl

theorem cell22_3139715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 6].length) (baseStart_3139715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139715 prefixEnd_3139715 := by exact prefixLift 3139715
  have htrace : WordTrace (prefixWord ++ tailWord_3139715) baseStart_3139715 baseEnd_3139715 := by
    simpa [prefixWord, tailWord_3139715, baseEnd_3139715] using wordTrace_append hprefix tailTrace_3139715
  have hstable : (prefixWord ++ tailWord_3139715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139715).length < 2 ^ (prefixWord ++ tailWord_3139715).sum := by decide
  have hdescent : baseEnd_3139715 < baseStart_3139715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139732 : List Nat := [2, 4, 2, 3, 1, 2, 8]
def baseStart_3139732 : Nat := 118140960795 + 3139732 * 2 ^ 59
def prefixEnd_3139732 : Nat := 4983230072969 + 3 ^ 40 * 3139732 * 2
def baseEnd_3139732 : Nat := 39807201044504074513843

theorem tailTrace_3139732 : CollatzResearch.WordTrace tailWord_3139732 prefixEnd_3139732 39807201044504074513843 := by
  unfold tailWord_3139732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57257716930647331189886725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76343622574196441586515633 57257716930647331189886725)
  ·
    refine ⟨10735821924496374598103761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57257716930647331189886725 10735821924496374598103761)
    ·
      refine ⟨8051866443372280948577821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10735821924496374598103761 8051866443372280948577821)
      ·
        refine ⟨3019449916264605355716683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8051866443372280948577821 3019449916264605355716683)
        ·
          refine ⟨4529174874396908033575025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019449916264605355716683 4529174874396908033575025)
          ·
            refine ⟨3396881155797681025181269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529174874396908033575025 3396881155797681025181269)
            ·
              refine ⟨39807201044504074513843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3396881155797681025181269 39807201044504074513843)
              ·
                rfl

theorem cell22_3139732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 8].length) (baseStart_3139732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139732 prefixEnd_3139732 := by exact prefixLift 3139732
  have htrace : WordTrace (prefixWord ++ tailWord_3139732) baseStart_3139732 baseEnd_3139732 := by
    simpa [prefixWord, tailWord_3139732, baseEnd_3139732] using wordTrace_append hprefix tailTrace_3139732
  have hstable : (prefixWord ++ tailWord_3139732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139732).length < 2 ^ (prefixWord ++ tailWord_3139732).sum := by decide
  have hdescent : baseEnd_3139732 < baseStart_3139732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139798 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3139798 : Nat := 118140960795 + 3139798 * 2 ^ 59
def prefixEnd_3139798 : Nat := 4983230072969 + 3 ^ 40 * 3139798 * 2
def baseEnd_3139798 : Nat := 1074817021350407839723559

theorem tailTrace_3139798 : CollatzResearch.WordTrace tailWord_3139798 prefixEnd_3139798 1074817021350407839723559 := by
  unfold tailWord_3139798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157365067440972228229753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76345227386037037101117365 7157365067440972228229753)
  ·
    refine ⟨5368023800580729171172315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7157365067440972228229753 5368023800580729171172315)
    ·
      refine ⟨8052035700871093756758473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368023800580729171172315 8052035700871093756758473)
      ·
        refine ⟨6039026775653320317568855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8052035700871093756758473 6039026775653320317568855)
        ·
          refine ⟨9058540163479980476353283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039026775653320317568855 9058540163479980476353283)
          ·
            refine ⟨13587810245219970714529925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058540163479980476353283 13587810245219970714529925)
            ·
              refine ⟨2547714420978744508974361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13587810245219970714529925 2547714420978744508974361)
              ·
                refine ⟨1910785815734058381730771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547714420978744508974361 1910785815734058381730771)
                ·
                  refine ⟨2866178723601087572596157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910785815734058381730771 2866178723601087572596157)
                  ·
                    refine ⟨1074817021350407839723559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866178723601087572596157 1074817021350407839723559)
                    ·
                      rfl

theorem cell22_3139798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3139798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139798 prefixEnd_3139798 := by exact prefixLift 3139798
  have htrace : WordTrace (prefixWord ++ tailWord_3139798) baseStart_3139798 baseEnd_3139798 := by
    simpa [prefixWord, tailWord_3139798, baseEnd_3139798] using wordTrace_append hprefix tailTrace_3139798
  have hstable : (prefixWord ++ tailWord_3139798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139798).length < 2 ^ (prefixWord ++ tailWord_3139798).sum := by decide
  have hdescent : baseEnd_3139798 < baseStart_3139798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139820 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_3139820 : Nat := 118140960795 + 3139820 * 2 ^ 59
def prefixEnd_3139820 : Nat := 4983230072969 + 3 ^ 40 * 3139820 * 2
def baseEnd_3139820 : Nat := 1074824552400007115673491

theorem tailTrace_3139820 : CollatzResearch.WordTrace tailWord_3139820 prefixEnd_3139820 1074824552400007115673491 := by
  unfold tailWord_3139820
  simp only [CollatzResearch.WordTrace]
  refine ⟨57259321742487926704488457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76345762323317235605984609 57259321742487926704488457)
  ·
    refine ⟨42944491306865945028366343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57259321742487926704488457 42944491306865945028366343)
    ·
      refine ⟨64416736960298917542549515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42944491306865945028366343 64416736960298917542549515)
      ·
        refine ⟨96625105440448376313824273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64416736960298917542549515 96625105440448376313824273)
        ·
          refine ⟨72468829080336282235368205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96625105440448376313824273 72468829080336282235368205)
          ·
            refine ⟨27175810905126105838263077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72468829080336282235368205 27175810905126105838263077)
            ·
              refine ⟨5095464544711144844674327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27175810905126105838263077 5095464544711144844674327)
              ·
                refine ⟨7643196817066717267011491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095464544711144844674327 7643196817066717267011491)
                ·
                  refine ⟨11464795225600075900517237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643196817066717267011491 11464795225600075900517237)
                  ·
                    refine ⟨1074824552400007115673491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464795225600075900517237 1074824552400007115673491)
                    ·
                      rfl

theorem cell22_3139820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_3139820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139820 prefixEnd_3139820 := by exact prefixLift 3139820
  have htrace : WordTrace (prefixWord ++ tailWord_3139820) baseStart_3139820 baseEnd_3139820 := by
    simpa [prefixWord, tailWord_3139820, baseEnd_3139820] using wordTrace_append hprefix tailTrace_3139820
  have hstable : (prefixWord ++ tailWord_3139820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139820).length < 2 ^ (prefixWord ++ tailWord_3139820).sum := by decide
  have hdescent : baseEnd_3139820 < baseStart_3139820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139916 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_3139916 : Nat := 118140960795 + 3139916 * 2 ^ 59
def prefixEnd_3139916 : Nat := 4983230072969 + 3 ^ 40 * 3139916 * 2
def baseEnd_3139916 : Nat := 1074857415161894865273197

theorem tailTrace_3139916 : CollatzResearch.WordTrace tailWord_3139916 prefixEnd_3139916 1074857415161894865273197 := by
  unfold tailWord_3139916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261072446314030902235801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76348096595085374536314401 57261072446314030902235801)
  ·
    refine ⟨42945804334735523176676851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57261072446314030902235801 42945804334735523176676851)
    ·
      refine ⟨64418706502103284765015277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42945804334735523176676851 64418706502103284765015277)
      ·
        refine ⟨24157014938288731786880729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64418706502103284765015277 24157014938288731786880729)
        ·
          refine ⟨18117761203716548840160547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24157014938288731786880729 18117761203716548840160547)
          ·
            refine ⟨27176641805574823260240821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18117761203716548840160547 27176641805574823260240821)
            ·
              refine ⟨2547810169272639680647577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27176641805574823260240821 2547810169272639680647577)
              ·
                refine ⟨1910857626954479760485683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547810169272639680647577 1910857626954479760485683)
                ·
                  refine ⟨2866286440431719640728525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910857626954479760485683 2866286440431719640728525)
                  ·
                    refine ⟨1074857415161894865273197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866286440431719640728525 1074857415161894865273197)
                    ·
                      rfl

theorem cell22_3139916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_3139916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139916 prefixEnd_3139916 := by exact prefixLift 3139916
  have htrace : WordTrace (prefixWord ++ tailWord_3139916) baseStart_3139916 baseEnd_3139916 := by
    simpa [prefixWord, tailWord_3139916, baseEnd_3139916] using wordTrace_append hprefix tailTrace_3139916
  have hstable : (prefixWord ++ tailWord_3139916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139916).length < 2 ^ (prefixWord ++ tailWord_3139916).sum := by decide
  have hdescent : baseEnd_3139916 < baseStart_3139916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139940 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_3139940 : Nat := 118140960795 + 3139940 * 2 ^ 59
def prefixEnd_3139940 : Nat := 4983230072969 + 3 ^ 40 * 3139940 * 2
def baseEnd_3139940 : Nat := 358288543617455600891041

theorem tailTrace_3139940 : CollatzResearch.WordTrace tailWord_3139940 prefixEnd_3139940 358288543617455600891041 := by
  unfold tailWord_3139940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261510122270556951672637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76348680163027409268896849 57261510122270556951672637)
  ·
    refine ⟨21473066295851458856877239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57261510122270556951672637 21473066295851458856877239)
    ·
      refine ⟨32209599443777188285315859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21473066295851458856877239 32209599443777188285315859)
      ·
        refine ⟨48314399165665782427973789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32209599443777188285315859 48314399165665782427973789)
        ·
          refine ⟨18117899687124668410490171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48314399165665782427973789 18117899687124668410490171)
          ·
            refine ⟨27176849530687002615735257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18117899687124668410490171 27176849530687002615735257)
            ·
              refine ⟨20382637148015251961801443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27176849530687002615735257 20382637148015251961801443)
              ·
                refine ⟨30573955722022877942702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20382637148015251961801443 30573955722022877942702165)
                ·
                  refine ⟨358288543617455600891041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30573955722022877942702165 358288543617455600891041)
                  ·
                    rfl

theorem cell22_3139940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_3139940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139940 prefixEnd_3139940 := by exact prefixLift 3139940
  have htrace : WordTrace (prefixWord ++ tailWord_3139940) baseStart_3139940 baseEnd_3139940 := by
    simpa [prefixWord, tailWord_3139940, baseEnd_3139940] using wordTrace_append hprefix tailTrace_3139940
  have hstable : (prefixWord ++ tailWord_3139940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139940).length < 2 ^ (prefixWord ++ tailWord_3139940).sum := by decide
  have hdescent : baseEnd_3139940 < baseStart_3139940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139955 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_3139955 : Nat := 118140960795 + 3139955 * 2 ^ 59
def prefixEnd_3139955 : Nat := 4983230072969 + 3 ^ 40 * 3139955 * 2
def baseEnd_3139955 : Nat := 1074870765658911763548077

theorem tailTrace_3139955 : CollatzResearch.WordTrace tailWord_3139955 prefixEnd_3139955 1074870765658911763548077 := by
  unfold tailWord_3139955
  simp only [CollatzResearch.WordTrace]
  refine ⟨114523567339486771465141319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76349044892991180976760879 114523567339486771465141319)
  ·
    refine ⟨171785351009230157197711979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114523567339486771465141319 171785351009230157197711979)
    ·
      refine ⟨257678026513845235796567969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171785351009230157197711979 257678026513845235796567969)
      ·
        refine ⟨193258519885383926847425977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257678026513845235796567969 193258519885383926847425977)
        ·
          refine ⟨144943889914037945135569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193258519885383926847425977 144943889914037945135569483)
          ·
            refine ⟨217415834871056917703354225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144943889914037945135569483 217415834871056917703354225)
            ·
              refine ⟨163061876153292688277515669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217415834871056917703354225 163061876153292688277515669)
              ·
                refine ⟨7643525444685594763008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163061876153292688277515669 7643525444685594763008547)
                ·
                  refine ⟨11465288167028392144512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643525444685594763008547 11465288167028392144512821)
                  ·
                    refine ⟨1074870765658911763548077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11465288167028392144512821 1074870765658911763548077)
                    ·
                      rfl

theorem cell22_3139955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_3139955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3139955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3139955 prefixEnd_3139955 := by exact prefixLift 3139955
  have htrace : WordTrace (prefixWord ++ tailWord_3139955) baseStart_3139955 baseEnd_3139955 := by
    simpa [prefixWord, tailWord_3139955, baseEnd_3139955] using wordTrace_append hprefix tailTrace_3139955
  have hstable : (prefixWord ++ tailWord_3139955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139955).length < 2 ^ (prefixWord ++ tailWord_3139955).sum := by decide
  have hdescent : baseEnd_3139955 < baseStart_3139955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140085 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3140085 : Nat := 118140960795 + 3140085 * 2 ^ 59
def prefixEnd_3140085 : Nat := 4983230072969 + 3 ^ 40 * 3140085 * 2
def baseEnd_3140085 : Nat := 1074915267315634757797679

theorem tailTrace_3140085 : CollatzResearch.WordTrace tailWord_3140085 prefixEnd_3140085 1074915267315634757797679 := by
  unfold tailWord_3140085
  simp only [CollatzResearch.WordTrace]
  refine ⟨114528308829015803667373709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76352205886010535778249139 114528308829015803667373709)
  ·
    refine ⟨42948115810880926375265141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114528308829015803667373709 42948115810880926375265141)
    ·
      refine ⟨4026385857270086847681107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42948115810880926375265141 4026385857270086847681107)
      ·
        refine ⟨6039578785905130271521661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026385857270086847681107 6039578785905130271521661)
        ·
          refine ⟨2264842044714423851820623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039578785905130271521661 2264842044714423851820623)
          ·
            refine ⟨3397263067071635777730935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264842044714423851820623 3397263067071635777730935)
            ·
              refine ⟨5095894600607453666596403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397263067071635777730935 5095894600607453666596403)
              ·
                refine ⟨7643841900911180499894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095894600607453666596403 7643841900911180499894605)
                ·
                  refine ⟨2866440712841692687460477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7643841900911180499894605 2866440712841692687460477)
                  ·
                    refine ⟨1074915267315634757797679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866440712841692687460477 1074915267315634757797679)
                    ·
                      rfl

theorem cell22_3140085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3140085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140085 prefixEnd_3140085 := by exact prefixLift 3140085
  have htrace : WordTrace (prefixWord ++ tailWord_3140085) baseStart_3140085 baseEnd_3140085 := by
    simpa [prefixWord, tailWord_3140085, baseEnd_3140085] using wordTrace_append hprefix tailTrace_3140085
  have hstable : (prefixWord ++ tailWord_3140085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140085).length < 2 ^ (prefixWord ++ tailWord_3140085).sum := by decide
  have hdescent : baseEnd_3140085 < baseStart_3140085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140122 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_3140122 : Nat := 118140960795 + 3140122 * 2 ^ 59
def prefixEnd_3140122 : Nat := 4983230072969 + 3 ^ 40 * 3140122 * 2
def baseEnd_3140122 : Nat := 1074927933171778994622565

theorem tailTrace_3140122 : CollatzResearch.WordTrace tailWord_3140122 prefixEnd_3140122 1074927933171778994622565 := by
  unfold tailWord_3140122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28632414582470439746617655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76353105553254505990980413 28632414582470439746617655)
  ·
    refine ⟨42948621873705659619926483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28632414582470439746617655 42948621873705659619926483)
    ·
      refine ⟨64422932810558489429889725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42948621873705659619926483 64422932810558489429889725)
      ·
        refine ⟨24158599803959433536208647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64422932810558489429889725 24158599803959433536208647)
        ·
          refine ⟨36237899705939150304312971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24158599803959433536208647 36237899705939150304312971)
          ·
            refine ⟨54356849558908725456469457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36237899705939150304312971 54356849558908725456469457)
            ·
              refine ⟨40767637169181544092352093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54356849558908725456469457 40767637169181544092352093)
              ·
                refine ⟨15287863938443079034632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40767637169181544092352093 15287863938443079034632035)
                ·
                  refine ⟨22931795907664618551948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15287863938443079034632035 22931795907664618551948053)
                  ·
                    refine ⟨1074927933171778994622565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22931795907664618551948053 1074927933171778994622565)
                    ·
                      rfl

theorem cell22_3140122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_3140122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140122 prefixEnd_3140122 := by exact prefixLift 3140122
  have htrace : WordTrace (prefixWord ++ tailWord_3140122) baseStart_3140122 baseEnd_3140122 := by
    simpa [prefixWord, tailWord_3140122, baseEnd_3140122] using wordTrace_append hprefix tailTrace_3140122
  have hstable : (prefixWord ++ tailWord_3140122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140122).length < 2 ^ (prefixWord ++ tailWord_3140122).sum := by decide
  have hdescent : baseEnd_3140122 < baseStart_3140122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140124 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3140124 : Nat := 118140960795 + 3140124 * 2 ^ 59
def prefixEnd_3140124 : Nat := 4983230072969 + 3 ^ 40 * 3140124 * 2
def baseEnd_3140124 : Nat := 1074928617812651656072559

theorem tailTrace_3140124 : CollatzResearch.WordTrace tailWord_3140124 prefixEnd_3140124 1074928617812651656072559 := by
  unfold tailWord_3140124
  simp only [CollatzResearch.WordTrace]
  refine ⟨57264865637937256664021713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76353154183916342218695617 57264865637937256664021713)
  ·
    refine ⟨42948649228452942498016285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57264865637937256664021713 42948649228452942498016285)
    ·
      refine ⟨16105743460669853436756107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42948649228452942498016285 16105743460669853436756107)
      ·
        refine ⟨24158615191004780155134161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105743460669853436756107 24158615191004780155134161)
        ·
          refine ⟨18118961393253585116350621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24158615191004780155134161 18118961393253585116350621)
          ·
            refine ⟨6794610522470094418631483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18118961393253585116350621 6794610522470094418631483)
            ·
              refine ⟨10191915783705141627947225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794610522470094418631483 10191915783705141627947225)
              ·
                refine ⟨7643936837778856220960419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191915783705141627947225 7643936837778856220960419)
                ·
                  refine ⟨11465905256668284331440629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643936837778856220960419 11465905256668284331440629)
                  ·
                    refine ⟨1074928617812651656072559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11465905256668284331440629 1074928617812651656072559)
                    ·
                      rfl

theorem cell22_3140124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3140124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140124 prefixEnd_3140124 := by exact prefixLift 3140124
  have htrace : WordTrace (prefixWord ++ tailWord_3140124) baseStart_3140124 baseEnd_3140124 := by
    simpa [prefixWord, tailWord_3140124, baseEnd_3140124] using wordTrace_append hprefix tailTrace_3140124
  have hstable : (prefixWord ++ tailWord_3140124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140124).length < 2 ^ (prefixWord ++ tailWord_3140124).sum := by decide
  have hdescent : baseEnd_3140124 < baseStart_3140124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140128 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_3140128 : Nat := 118140960795 + 3140128 * 2 ^ 59
def prefixEnd_3140128 : Nat := 4983230072969 + 3 ^ 40 * 3140128 * 2
def baseEnd_3140128 : Nat := 1074929987094396978972547

theorem tailTrace_3140128 : CollatzResearch.WordTrace tailWord_3140128 prefixEnd_3140128 1074929987094396978972547 := by
  unfold tailWord_3140128
  simp only [CollatzResearch.WordTrace]
  refine ⟨57264938583930011005594519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76353251445240014674126025 57264938583930011005594519)
  ·
    refine ⟨85897407875895016508391779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57264938583930011005594519 85897407875895016508391779)
    ·
      refine ⟨128846111813842524762587669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85897407875895016508391779 128846111813842524762587669)
      ·
        refine ⟨6039661491273868348246297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128846111813842524762587669 6039661491273868348246297)
        ·
          refine ⟨4529746118455401261184723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6039661491273868348246297 4529746118455401261184723)
          ·
            refine ⟨6794619177683101891777085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529746118455401261184723 6794619177683101891777085)
            ·
              refine ⟨2547982191631163209416407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6794619177683101891777085 2547982191631163209416407)
              ·
                refine ⟨3821973287446744814124611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547982191631163209416407 3821973287446744814124611)
                ·
                  refine ⟨5732959931170117221186917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821973287446744814124611 5732959931170117221186917)
                  ·
                    refine ⟨1074929987094396978972547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732959931170117221186917 1074929987094396978972547)
                    ·
                      rfl

theorem cell22_3140128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_3140128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140128 prefixEnd_3140128 := by exact prefixLift 3140128
  have htrace : WordTrace (prefixWord ++ tailWord_3140128) baseStart_3140128 baseEnd_3140128 := by
    simpa [prefixWord, tailWord_3140128, baseEnd_3140128] using wordTrace_append hprefix tailTrace_3140128
  have hstable : (prefixWord ++ tailWord_3140128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140128).length < 2 ^ (prefixWord ++ tailWord_3140128).sum := by decide
  have hdescent : baseEnd_3140128 < baseStart_3140128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140154 : List Nat := [3, 1, 1, 1, 3, 5, 1, 7]
def baseStart_3140154 : Nat := 118140960795 + 3140154 * 2 ^ 59
def prefixEnd_3140154 : Nat := 4983230072969 + 3 ^ 40 * 3140154 * 2
def baseEnd_3140154 : Nat := 119437654158415730869163

theorem tailTrace_3140154 : CollatzResearch.WordTrace tailWord_3140154 prefixEnd_3140154 119437654158415730869163 := by
  unfold tailWord_3140154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28632706366441457112908879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76353883643843885634423677 28632706366441457112908879)
  ·
    refine ⟨42949059549662185669363319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28632706366441457112908879 42949059549662185669363319)
    ·
      refine ⟨64423589324493278504044979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42949059549662185669363319 64423589324493278504044979)
      ·
        refine ⟨96635383986739917756067469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64423589324493278504044979 96635383986739917756067469)
        ·
          refine ⟨36238268995027469158525301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96635383986739917756067469 36238268995027469158525301)
          ·
            refine ⟨3397337718283825233611747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36238268995027469158525301 3397337718283825233611747)
            ·
              refine ⟨5096006577425737850417621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397337718283825233611747 5096006577425737850417621)
              ·
                refine ⟨119437654158415730869163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5096006577425737850417621 119437654158415730869163)
                ·
                  rfl

theorem cell22_3140154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_3140154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140154 prefixEnd_3140154 := by exact prefixLift 3140154
  have htrace : WordTrace (prefixWord ++ tailWord_3140154) baseStart_3140154 baseEnd_3140154 := by
    simpa [prefixWord, tailWord_3140154, baseEnd_3140154] using wordTrace_append hprefix tailTrace_3140154
  have hstable : (prefixWord ++ tailWord_3140154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140154).length < 2 ^ (prefixWord ++ tailWord_3140154).sum := by decide
  have hdescent : baseEnd_3140154 < baseStart_3140154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140158 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3140158 : Nat := 118140960795 + 3140158 * 2 ^ 59
def prefixEnd_3140158 : Nat := 4983230072969 + 3 ^ 40 * 3140158 * 2
def baseEnd_3140158 : Nat := 1074940256707486900722455

theorem tailTrace_3140158 : CollatzResearch.WordTrace tailWord_3140158 prefixEnd_3140158 1074940256707486900722455 := by
  unfold tailWord_3140158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316371419718917141847641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76353980905167558089854085 14316371419718917141847641)
  ·
    refine ⟨10737278564789187856385731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14316371419718917141847641 10737278564789187856385731)
    ·
      refine ⟨16105917847183781784578597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10737278564789187856385731 16105917847183781784578597)
      ·
        refine ⟨3019859596346959084608487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16105917847183781784578597 3019859596346959084608487)
        ·
          refine ⟨4529789394520438626912731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019859596346959084608487 4529789394520438626912731)
          ·
            refine ⟨6794684091780657940369097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529789394520438626912731 6794684091780657940369097)
            ·
              refine ⟨5096013068835493455276823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794684091780657940369097 5096013068835493455276823)
              ·
                refine ⟨7644019603253240182915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096013068835493455276823 7644019603253240182915235)
                ·
                  refine ⟨11466029404879860274372853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644019603253240182915235 11466029404879860274372853)
                  ·
                    refine ⟨1074940256707486900722455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11466029404879860274372853 1074940256707486900722455)
                    ·
                      rfl

theorem cell22_3140158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3140158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140158 prefixEnd_3140158 := by exact prefixLift 3140158
  have htrace : WordTrace (prefixWord ++ tailWord_3140158) baseStart_3140158 baseEnd_3140158 := by
    simpa [prefixWord, tailWord_3140158, baseEnd_3140158] using wordTrace_append hprefix tailTrace_3140158
  have hstable : (prefixWord ++ tailWord_3140158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140158).length < 2 ^ (prefixWord ++ tailWord_3140158).sum := by decide
  have hdescent : baseEnd_3140158 < baseStart_3140158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140173 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3140173 : Nat := 118140960795 + 3140173 * 2 ^ 59
def prefixEnd_3140173 : Nat := 4983230072969 + 3 ^ 40 * 3140173 * 2
def baseEnd_3140173 : Nat := 1074945391514031861597409

theorem tailTrace_3140173 : CollatzResearch.WordTrace tailWord_3140173 prefixEnd_3140173 1074945391514031861597409 := by
  unfold tailWord_3140173
  simp only [CollatzResearch.WordTrace]
  refine ⟨114531518452696994696577173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76354345635131329797718115 114531518452696994696577173)
  ·
    refine ⟨5368664927470171626402055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114531518452696994696577173 5368664927470171626402055)
    ·
      refine ⟨8052997391205257439603083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368664927470171626402055 8052997391205257439603083)
      ·
        refine ⟨12079496086807886159404625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052997391205257439603083 12079496086807886159404625)
        ·
          refine ⟨9059622065105914619553469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12079496086807886159404625 9059622065105914619553469)
          ·
            refine ⟨3397358274414717982332551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9059622065105914619553469 3397358274414717982332551)
            ·
              refine ⟨5096037411622076973498827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397358274414717982332551 5096037411622076973498827)
              ·
                refine ⟨7644056117433115460248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096037411622076973498827 7644056117433115460248241)
                ·
                  refine ⟨5733042088074836595186181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644056117433115460248241 5733042088074836595186181)
                  ·
                    refine ⟨1074945391514031861597409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733042088074836595186181 1074945391514031861597409)
                    ·
                      rfl

theorem cell22_3140173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3140173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140173 prefixEnd_3140173 := by exact prefixLift 3140173
  have htrace : WordTrace (prefixWord ++ tailWord_3140173) baseStart_3140173 baseEnd_3140173 := by
    simpa [prefixWord, tailWord_3140173, baseEnd_3140173] using wordTrace_append hprefix tailTrace_3140173
  have hstable : (prefixWord ++ tailWord_3140173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140173).length < 2 ^ (prefixWord ++ tailWord_3140173).sum := by decide
  have hdescent : baseEnd_3140173 < baseStart_3140173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_3140274 : Nat := 118140960795 + 3140274 * 2 ^ 59
def prefixEnd_3140274 : Nat := 4983230072969 + 3 ^ 40 * 3140274 * 2
def baseEnd_3140274 : Nat := 1074979965878101264822099

theorem tailTrace_3140274 : CollatzResearch.WordTrace tailWord_3140274 prefixEnd_3140274 1074979965878101264822099 := by
  unfold tailWord_3140274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633800556332772236500969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76356801483554059297335917 28633800556332772236500969)
  ·
    refine ⟨21475350417249579177375727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28633800556332772236500969 21475350417249579177375727)
    ·
      refine ⟨32213025625874368766063591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21475350417249579177375727 32213025625874368766063591)
      ·
        refine ⟨48319538438811553149095387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32213025625874368766063591 48319538438811553149095387)
        ·
          refine ⟨72479307658217329723643081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48319538438811553149095387 72479307658217329723643081)
          ·
            refine ⟨54359480743662997292732311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72479307658217329723643081 54359480743662997292732311)
            ·
              refine ⟨81539221115494495939098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54359480743662997292732311 81539221115494495939098467)
              ·
                refine ⟨122308831673241743908647701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81539221115494495939098467 122308831673241743908647701)
                ·
                  refine ⟨5733226484683206745717861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122308831673241743908647701 5733226484683206745717861)
                  ·
                    refine ⟨1074979965878101264822099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733226484683206745717861 1074979965878101264822099)
                    ·
                      rfl

theorem cell22_3140274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_3140274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140274 prefixEnd_3140274 := by exact prefixLift 3140274
  have htrace : WordTrace (prefixWord ++ tailWord_3140274) baseStart_3140274 baseEnd_3140274 := by
    simpa [prefixWord, tailWord_3140274, baseEnd_3140274] using wordTrace_append hprefix tailTrace_3140274
  have hstable : (prefixWord ++ tailWord_3140274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140274).length < 2 ^ (prefixWord ++ tailWord_3140274).sum := by decide
  have hdescent : baseEnd_3140274 < baseStart_3140274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140306 : List Nat := [3, 2, 2, 2, 4, 9]
def baseStart_3140306 : Nat := 118140960795 + 3140306 * 2 ^ 59
def prefixEnd_3140306 : Nat := 4983230072969 + 3 ^ 40 * 3140306 * 2
def baseEnd_3140306 : Nat := 13271492841136590716321

theorem tailTrace_3140306 : CollatzResearch.WordTrace tailWord_3140306 prefixEnd_3140306 13271492841136590716321 := by
  unfold tailWord_3140306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28634092340303789602792193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76357579574143438940779181 28634092340303789602792193)
  ·
    refine ⟨21475569255227842202094145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28634092340303789602792193 21475569255227842202094145)
    ·
      refine ⟨16106676941420881651570609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21475569255227842202094145 16106676941420881651570609)
      ·
        refine ⟨12080007706065661238677957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16106676941420881651570609 12080007706065661238677957)
        ·
          refine ⟨2265001444887311482252117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12080007706065661238677957 2265001444887311482252117)
          ·
            refine ⟨13271492841136590716321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2265001444887311482252117 13271492841136590716321)
            ·
              rfl

theorem cell22_3140306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 9].length) (baseStart_3140306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140306 prefixEnd_3140306 := by exact prefixLift 3140306
  have htrace : WordTrace (prefixWord ++ tailWord_3140306) baseStart_3140306 baseEnd_3140306 := by
    simpa [prefixWord, tailWord_3140306, baseEnd_3140306] using wordTrace_append hprefix tailTrace_3140306
  have hstable : (prefixWord ++ tailWord_3140306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140306).length < 2 ^ (prefixWord ++ tailWord_3140306).sum := by decide
  have hdescent : baseEnd_3140306 < baseStart_3140306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140319 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3140319 : Nat := 118140960795 + 3140319 * 2 ^ 59
def prefixEnd_3140319 : Nat := 4983230072969 + 3 ^ 40 * 3140319 * 2
def baseEnd_3140319 : Nat := 1074995370297736147446961

theorem tailTrace_3140319 : CollatzResearch.WordTrace tailWord_3140319 prefixEnd_3140319 1074995370297736147446961 := by
  unfold tailWord_3140319
  simp only [CollatzResearch.WordTrace]
  refine ⟨114536843510168061631392011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76357895673445374420928007 114536843510168061631392011)
  ·
    refine ⟨171805265265252092447088017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114536843510168061631392011 171805265265252092447088017)
    ·
      refine ⟨128853948948939069335316013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171805265265252092447088017 128853948948939069335316013)
      ·
        refine ⟨48320230855852151000743505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128853948948939069335316013 48320230855852151000743505)
        ·
          refine ⟨36240173141889113250557629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48320230855852151000743505 36240173141889113250557629)
          ·
            refine ⟨13590064928208417468959111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36240173141889113250557629 13590064928208417468959111)
            ·
              refine ⟨20385097392312626203438667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590064928208417468959111 20385097392312626203438667)
              ·
                refine ⟨30577646088468939305158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20385097392312626203438667 30577646088468939305158001)
                ·
                  refine ⟨22933234566351704478868501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30577646088468939305158001 22933234566351704478868501)
                  ·
                    refine ⟨1074995370297736147446961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22933234566351704478868501 1074995370297736147446961)
                    ·
                      rfl

theorem cell22_3140319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3140319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140319 prefixEnd_3140319 := by exact prefixLift 3140319
  have htrace : WordTrace (prefixWord ++ tailWord_3140319) baseStart_3140319 baseEnd_3140319 := by
    simpa [prefixWord, tailWord_3140319, baseEnd_3140319] using wordTrace_append hprefix tailTrace_3140319
  have hstable : (prefixWord ++ tailWord_3140319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140319).length < 2 ^ (prefixWord ++ tailWord_3140319).sum := by decide
  have hdescent : baseEnd_3140319 < baseStart_3140319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140338 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3140338 : Nat := 118140960795 + 3140338 * 2 ^ 59
def prefixEnd_3140338 : Nat := 4983230072969 + 3 ^ 40 * 3140338 * 2
def baseEnd_3140338 : Nat := 1075001874386026431221903

theorem tailTrace_3140338 : CollatzResearch.WordTrace tailWord_3140338 prefixEnd_3140338 1075001874386026431221903 := by
  unfold tailWord_3140338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28634384124274806969083417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76358357664732818584222445 28634384124274806969083417)
  ·
    refine ⟨21475788093206105226812563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28634384124274806969083417 21475788093206105226812563)
    ·
      refine ⟨32213682139809157840218845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21475788093206105226812563 32213682139809157840218845)
      ·
        refine ⟨12080130802428434190082067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32213682139809157840218845 12080130802428434190082067)
        ·
          refine ⟨18120196203642651285123101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080130802428434190082067 18120196203642651285123101)
          ·
            refine ⟨6795073576365994231921163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18120196203642651285123101 6795073576365994231921163)
            ·
              refine ⟨10192610364548991347881745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795073576365994231921163 10192610364548991347881745)
              ·
                refine ⟨7644457773411743510911309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10192610364548991347881745 7644457773411743510911309)
                ·
                  refine ⟨2866671665029403816591741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7644457773411743510911309 2866671665029403816591741)
                  ·
                    refine ⟨1075001874386026431221903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866671665029403816591741 1075001874386026431221903)
                    ·
                      rfl

theorem cell22_3140338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3140338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140338 prefixEnd_3140338 := by exact prefixLift 3140338
  have htrace : WordTrace (prefixWord ++ tailWord_3140338) baseStart_3140338 baseEnd_3140338 := by
    simpa [prefixWord, tailWord_3140338, baseEnd_3140338] using wordTrace_append hprefix tailTrace_3140338
  have hstable : (prefixWord ++ tailWord_3140338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140338).length < 2 ^ (prefixWord ++ tailWord_3140338).sum := by decide
  have hdescent : baseEnd_3140338 < baseStart_3140338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
