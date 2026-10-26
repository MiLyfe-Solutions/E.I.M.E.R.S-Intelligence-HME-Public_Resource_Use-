import V185TrunkScan22Chunk113

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1022126 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1022126 : Nat := 118140960795 + 1022126 * 2 ^ 59
def prefixEnd_1022126 : Nat := 4983230072969 + 3 ^ 40 * 1022126 * 2
def baseEnd_1022126 : Nat := 349894618305048774016223

theorem tailTrace_1022126 : CollatzResearch.WordTrace tailWord_1022126 prefixEnd_1022126 349894618305048774016223 := by
  unfold tailWord_1022126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659999736877442758507779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24853331930013028045374821 4659999736877442758507779)
  ·
    refine ⟨6989999605316164137761669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4659999736877442758507779 6989999605316164137761669)
    ·
      refine ⟨1310624925996780775830313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6989999605316164137761669 1310624925996780775830313)
      ·
        refine ⟨982968694497585581872735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310624925996780775830313 982968694497585581872735)
        ·
          refine ⟨1474453041746378372809103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982968694497585581872735 1474453041746378372809103)
          ·
            refine ⟨2211679562619567559213655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474453041746378372809103 2211679562619567559213655)
            ·
              refine ⟨3317519343929351338820483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211679562619567559213655 3317519343929351338820483)
              ·
                refine ⟨4976279015894027008230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317519343929351338820483 4976279015894027008230725)
                ·
                  refine ⟨933052315480130064043261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4976279015894027008230725 933052315480130064043261)
                  ·
                    refine ⟨349894618305048774016223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933052315480130064043261 349894618305048774016223)
                    ·
                      rfl

theorem cell22_1022126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1022126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022126 prefixEnd_1022126 := by exact prefixLift 1022126
  have htrace : WordTrace (prefixWord ++ tailWord_1022126) baseStart_1022126 baseEnd_1022126 := by
    simpa [prefixWord, tailWord_1022126, baseEnd_1022126] using wordTrace_append hprefix tailTrace_1022126
  have hstable : (prefixWord ++ tailWord_1022126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022126).length < 2 ^ (prefixWord ++ tailWord_1022126).sum := by decide
  have hdescent : baseEnd_1022126 < baseStart_1022126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022137 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_1022137 : Nat := 118140960795 + 1022137 * 2 ^ 59
def prefixEnd_1022137 : Nat := 4983230072969 + 3 ^ 40 * 1022137 * 2
def baseEnd_1022137 : Nat := 349898383829848411991189

theorem tailTrace_1022137 : CollatzResearch.WordTrace tailWord_1022137 prefixEnd_1022137 349898383829848411991189 := by
  unfold tailWord_1022137
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280399097979690946712665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24853599398653127297808443 37280399097979690946712665)
  ·
    refine ⟨27960299323484768210034499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37280399097979690946712665 27960299323484768210034499)
    ·
      refine ⟨41940448985227152315051749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27960299323484768210034499 41940448985227152315051749)
      ·
        refine ⟨7863834184730091059072203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41940448985227152315051749 7863834184730091059072203)
        ·
          refine ⟨11795751277095136588608305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863834184730091059072203 11795751277095136588608305)
          ·
            refine ⟨8846813457821352441456229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11795751277095136588608305 8846813457821352441456229)
            ·
              refine ⟨1658777523341503582773043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8846813457821352441456229 1658777523341503582773043)
              ·
                refine ⟨2488166285012255374159565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658777523341503582773043 2488166285012255374159565)
                ·
                  refine ⟨933062356879595765309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2488166285012255374159565 933062356879595765309837)
                  ·
                    refine ⟨349898383829848411991189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933062356879595765309837 349898383829848411991189)
                    ·
                      rfl

theorem cell22_1022137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_1022137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022137 prefixEnd_1022137 := by exact prefixLift 1022137
  have htrace : WordTrace (prefixWord ++ tailWord_1022137) baseStart_1022137 baseEnd_1022137 := by
    simpa [prefixWord, tailWord_1022137, baseEnd_1022137] using wordTrace_append hprefix tailTrace_1022137
  have hstable : (prefixWord ++ tailWord_1022137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022137).length < 2 ^ (prefixWord ++ tailWord_1022137).sum := by decide
  have hdescent : baseEnd_1022137 < baseStart_1022137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022156 : List Nat := [2, 2, 1, 6, 2, 1, 2, 6]
def baseStart_1022156 : Nat := 118140960795 + 1022156 * 2 ^ 59
def prefixEnd_1022156 : Nat := 4983230072969 + 3 ^ 40 * 1022156 * 2
def baseEnd_1022156 : Nat := 38878320879793188418459

theorem tailTrace_1022156 : CollatzResearch.WordTrace tailWord_1022156 prefixEnd_1022156 38878320879793188418459 := by
  unfold tailWord_1022156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640546042455428595827161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24854061389940571461102881 18640546042455428595827161)
  ·
    refine ⟨13980409531841571446870371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18640546042455428595827161 13980409531841571446870371)
    ·
      refine ⟨20970614297762357170305557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980409531841571446870371 20970614297762357170305557)
      ·
        refine ⟨982997545207610492358073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20970614297762357170305557 982997545207610492358073)
        ·
          refine ⟨737248158905707869268555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982997545207610492358073 737248158905707869268555)
          ·
            refine ⟨1105872238358561803902833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737248158905707869268555 1105872238358561803902833)
            ·
              refine ⟨829404178768921352927125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105872238358561803902833 829404178768921352927125)
              ·
                refine ⟨38878320879793188418459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 829404178768921352927125 38878320879793188418459)
                ·
                  rfl

theorem cell22_1022156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_1022156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022156 prefixEnd_1022156 := by exact prefixLift 1022156
  have htrace : WordTrace (prefixWord ++ tailWord_1022156) baseStart_1022156 baseEnd_1022156 := by
    simpa [prefixWord, tailWord_1022156, baseEnd_1022156] using wordTrace_append hprefix tailTrace_1022156
  have hstable : (prefixWord ++ tailWord_1022156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022156).length < 2 ^ (prefixWord ++ tailWord_1022156).sum := by decide
  have hdescent : baseEnd_1022156 < baseStart_1022156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022180 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1022180 : Nat := 118140960795 + 1022180 * 2 ^ 59
def prefixEnd_1022180 : Nat := 4983230072969 + 3 ^ 40 * 1022180 * 2
def baseEnd_1022180 : Nat := 349913103608610633166057

theorem tailTrace_1022180 : CollatzResearch.WordTrace tailWord_1022180 prefixEnd_1022180 349913103608610633166057 := by
  unfold tailWord_1022180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640983718411954645263997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24854644957882606193685329 18640983718411954645263997)
  ·
    refine ⟨6990368894404482991973999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18640983718411954645263997 6990368894404482991973999)
    ·
      refine ⟨10485553341606724487960999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990368894404482991973999 10485553341606724487960999)
      ·
        refine ⟨15728330012410086731941499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485553341606724487960999 15728330012410086731941499)
        ·
          refine ⟨23592495018615130097912249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728330012410086731941499 23592495018615130097912249)
          ·
            refine ⟨17694371263961347573434187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23592495018615130097912249 17694371263961347573434187)
            ·
              refine ⟨26541556895942021360151281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694371263961347573434187 26541556895942021360151281)
              ·
                refine ⟨19906167671956516020113461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26541556895942021360151281 19906167671956516020113461)
                ·
                  refine ⟨1866203219245923376885637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19906167671956516020113461 1866203219245923376885637)
                  ·
                    refine ⟨349913103608610633166057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866203219245923376885637 349913103608610633166057)
                    ·
                      rfl

theorem cell22_1022180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1022180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022180 prefixEnd_1022180 := by exact prefixLift 1022180
  have htrace : WordTrace (prefixWord ++ tailWord_1022180) baseStart_1022180 baseEnd_1022180 := by
    simpa [prefixWord, tailWord_1022180, baseEnd_1022180] using wordTrace_append hprefix tailTrace_1022180
  have hstable : (prefixWord ++ tailWord_1022180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022180).length < 2 ^ (prefixWord ++ tailWord_1022180).sum := by decide
  have hdescent : baseEnd_1022180 < baseStart_1022180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022240 : List Nat := [2, 1, 1, 5, 2, 11]
def baseStart_1022240 : Nat := 118140960795 + 1022240 * 2 ^ 59
def prefixEnd_1022240 : Nat := 4983230072969 + 3 ^ 40 * 1022240 * 2
def baseEnd_1022240 : Nat := 4320168430059141687233

theorem tailTrace_1022240 : CollatzResearch.WordTrace tailWord_1022240 prefixEnd_1022240 4320168430059141687233 := by
  unfold tailWord_1022240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18642077908303269768856087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24856103877737693025141449 18642077908303269768856087)
  ·
    refine ⟨27963116862454904653284131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18642077908303269768856087 27963116862454904653284131)
    ·
      refine ⟨41944675293682356979926197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27963116862454904653284131 41944675293682356979926197)
      ·
        refine ⟨3932313308782720966868081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41944675293682356979926197 3932313308782720966868081)
        ·
          refine ⟨2949234981587040725151061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932313308782720966868081 2949234981587040725151061)
          ·
            refine ⟨4320168430059141687233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2949234981587040725151061 4320168430059141687233)
            ·
              rfl

theorem cell22_1022240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 11].length) (baseStart_1022240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022240 prefixEnd_1022240 := by exact prefixLift 1022240
  have htrace : WordTrace (prefixWord ++ tailWord_1022240) baseStart_1022240 baseEnd_1022240 := by
    simpa [prefixWord, tailWord_1022240, baseEnd_1022240] using wordTrace_append hprefix tailTrace_1022240
  have hstable : (prefixWord ++ tailWord_1022240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022240).length < 2 ^ (prefixWord ++ tailWord_1022240).sum := by decide
  have hdescent : baseEnd_1022240 < baseStart_1022240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022244 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1022244 : Nat := 118140960795 + 1022244 * 2 ^ 59
def prefixEnd_1022244 : Nat := 4983230072969 + 3 ^ 40 * 1022244 * 2
def baseEnd_1022244 : Nat := 349935012116535799565861

theorem tailTrace_1022244 : CollatzResearch.WordTrace tailWord_1022244 prefixEnd_1022244 349935012116535799565861 := by
  unfold tailWord_1022244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18642150854296024110428893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24856201139061365480571857 18642150854296024110428893)
  ·
    refine ⟨6990806570361009041410835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18642150854296024110428893 6990806570361009041410835)
    ·
      refine ⟨10486209855541513562116253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990806570361009041410835 10486209855541513562116253)
      ·
        refine ⟨3932328695828067585793595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10486209855541513562116253 3932328695828067585793595)
        ·
          refine ⟨5898493043742101378690393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932328695828067585793595 5898493043742101378690393)
          ·
            refine ⟨4423869782806576034017795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898493043742101378690393 4423869782806576034017795)
            ·
              refine ⟨6635804674209864051026693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423869782806576034017795 6635804674209864051026693)
              ·
                refine ⟨1244213376414349509567505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6635804674209864051026693 1244213376414349509567505)
                ·
                  refine ⟨933160032310762132175629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1244213376414349509567505 933160032310762132175629)
                  ·
                    refine ⟨349935012116535799565861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933160032310762132175629 349935012116535799565861)
                    ·
                      rfl

theorem cell22_1022244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1022244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022244 prefixEnd_1022244 := by exact prefixLift 1022244
  have htrace : WordTrace (prefixWord ++ tailWord_1022244) baseStart_1022244 baseEnd_1022244 := by
    simpa [prefixWord, tailWord_1022244, baseEnd_1022244] using wordTrace_append hprefix tailTrace_1022244
  have hstable : (prefixWord ++ tailWord_1022244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022244).length < 2 ^ (prefixWord ++ tailWord_1022244).sum := by decide
  have hdescent : baseEnd_1022244 < baseStart_1022244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022306 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1022306 : Nat := 118140960795 + 1022306 * 2 ^ 59
def prefixEnd_1022306 : Nat := 4983230072969 + 3 ^ 40 * 1022306 * 2
def baseEnd_1022306 : Nat := 349956235983588304515671

theorem tailTrace_1022306 : CollatzResearch.WordTrace tailWord_1022306 prefixEnd_1022306 349956235983588304515671 := by
  unfold tailWord_1022306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321640758591858202403693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24857708689578288539743181 9321640758591858202403693)
  ·
    refine ⟨3495615284471946825901385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9321640758591858202403693 3495615284471946825901385)
    ·
      refine ⟨2621711463353960119426039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3495615284471946825901385 2621711463353960119426039)
      ·
        refine ⟨3932567195030940179139059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621711463353960119426039 3932567195030940179139059)
        ·
          refine ⟨5898850792546410268708589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932567195030940179139059 5898850792546410268708589)
          ·
            refine ⟨2212069047204903850765721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5898850792546410268708589 2212069047204903850765721)
            ·
              refine ⟨1659051785403677888074291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212069047204903850765721 1659051785403677888074291)
              ·
                refine ⟨2488577678105516832111437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659051785403677888074291 2488577678105516832111437)
                ·
                  refine ⟨933216629289568812041789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2488577678105516832111437 933216629289568812041789)
                  ·
                    refine ⟨349956235983588304515671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933216629289568812041789 349956235983588304515671)
                    ·
                      rfl

theorem cell22_1022306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1022306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022306 prefixEnd_1022306 := by exact prefixLift 1022306
  have htrace : WordTrace (prefixWord ++ tailWord_1022306) baseStart_1022306 baseEnd_1022306 := by
    simpa [prefixWord, tailWord_1022306, baseEnd_1022306] using wordTrace_append hprefix tailTrace_1022306
  have hstable : (prefixWord ++ tailWord_1022306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022306).length < 2 ^ (prefixWord ++ tailWord_1022306).sum := by decide
  have hdescent : baseEnd_1022306 < baseStart_1022306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022317 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1022317 : Nat := 118140960795 + 1022317 * 2 ^ 59
def prefixEnd_1022317 : Nat := 4983230072969 + 3 ^ 40 * 1022317 * 2
def baseEnd_1022317 : Nat := 349960001508387942490637

theorem tailTrace_1022317 : CollatzResearch.WordTrace tailWord_1022317 prefixEnd_1022317 349960001508387942490637 := by
  unfold tailWord_1022317
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286964237327581688265205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24857976158218387792176803 37286964237327581688265205)
  ·
    refine ⟨3495652897249460783274863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37286964237327581688265205 3495652897249460783274863)
    ·
      refine ⟨5243479345874191174912295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495652897249460783274863 5243479345874191174912295)
      ·
        refine ⟨7865219018811286762368443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243479345874191174912295 7865219018811286762368443)
        ·
          refine ⟨11797828528216930143552665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865219018811286762368443 11797828528216930143552665)
          ·
            refine ⟨8848371396162697607664499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797828528216930143552665 8848371396162697607664499)
            ·
              refine ⟨13272557094244046411496749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848371396162697607664499 13272557094244046411496749)
              ·
                refine ⟨4977208910341517404311281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13272557094244046411496749 4977208910341517404311281)
                ·
                  refine ⟨3732906682756138053233461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977208910341517404311281 3732906682756138053233461)
                  ·
                    refine ⟨349960001508387942490637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3732906682756138053233461 349960001508387942490637)
                    ·
                      rfl

theorem cell22_1022317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1022317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022317 prefixEnd_1022317 := by exact prefixLift 1022317
  have htrace : WordTrace (prefixWord ++ tailWord_1022317) baseStart_1022317 baseEnd_1022317 := by
    simpa [prefixWord, tailWord_1022317, baseEnd_1022317] using wordTrace_append hprefix tailTrace_1022317
  have hstable : (prefixWord ++ tailWord_1022317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022317).length < 2 ^ (prefixWord ++ tailWord_1022317).sum := by decide
  have hdescent : baseEnd_1022317 < baseStart_1022317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022424 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1022424 : Nat := 118140960795 + 1022424 * 2 ^ 59
def prefixEnd_1022424 : Nat := 4983230072969 + 3 ^ 40 * 1022424 * 2
def baseEnd_1022424 : Nat := 349996629795075330065309

theorem tailTrace_1022424 : CollatzResearch.WordTrace tailWord_1022424 prefixEnd_1022424 349996629795075330065309 := by
  unfold tailWord_1022424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645433423969969481205163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24860577898626625974940217 18645433423969969481205163)
  ·
    refine ⟨27968150135954954221807745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18645433423969969481205163 27968150135954954221807745)
    ·
      refine ⟨20976112601966215666355809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27968150135954954221807745 20976112601966215666355809)
      ·
        refine ⟨15732084451474661749766857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20976112601966215666355809 15732084451474661749766857)
        ·
          refine ⟨11799063338605996312325143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15732084451474661749766857 11799063338605996312325143)
          ·
            refine ⟨17698595007908994468487715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11799063338605996312325143 17698595007908994468487715)
            ·
              refine ⟨26547892511863491702731573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698595007908994468487715 26547892511863491702731573)
              ·
                refine ⟨2488864922987202347131085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26547892511863491702731573 2488864922987202347131085)
                ·
                  refine ⟨933324346120200880174157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2488864922987202347131085 933324346120200880174157)
                  ·
                    refine ⟨349996629795075330065309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933324346120200880174157 349996629795075330065309)
                    ·
                      rfl

theorem cell22_1022424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1022424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022424 prefixEnd_1022424 := by exact prefixLift 1022424
  have htrace : WordTrace (prefixWord ++ tailWord_1022424) baseStart_1022424 baseEnd_1022424 := by
    simpa [prefixWord, tailWord_1022424, baseEnd_1022424] using wordTrace_append hprefix tailTrace_1022424
  have hstable : (prefixWord ++ tailWord_1022424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022424).length < 2 ^ (prefixWord ++ tailWord_1022424).sum := by decide
  have hdescent : baseEnd_1022424 < baseStart_1022424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022454 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1022454 : Nat := 118140960795 + 1022454 * 2 ^ 59
def prefixEnd_1022454 : Nat := 4983230072969 + 3 ^ 40 * 1022454 * 2
def baseEnd_1022454 : Nat := 116668966469388417271739

theorem tailTrace_1022454 : CollatzResearch.WordTrace tailWord_1022454 prefixEnd_1022454 116668966469388417271739 := by
  unfold tailWord_1022454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330747564864453380375151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24861307358554169390668277 2330747564864453380375151)
  ·
    refine ⟨3496121347296680070562727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330747564864453380375151 3496121347296680070562727)
    ·
      refine ⟨5244182020945020105844091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496121347296680070562727 5244182020945020105844091)
      ·
        refine ⟨7866273031417530158766137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244182020945020105844091 7866273031417530158766137)
        ·
          refine ⟨5899704773563147619074603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7866273031417530158766137 5899704773563147619074603)
          ·
            refine ⟨8849557160344721428611905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899704773563147619074603 8849557160344721428611905)
            ·
              refine ⟨6637167870258541071458929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8849557160344721428611905 6637167870258541071458929)
              ·
                refine ⟨4977875902693905803594197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637167870258541071458929 4977875902693905803594197)
                ·
                  refine ⟨116668966469388417271739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4977875902693905803594197 116668966469388417271739)
                  ·
                    rfl

theorem cell22_1022454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1022454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022454 prefixEnd_1022454 := by exact prefixLift 1022454
  have htrace : WordTrace (prefixWord ++ tailWord_1022454) baseStart_1022454 baseEnd_1022454 := by
    simpa [prefixWord, tailWord_1022454, baseEnd_1022454] using wordTrace_append hprefix tailTrace_1022454
  have hstable : (prefixWord ++ tailWord_1022454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022454).length < 2 ^ (prefixWord ++ tailWord_1022454).sum := by decide
  have hdescent : baseEnd_1022454 < baseStart_1022454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022499 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 6]
def baseStart_1022499 : Nat := 118140960795 + 1022499 * 2 ^ 59
def prefixEnd_1022499 : Nat := 4983230072969 + 3 ^ 40 * 1022499 * 2
def baseEnd_1022499 : Nat := 116674101275933378146693

theorem tailTrace_1022499 : CollatzResearch.WordTrace tailWord_1022499 prefixEnd_1022499 116674101275933378146693 := by
  unfold tailWord_1022499
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293602322668226771390551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24862401548445484514260367 37293602322668226771390551)
  ·
    refine ⟨55940403484002340157085827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37293602322668226771390551 55940403484002340157085827)
    ·
      refine ⟨83910605226003510235628741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55940403484002340157085827 83910605226003510235628741)
      ·
        refine ⟨15733238479875658169180389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83910605226003510235628741 15733238479875658169180389)
        ·
          refine ⟨2949982214976685906721323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15733238479875658169180389 2949982214976685906721323)
          ·
            refine ⟨4424973322465028860081985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949982214976685906721323 4424973322465028860081985)
            ·
              refine ⟨3318729991848771645061489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424973322465028860081985 3318729991848771645061489)
              ·
                refine ⟨2489047493886578733796117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318729991848771645061489 2489047493886578733796117)
                ·
                  refine ⟨116674101275933378146693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2489047493886578733796117 116674101275933378146693)
                  ·
                    rfl

theorem cell22_1022499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_1022499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022499 prefixEnd_1022499 := by exact prefixLift 1022499
  have htrace : WordTrace (prefixWord ++ tailWord_1022499) baseStart_1022499 baseEnd_1022499 := by
    simpa [prefixWord, tailWord_1022499, baseEnd_1022499] using wordTrace_append hprefix tailTrace_1022499
  have hstable : (prefixWord ++ tailWord_1022499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022499).length < 2 ^ (prefixWord ++ tailWord_1022499).sum := by decide
  have hdescent : baseEnd_1022499 < baseStart_1022499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022514 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1022514 : Nat := 118140960795 + 1022514 * 2 ^ 59
def prefixEnd_1022514 : Nat := 4983230072969 + 3 ^ 40 * 1022514 * 2
def baseEnd_1022514 : Nat := 350027438634345095315033

theorem tailTrace_1022514 : CollatzResearch.WordTrace tailWord_1022514 prefixEnd_1022514 350027438634345095315033 := by
  unfold tailWord_1022514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323537354403471083296649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24862766278409256222124397 9323537354403471083296649)
  ·
    refine ⟨6992653015802603312472487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9323537354403471083296649 6992653015802603312472487)
    ·
      refine ⟨10488979523703904968708731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6992653015802603312472487 10488979523703904968708731)
      ·
        refine ⟨15733469285555857453063097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10488979523703904968708731 15733469285555857453063097)
        ·
          refine ⟨11800101964166893089797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15733469285555857453063097 11800101964166893089797323)
          ·
            refine ⟨17700152946250339634695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800101964166893089797323 17700152946250339634695985)
            ·
              refine ⟨13275114709687754726021989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17700152946250339634695985 13275114709687754726021989)
              ·
                refine ⟨2489084008066454011129123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13275114709687754726021989 2489084008066454011129123)
                ·
                  refine ⟨3733626012099681016693685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489084008066454011129123 3733626012099681016693685)
                  ·
                    refine ⟨350027438634345095315033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3733626012099681016693685 350027438634345095315033)
                    ·
                      rfl

theorem cell22_1022514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1022514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022514 prefixEnd_1022514 := by exact prefixLift 1022514
  have htrace : WordTrace (prefixWord ++ tailWord_1022514) baseStart_1022514 baseEnd_1022514 := by
    simpa [prefixWord, tailWord_1022514, baseEnd_1022514] using wordTrace_append hprefix tailTrace_1022514
  have hstable : (prefixWord ++ tailWord_1022514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022514).length < 2 ^ (prefixWord ++ tailWord_1022514).sum := by decide
  have hdescent : baseEnd_1022514 < baseStart_1022514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022518 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1022518 : Nat := 118140960795 + 1022518 * 2 ^ 59
def prefixEnd_1022518 : Nat := 4983230072969 + 3 ^ 40 * 1022518 * 2
def baseEnd_1022518 : Nat := 350028807916090418215021

theorem tailTrace_1022518 : CollatzResearch.WordTrace tailWord_1022518 prefixEnd_1022518 350028807916090418215021 := by
  unfold tailWord_1022518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330893456849962063520763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24862863539732928677554805 2330893456849962063520763)
  ·
    refine ⟨3496340185274943095281145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330893456849962063520763 3496340185274943095281145)
    ·
      refine ⟨2622255138956207321460859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3496340185274943095281145 2622255138956207321460859)
      ·
        refine ⟨3933382708434310982191289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622255138956207321460859 3933382708434310982191289)
        ·
          refine ⟨2950037031325733236643467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933382708434310982191289 2950037031325733236643467)
          ·
            refine ⟨4425055546988599854965201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950037031325733236643467 4425055546988599854965201)
            ·
              refine ⟨3318791660241449891223901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425055546988599854965201 3318791660241449891223901)
              ·
                refine ⟨1244546872590543709208963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3318791660241449891223901 1244546872590543709208963)
                ·
                  refine ⟨1866820308885815563813445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244546872590543709208963 1866820308885815563813445)
                  ·
                    refine ⟨350028807916090418215021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866820308885815563813445 350028807916090418215021)
                    ·
                      rfl

theorem cell22_1022518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1022518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022518 prefixEnd_1022518 := by exact prefixLift 1022518
  have htrace : WordTrace (prefixWord ++ tailWord_1022518) baseStart_1022518 baseEnd_1022518 := by
    simpa [prefixWord, tailWord_1022518, baseEnd_1022518] using wordTrace_append hprefix tailTrace_1022518
  have hstable : (prefixWord ++ tailWord_1022518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022518).length < 2 ^ (prefixWord ++ tailWord_1022518).sum := by decide
  have hdescent : baseEnd_1022518 < baseStart_1022518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022533 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1022533 : Nat := 118140960795 + 1022533 * 2 ^ 59
def prefixEnd_1022533 : Nat := 4983230072969 + 3 ^ 40 * 1022533 * 2
def baseEnd_1022533 : Nat := 116677980907545126363325

theorem tailTrace_1022533 : CollatzResearch.WordTrace tailWord_1022533 prefixEnd_1022533 116677980907545126363325 := by
  unfold tailWord_1022533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37294842404545050578128253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24863228269696700385418835 37294842404545050578128253)
  ·
    refine ⟨13985565901704393966798095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37294842404545050578128253 13985565901704393966798095)
    ·
      refine ⟨20978348852556590950197143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13985565901704393966798095 20978348852556590950197143)
      ·
        refine ⟨31467523278834886425295715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20978348852556590950197143 31467523278834886425295715)
        ·
          refine ⟨47201284918252329637943573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31467523278834886425295715 47201284918252329637943573)
          ·
            refine ⟨2212560230543077951778605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47201284918252329637943573 2212560230543077951778605)
            ·
              refine ⟨829710086453654231916977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212560230543077951778605 829710086453654231916977)
              ·
                refine ⟨622282564840240673937733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829710086453654231916977 622282564840240673937733)
                ·
                  refine ⟨116677980907545126363325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622282564840240673937733 116677980907545126363325)
                  ·
                    rfl

theorem cell22_1022533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1022533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022533 prefixEnd_1022533 := by exact prefixLift 1022533
  have htrace : WordTrace (prefixWord ++ tailWord_1022533) baseStart_1022533 baseEnd_1022533 := by
    simpa [prefixWord, tailWord_1022533, baseEnd_1022533] using wordTrace_append hprefix tailTrace_1022533
  have hstable : (prefixWord ++ tailWord_1022533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022533).length < 2 ^ (prefixWord ++ tailWord_1022533).sum := by decide
  have hdescent : baseEnd_1022533 < baseStart_1022533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022548 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1022548 : Nat := 118140960795 + 1022548 * 2 ^ 59
def prefixEnd_1022548 : Nat := 4983230072969 + 3 ^ 40 * 1022548 * 2
def baseEnd_1022548 : Nat := 350039077529180339964929

theorem tailTrace_1022548 : CollatzResearch.WordTrace tailWord_1022548 prefixEnd_1022548 350039077529180339964929 := by
  unfold tailWord_1022548
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647694749745354069962149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24863592999660472093282865 18647694749745354069962149)
  ·
    refine ⟨3496442765577253888117903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18647694749745354069962149 3496442765577253888117903)
    ·
      refine ⟨5244664148365880832176855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496442765577253888117903 5244664148365880832176855)
      ·
        refine ⟨7866996222548821248265283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244664148365880832176855 7866996222548821248265283)
        ·
          refine ⟨11800494333823231872397925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866996222548821248265283 11800494333823231872397925)
          ·
            refine ⟨2212592687591855976074611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11800494333823231872397925 2212592687591855976074611)
            ·
              refine ⟨3318889031387783964111917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212592687591855976074611 3318889031387783964111917)
              ·
                refine ⟨1244583386770418986541969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3318889031387783964111917 1244583386770418986541969)
                ·
                  refine ⟨933437540077814239906477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1244583386770418986541969 933437540077814239906477)
                  ·
                    refine ⟨350039077529180339964929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933437540077814239906477 350039077529180339964929)
                    ·
                      rfl

theorem cell22_1022548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1022548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022548 prefixEnd_1022548 := by exact prefixLift 1022548
  have htrace : WordTrace (prefixWord ++ tailWord_1022548) baseStart_1022548 baseEnd_1022548 := by
    simpa [prefixWord, tailWord_1022548, baseEnd_1022548] using wordTrace_append hprefix tailTrace_1022548
  have hstable : (prefixWord ++ tailWord_1022548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022548).length < 2 ^ (prefixWord ++ tailWord_1022548).sum := by decide
  have hdescent : baseEnd_1022548 < baseStart_1022548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022606 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1022606 : Nat := 118140960795 + 1022606 * 2 ^ 59
def prefixEnd_1022606 : Nat := 4983230072969 + 3 ^ 40 * 1022606 * 2
def baseEnd_1022606 : Nat := 116686310704829174004917

theorem tailTrace_1022606 : CollatzResearch.WordTrace tailWord_1022606 prefixEnd_1022606 116686310704829174004917 := by
  unfold tailWord_1022606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662188116660073005691959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24865003288853722697023781 4662188116660073005691959)
  ·
    refine ⟨6993282174990109508537939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662188116660073005691959 6993282174990109508537939)
    ·
      refine ⟨10489923262485164262806909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993282174990109508537939 10489923262485164262806909)
      ·
        refine ⟨3933721223431936598552591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10489923262485164262806909 3933721223431936598552591)
        ·
          refine ⟨5900581835147904897828887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933721223431936598552591 5900581835147904897828887)
          ·
            refine ⟨8850872752721857346743331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900581835147904897828887 8850872752721857346743331)
            ·
              refine ⟨13276309129082786020114997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850872752721857346743331 13276309129082786020114997)
              ·
                refine ⟨1244653980851511189385781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13276309129082786020114997 1244653980851511189385781)
                ·
                  refine ⟨116686310704829174004917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1244653980851511189385781 116686310704829174004917)
                  ·
                    rfl

theorem cell22_1022606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1022606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022606 prefixEnd_1022606 := by exact prefixLift 1022606
  have htrace : WordTrace (prefixWord ++ tailWord_1022606) baseStart_1022606 baseEnd_1022606 := by
    simpa [prefixWord, tailWord_1022606, baseEnd_1022606] using wordTrace_append hprefix tailTrace_1022606
  have hstable : (prefixWord ++ tailWord_1022606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022606).length < 2 ^ (prefixWord ++ tailWord_1022606).sum := by decide
  have hdescent : baseEnd_1022606 < baseStart_1022606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022638 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1022638 : Nat := 118140960795 + 1022638 * 2 ^ 59
def prefixEnd_1022638 : Nat := 4983230072969 + 3 ^ 40 * 1022638 * 2
def baseEnd_1022638 : Nat := 350069886368450105214653

theorem tailTrace_1022638 : CollatzResearch.WordTrace tailWord_1022638 prefixEnd_1022638 350069886368450105214653 := by
  unfold tailWord_1022638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662334008645581688837571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24865781379443102340467045 4662334008645581688837571)
  ·
    refine ⟨6993501012968372533256357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662334008645581688837571 6993501012968372533256357)
    ·
      refine ⟨1311281439931569849985567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6993501012968372533256357 1311281439931569849985567)
      ·
        refine ⟨1966922159897354774978351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311281439931569849985567 1966922159897354774978351)
        ·
          refine ⟨2950383239846032162467527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966922159897354774978351 2950383239846032162467527)
          ·
            refine ⟨4425574859769048243701291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950383239846032162467527 4425574859769048243701291)
            ·
              refine ⟨6638362289653572365551937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425574859769048243701291 6638362289653572365551937)
              ·
                refine ⟨4978771717240179274163953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638362289653572365551937 4978771717240179274163953)
                ·
                  refine ⟨3734078787930134455622965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4978771717240179274163953 3734078787930134455622965)
                  ·
                    refine ⟨350069886368450105214653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3734078787930134455622965 350069886368450105214653)
                    ·
                      rfl

theorem cell22_1022638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1022638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022638 prefixEnd_1022638 := by exact prefixLift 1022638
  have htrace : WordTrace (prefixWord ++ tailWord_1022638) baseStart_1022638 baseEnd_1022638 := by
    simpa [prefixWord, tailWord_1022638, baseEnd_1022638] using wordTrace_append hprefix tailTrace_1022638
  have hstable : (prefixWord ++ tailWord_1022638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022638).length < 2 ^ (prefixWord ++ tailWord_1022638).sum := by decide
  have hdescent : baseEnd_1022638 < baseStart_1022638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022657 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 5]
def baseStart_1022657 : Nat := 118140960795 + 1022657 * 2 ^ 59
def prefixEnd_1022657 : Nat := 4983230072969 + 3 ^ 40 * 1022657 * 2
def baseEnd_1022657 : Nat := 116692130152246796329865

theorem tailTrace_1022657 : CollatzResearch.WordTrace tailWord_1022657 prefixEnd_1022657 116692130152246796329865 := by
  unfold tailWord_1022657
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299365056095819755642225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24866243370730546503761483 37299365056095819755642225)
  ·
    refine ⟨27974523792071864816731669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37299365056095819755642225 27974523792071864816731669)
    ·
      refine ⟨1311305802753368663284297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27974523792071864816731669 1311305802753368663284297)
      ·
        refine ⟨983479352065026497463223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311305802753368663284297 983479352065026497463223)
        ·
          refine ⟨1475219028097539746194835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983479352065026497463223 1475219028097539746194835)
          ·
            refine ⟨2212828542146309619292253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475219028097539746194835 2212828542146309619292253)
            ·
              refine ⟨829810703304866107234595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212828542146309619292253 829810703304866107234595)
              ·
                refine ⟨1244716054957299160851893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829810703304866107234595 1244716054957299160851893)
                ·
                  refine ⟨116692130152246796329865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1244716054957299160851893 116692130152246796329865)
                  ·
                    rfl

theorem cell22_1022657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_1022657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022657 prefixEnd_1022657 := by exact prefixLift 1022657
  have htrace : WordTrace (prefixWord ++ tailWord_1022657) baseStart_1022657 baseEnd_1022657 := by
    simpa [prefixWord, tailWord_1022657, baseEnd_1022657] using wordTrace_append hprefix tailTrace_1022657
  have hstable : (prefixWord ++ tailWord_1022657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022657).length < 2 ^ (prefixWord ++ tailWord_1022657).sum := by decide
  have hdescent : baseEnd_1022657 < baseStart_1022657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022681 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_1022681 : Nat := 118140960795 + 1022681 * 2 ^ 59
def prefixEnd_1022681 : Nat := 4983230072969 + 3 ^ 40 * 1022681 * 2
def baseEnd_1022681 : Nat := 350084606147212326389521

theorem tailTrace_1022681 : CollatzResearch.WordTrace tailWord_1022681 prefixEnd_1022681 350084606147212326389521 := by
  unfold tailWord_1022681
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300240408008871854515897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24866826938672581236343931 37300240408008871854515897)
  ·
    refine ⟨27975180306006653890886923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37300240408008871854515897 27975180306006653890886923)
    ·
      refine ⟨41962770459009980836330385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27975180306006653890886923 41962770459009980836330385)
      ·
        refine ⟨31472077844257485627247789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41962770459009980836330385 31472077844257485627247789)
        ·
          refine ⟨11802029191596557110217921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31472077844257485627247789 11802029191596557110217921)
          ·
            refine ⟨8851521893697417832663441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802029191596557110217921 8851521893697417832663441)
            ·
              refine ⟨6638641420273063374497581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851521893697417832663441 6638641420273063374497581)
              ·
                refine ⟨2489490532602398765436593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6638641420273063374497581 2489490532602398765436593)
                ·
                  refine ⟨1867117899451799074077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489490532602398765436593 1867117899451799074077445)
                  ·
                    refine ⟨350084606147212326389521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867117899451799074077445 350084606147212326389521)
                    ·
                      rfl

theorem cell22_1022681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_1022681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022681 prefixEnd_1022681 := by exact prefixLift 1022681
  have htrace : WordTrace (prefixWord ++ tailWord_1022681) baseStart_1022681 baseEnd_1022681 := by
    simpa [prefixWord, tailWord_1022681, baseEnd_1022681] using wordTrace_append hprefix tailTrace_1022681
  have hstable : (prefixWord ++ tailWord_1022681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022681).length < 2 ^ (prefixWord ++ tailWord_1022681).sum := by decide
  have hdescent : baseEnd_1022681 < baseStart_1022681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022773 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1022773 : Nat := 118140960795 + 1022773 * 2 ^ 59
def prefixEnd_1022773 : Nat := 4983230072969 + 3 ^ 40 * 1022773 * 2
def baseEnd_1022773 : Nat := 350116099627354753089239

theorem tailTrace_1022773 : CollatzResearch.WordTrace tailWord_1022773 prefixEnd_1022773 350116099627354753089239 := by
  unfold tailWord_1022773
  simp only [CollatzResearch.WordTrace]
  refine ⟨37303595923675571566864973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24869063949117047711243315 37303595923675571566864973)
  ·
    refine ⟨13988848471378339337574365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37303595923675571566864973 13988848471378339337574365)
    ·
      refine ⟨5245818176766877251590387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13988848471378339337574365 5245818176766877251590387)
      ·
        refine ⟨7868727265150315877385581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245818176766877251590387 7868727265150315877385581)
        ·
          refine ⟨2950772724431368454019593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7868727265150315877385581 2950772724431368454019593)
          ·
            refine ⟨2213079543323526340514695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950772724431368454019593 2213079543323526340514695)
            ·
              refine ⟨3319619314985289510772043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213079543323526340514695 3319619314985289510772043)
              ·
                refine ⟨4979428972477934266158065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319619314985289510772043 4979428972477934266158065)
                ·
                  refine ⟨3734571729358450699618549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979428972477934266158065 3734571729358450699618549)
                  ·
                    refine ⟨350116099627354753089239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3734571729358450699618549 350116099627354753089239)
                    ·
                      rfl

theorem cell22_1022773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1022773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022773 prefixEnd_1022773 := by exact prefixLift 1022773
  have htrace : WordTrace (prefixWord ++ tailWord_1022773) baseStart_1022773 baseEnd_1022773 := by
    simpa [prefixWord, tailWord_1022773, baseEnd_1022773] using wordTrace_append hprefix tailTrace_1022773
  have hstable : (prefixWord ++ tailWord_1022773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022773).length < 2 ^ (prefixWord ++ tailWord_1022773).sum := by decide
  have hdescent : baseEnd_1022773 < baseStart_1022773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022820 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1022820 : Nat := 118140960795 + 1022820 * 2 ^ 59
def prefixEnd_1022820 : Nat := 4983230072969 + 3 ^ 40 * 1022820 * 2
def baseEnd_1022820 : Nat := 116710729562620765721365

theorem tailTrace_1022820 : CollatzResearch.WordTrace tailWord_1022820 prefixEnd_1022820 116710729562620765721365 := by
  unfold tailWord_1022820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18652655077252649296912957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24870206769670199062550609 18652655077252649296912957)
  ·
    refine ⟨6994745653969743486342359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18652655077252649296912957 6994745653969743486342359)
    ·
      refine ⟨10492118480954615229513539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994745653969743486342359 10492118480954615229513539)
      ·
        refine ⟨15738177721431922844270309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492118480954615229513539 15738177721431922844270309)
        ·
          refine ⟨2950908322768485533300683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15738177721431922844270309 2950908322768485533300683)
          ·
            refine ⟨4426362484152728299951025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950908322768485533300683 4426362484152728299951025)
            ·
              refine ⟨3319771863114546224963269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4426362484152728299951025 3319771863114546224963269)
              ·
                refine ⟨622457224333977417180613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3319771863114546224963269 622457224333977417180613)
                ·
                  refine ⟨116710729562620765721365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622457224333977417180613 116710729562620765721365)
                  ·
                    rfl

theorem cell22_1022820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1022820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022820 prefixEnd_1022820 := by exact prefixLift 1022820
  have htrace : WordTrace (prefixWord ++ tailWord_1022820) baseStart_1022820 baseEnd_1022820 := by
    simpa [prefixWord, tailWord_1022820, baseEnd_1022820] using wordTrace_append hprefix tailTrace_1022820
  have hstable : (prefixWord ++ tailWord_1022820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022820).length < 2 ^ (prefixWord ++ tailWord_1022820).sum := by decide
  have hdescent : baseEnd_1022820 < baseStart_1022820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022880 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_1022880 : Nat := 118140960795 + 1022880 * 2 ^ 59
def prefixEnd_1022880 : Nat := 4983230072969 + 3 ^ 40 * 1022880 * 2
def baseEnd_1022880 : Nat := 350152727914042140663911

theorem tailTrace_1022880 : CollatzResearch.WordTrace tailWord_1022880 prefixEnd_1022880 350152727914042140663911 := by
  unfold tailWord_1022880
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653749267143964420505047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24871665689525285894006729 18653749267143964420505047)
  ·
    refine ⟨27980623900715946630757571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653749267143964420505047 27980623900715946630757571)
    ·
      refine ⟨41970935851073919946136357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27980623900715946630757571 41970935851073919946136357)
      ·
        refine ⟨7869550472076359989900567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41970935851073919946136357 7869550472076359989900567)
        ·
          refine ⟨11804325708114539984850851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869550472076359989900567 11804325708114539984850851)
          ·
            refine ⟨17706488562171809977276277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804325708114539984850851 17706488562171809977276277)
            ·
              refine ⟨1659983302703607185369651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17706488562171809977276277 1659983302703607185369651)
              ·
                refine ⟨2489974954055410778054477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659983302703607185369651 2489974954055410778054477)
                ·
                  refine ⟨933740607770779041770429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2489974954055410778054477 933740607770779041770429)
                  ·
                    refine ⟨350152727914042140663911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933740607770779041770429 350152727914042140663911)
                    ·
                      rfl

theorem cell22_1022880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_1022880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022880 prefixEnd_1022880 := by exact prefixLift 1022880
  have htrace : WordTrace (prefixWord ++ tailWord_1022880) baseStart_1022880 baseEnd_1022880 := by
    simpa [prefixWord, tailWord_1022880, baseEnd_1022880] using wordTrace_append hprefix tailTrace_1022880
  have hstable : (prefixWord ++ tailWord_1022880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022880).length < 2 ^ (prefixWord ++ tailWord_1022880).sum := by decide
  have hdescent : baseEnd_1022880 < baseStart_1022880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022972 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_1022972 : Nat := 118140960795 + 1022972 * 2 ^ 59
def prefixEnd_1022972 : Nat := 4983230072969 + 3 ^ 40 * 1022972 * 2
def baseEnd_1022972 : Nat := 116728073798061522454543

theorem tailTrace_1022972 : CollatzResearch.WordTrace tailWord_1022972 prefixEnd_1022972 116728073798061522454543 := by
  unfold tailWord_1022972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655427024977314276679585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24873902699969752368906113 18655427024977314276679585)
  ·
    refine ⟨13991570268732985707509689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18655427024977314276679585 13991570268732985707509689)
    ·
      refine ⟨10493677701549739280632267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991570268732985707509689 10493677701549739280632267)
      ·
        refine ⟨15740516552324608920948401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493677701549739280632267 15740516552324608920948401)
        ·
          refine ⟨11805387414243456690711301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15740516552324608920948401 11805387414243456690711301)
          ·
            refine ⟨2213510140170648129508369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11805387414243456690711301 2213510140170648129508369)
            ·
              refine ⟨1660132605127986097131277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213510140170648129508369 1660132605127986097131277)
              ·
                refine ⟨622549726922994786424229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1660132605127986097131277 622549726922994786424229)
                ·
                  refine ⟨116728073798061522454543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622549726922994786424229 116728073798061522454543)
                  ·
                    rfl

theorem cell22_1022972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_1022972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022972 prefixEnd_1022972 := by exact prefixLift 1022972
  have htrace : WordTrace (prefixWord ++ tailWord_1022972) baseStart_1022972 baseEnd_1022972 := by
    simpa [prefixWord, tailWord_1022972, baseEnd_1022972] using wordTrace_append hprefix tailTrace_1022972
  have hstable : (prefixWord ++ tailWord_1022972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022972).length < 2 ^ (prefixWord ++ tailWord_1022972).sum := by decide
  have hdescent : baseEnd_1022972 < baseStart_1022972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022974 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1022974 : Nat := 118140960795 + 1022974 * 2 ^ 59
def prefixEnd_1022974 : Nat := 4983230072969 + 3 ^ 40 * 1022974 * 2
def baseEnd_1022974 : Nat := 350184906035057228813623

theorem tailTrace_1022974 : CollatzResearch.WordTrace tailWord_1022974 prefixEnd_1022974 350184906035057228813623 := by
  unfold tailWord_1022974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663865874493422861866497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24873951330631588596621317 4663865874493422861866497)
  ·
    refine ⟨3497899405870067146399873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4663865874493422861866497 3497899405870067146399873)
    ·
      refine ⟨2623424554402550359799905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3497899405870067146399873 2623424554402550359799905)
      ·
        refine ⟨1967568415801912769849929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623424554402550359799905 1967568415801912769849929)
        ·
          refine ⟨1475676311851434577387447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967568415801912769849929 1475676311851434577387447)
          ·
            refine ⟨2213514467777151866081171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475676311851434577387447 2213514467777151866081171)
            ·
              refine ⟨3320271701665727799121757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213514467777151866081171 3320271701665727799121757)
              ·
                refine ⟨1245101888124647924670659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320271701665727799121757 1245101888124647924670659)
                ·
                  refine ⟨1867652832186971887005989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245101888124647924670659 1867652832186971887005989)
                  ·
                    refine ⟨350184906035057228813623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867652832186971887005989 350184906035057228813623)
                    ·
                      rfl

theorem cell22_1022974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1022974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022974 prefixEnd_1022974 := by exact prefixLift 1022974
  have htrace : WordTrace (prefixWord ++ tailWord_1022974) baseStart_1022974 baseEnd_1022974 := by
    simpa [prefixWord, tailWord_1022974, baseEnd_1022974] using wordTrace_append hprefix tailTrace_1022974
  have hstable : (prefixWord ++ tailWord_1022974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022974).length < 2 ^ (prefixWord ++ tailWord_1022974).sum := by decide
  have hdescent : baseEnd_1022974 < baseStart_1022974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022983 : List Nat := [1, 1, 4, 3, 1, 1, 11]
def baseStart_1022983 : Nat := 118140960795 + 1022983 * 2 ^ 59
def prefixEnd_1022983 : Nat := 4983230072969 + 3 ^ 40 * 1022983 * 2
def baseEnd_1022983 : Nat := 12969925441443859456985

theorem tailTrace_1022983 : CollatzResearch.WordTrace tailWord_1022983 prefixEnd_1022983 12969925441443859456985 := by
  unfold tailWord_1022983
  simp only [CollatzResearch.WordTrace]
  refine ⟨37311255252914777432009603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24874170168609851621339735 37311255252914777432009603)
  ·
    refine ⟨55966882879372166148014405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37311255252914777432009603 55966882879372166148014405)
    ·
      refine ⟨10493790539882281152752701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55966882879372166148014405 10493790539882281152752701)
      ·
        refine ⟨3935171452455855432282263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10493790539882281152752701 3935171452455855432282263)
        ·
          refine ⟨5902757178683783148423395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935171452455855432282263 5902757178683783148423395)
          ·
            refine ⟨8854135768025674722635093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902757178683783148423395 8854135768025674722635093)
            ·
              refine ⟨12969925441443859456985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8854135768025674722635093 12969925441443859456985)
              ·
                rfl

theorem cell22_1022983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 11].length) (baseStart_1022983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022983 prefixEnd_1022983 := by exact prefixLift 1022983
  have htrace : WordTrace (prefixWord ++ tailWord_1022983) baseStart_1022983 baseEnd_1022983 := by
    simpa [prefixWord, tailWord_1022983, baseEnd_1022983] using wordTrace_append hprefix tailTrace_1022983
  have hstable : (prefixWord ++ tailWord_1022983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022983).length < 2 ^ (prefixWord ++ tailWord_1022983).sum := by decide
  have hdescent : baseEnd_1022983 < baseStart_1022983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022987 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 2, 3]
def baseStart_1022987 : Nat := 118140960795 + 1022987 * 2 ^ 59
def prefixEnd_1022987 : Nat := 4983230072969 + 3 ^ 40 * 1022987 * 2
def baseEnd_1022987 : Nat := 350189356200729528238583

theorem tailTrace_1022987 : CollatzResearch.WordTrace tailWord_1022987 prefixEnd_1022987 350189356200729528238583 := by
  unfold tailWord_1022987
  simp only [CollatzResearch.WordTrace]
  refine ⟨37311401144900286115155215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24874267429933524076770143 37311401144900286115155215)
  ·
    refine ⟨55967101717350429172732823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37311401144900286115155215 55967101717350429172732823)
    ·
      refine ⟨83950652576025643759099235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55967101717350429172732823 83950652576025643759099235)
      ·
        refine ⟨125925978864038465638648853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83950652576025643759099235 125925978864038465638648853)
        ·
          refine ⟨5902780259251803076811665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125925978864038465638648853 5902780259251803076811665)
          ·
            refine ⟨4427085194438852307608749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902780259251803076811665 4427085194438852307608749)
            ·
              refine ⟨1660156947914569615353281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4427085194438852307608749 1660156947914569615353281)
              ·
                refine ⟨1245117710935927211514961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660156947914569615353281 1245117710935927211514961)
                ·
                  refine ⟨933838283201945408636221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245117710935927211514961 933838283201945408636221)
                  ·
                    refine ⟨350189356200729528238583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 933838283201945408636221 350189356200729528238583)
                    ·
                      rfl

theorem cell22_1022987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].length) (baseStart_1022987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022987 prefixEnd_1022987 := by exact prefixLift 1022987
  have htrace : WordTrace (prefixWord ++ tailWord_1022987) baseStart_1022987 baseEnd_1022987 := by
    simpa [prefixWord, tailWord_1022987, baseEnd_1022987] using wordTrace_append hprefix tailTrace_1022987
  have hstable : (prefixWord ++ tailWord_1022987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022987).length < 2 ^ (prefixWord ++ tailWord_1022987).sum := by decide
  have hdescent : baseEnd_1022987 < baseStart_1022987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023004 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1023004 : Nat := 118140960795 + 1023004 * 2 ^ 59
def prefixEnd_1023004 : Nat := 4983230072969 + 3 ^ 40 * 1023004 * 2
def baseEnd_1023004 : Nat := 350195175648147150563531

theorem tailTrace_1023004 : CollatzResearch.WordTrace tailWord_1023004 prefixEnd_1023004 350195175648147150563531 := by
  unfold tailWord_1023004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18656010592919349009262033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24874680790559132012349377 18656010592919349009262033)
  ·
    refine ⟨13992007944689511756946525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18656010592919349009262033 13992007944689511756946525)
    ·
      refine ⟨5247002979258566908854947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13992007944689511756946525 5247002979258566908854947)
      ·
        refine ⟨7870504468887850363282421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247002979258566908854947 7870504468887850363282421)
        ·
          refine ⟨737859793958235971557727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7870504468887850363282421 737859793958235971557727)
          ·
            refine ⟨1106789690937353957336591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737859793958235971557727 1106789690937353957336591)
            ·
              refine ⟨1660184536406030936004887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106789690937353957336591 1660184536406030936004887)
              ·
                refine ⟨2490276804609046404007331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660184536406030936004887 2490276804609046404007331)
                ·
                  refine ⟨3735415206913569606010997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490276804609046404007331 3735415206913569606010997)
                  ·
                    refine ⟨350195175648147150563531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735415206913569606010997 350195175648147150563531)
                    ·
                      rfl

theorem cell22_1023004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1023004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023004 prefixEnd_1023004 := by exact prefixLift 1023004
  have htrace : WordTrace (prefixWord ++ tailWord_1023004) baseStart_1023004 baseEnd_1023004 := by
    simpa [prefixWord, tailWord_1023004, baseEnd_1023004] using wordTrace_append hprefix tailTrace_1023004
  have hstable : (prefixWord ++ tailWord_1023004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023004).length < 2 ^ (prefixWord ++ tailWord_1023004).sum := by decide
  have hdescent : baseEnd_1023004 < baseStart_1023004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023060 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1023060 : Nat := 118140960795 + 1023060 * 2 ^ 59
def prefixEnd_1023060 : Nat := 4983230072969 + 3 ^ 40 * 1023060 * 2
def baseEnd_1023060 : Nat := 350214345592581671163359

theorem tailTrace_1023060 : CollatzResearch.WordTrace tailWord_1023060 prefixEnd_1023060 350214345592581671163359 := by
  unfold tailWord_1023060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657031836817909791281317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24876042449090546388375089 18657031836817909791281317)
  ·
    refine ⟨3498193469403358085865247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18657031836817909791281317 3498193469403358085865247)
    ·
      refine ⟨5247290204105037128797871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498193469403358085865247 5247290204105037128797871)
      ·
        refine ⟨7870935306157555693196807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247290204105037128797871 7870935306157555693196807)
        ·
          refine ⟨11806402959236333539795211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870935306157555693196807 11806402959236333539795211)
          ·
            refine ⟨17709604438854500309692817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806402959236333539795211 17709604438854500309692817)
            ·
              refine ⟨13282203329140875232269613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17709604438854500309692817 13282203329140875232269613)
              ·
                refine ⟨4980826248427828212101105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13282203329140875232269613 4980826248427828212101105)
                ·
                  refine ⟨3735619686320871159075829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4980826248427828212101105 3735619686320871159075829)
                  ·
                    refine ⟨350214345592581671163359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735619686320871159075829 350214345592581671163359)
                    ·
                      rfl

theorem cell22_1023060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1023060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023060 prefixEnd_1023060 := by exact prefixLift 1023060
  have htrace : WordTrace (prefixWord ++ tailWord_1023060) baseStart_1023060 baseEnd_1023060 := by
    simpa [prefixWord, tailWord_1023060, baseEnd_1023060] using wordTrace_append hprefix tailTrace_1023060
  have hstable : (prefixWord ++ tailWord_1023060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023060).length < 2 ^ (prefixWord ++ tailWord_1023060).sum := by decide
  have hdescent : baseEnd_1023060 < baseStart_1023060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023107 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 4]
def baseStart_1023107 : Nat := 118140960795 + 1023107 * 2 ^ 59
def prefixEnd_1023107 : Nat := 4983230072969 + 3 ^ 40 * 1023107 * 2
def baseEnd_1023107 : Nat := 116743478217696405079405

theorem tailTrace_1023107 : CollatzResearch.WordTrace tailWord_1023107 prefixEnd_1023107 116743478217696405079405 := by
  unfold tailWord_1023107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315777904465546609523575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24877185269643697739682383 37315777904465546609523575)
  ·
    refine ⟨55973666856698319914285363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37315777904465546609523575 55973666856698319914285363)
    ·
      refine ⟨83960500285047479871428045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55973666856698319914285363 83960500285047479871428045)
      ·
        refine ⟨31485187606892804951785517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83960500285047479871428045 31485187606892804951785517)
        ·
          refine ⟨11806945352584801856919569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31485187606892804951785517 11806945352584801856919569)
          ·
            refine ⟨8855209014438601392689677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806945352584801856919569 8855209014438601392689677)
            ·
              refine ⟨3320703380414475522258629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8855209014438601392689677 3320703380414475522258629)
              ·
                refine ⟨622631883827714160423493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3320703380414475522258629 622631883827714160423493)
                ·
                  refine ⟨116743478217696405079405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622631883827714160423493 116743478217696405079405)
                  ·
                    rfl

theorem cell22_1023107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 4].length) (baseStart_1023107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023107 prefixEnd_1023107 := by exact prefixLift 1023107
  have htrace : WordTrace (prefixWord ++ tailWord_1023107) baseStart_1023107 baseEnd_1023107 := by
    simpa [prefixWord, tailWord_1023107, baseEnd_1023107] using wordTrace_append hprefix tailTrace_1023107
  have hstable : (prefixWord ++ tailWord_1023107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023107).length < 2 ^ (prefixWord ++ tailWord_1023107).sum := by decide
  have hdescent : baseEnd_1023107 < baseStart_1023107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023122 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1023122 : Nat := 118140960795 + 1023122 * 2 ^ 59
def prefixEnd_1023122 : Nat := 4983230072969 + 3 ^ 40 * 1023122 * 2
def baseEnd_1023122 : Nat := 350235569459634176113169

theorem tailTrace_1023122 : CollatzResearch.WordTrace tailWord_1023122 prefixEnd_1023122 350235569459634176113169 := by
  unfold tailWord_1023122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329081249852801042829905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24877549999607469447546413 9329081249852801042829905)
  ·
    refine ⟨6996810937389600782122429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9329081249852801042829905 6996810937389600782122429)
    ·
      refine ⟨2623804101521100293295911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6996810937389600782122429 2623804101521100293295911)
      ·
        refine ⟨3935706152281650439943867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623804101521100293295911 3935706152281650439943867)
        ·
          refine ⟨5903559228422475659915801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935706152281650439943867 5903559228422475659915801)
          ·
            refine ⟨4427669421316856744936851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903559228422475659915801 4427669421316856744936851)
            ·
              refine ⟨6641504131975285117405277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427669421316856744936851 6641504131975285117405277)
              ·
                refine ⟨2490564049490731919026979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6641504131975285117405277 2490564049490731919026979)
                ·
                  refine ⟨3735846074236097878540469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490564049490731919026979 3735846074236097878540469)
                  ·
                    refine ⟨350235569459634176113169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735846074236097878540469 350235569459634176113169)
                    ·
                      rfl

theorem cell22_1023122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1023122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023122 prefixEnd_1023122 := by exact prefixLift 1023122
  have htrace : WordTrace (prefixWord ++ tailWord_1023122) baseStart_1023122 baseEnd_1023122 := by
    simpa [prefixWord, tailWord_1023122, baseEnd_1023122] using wordTrace_append hprefix tailTrace_1023122
  have hstable : (prefixWord ++ tailWord_1023122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023122).length < 2 ^ (prefixWord ++ tailWord_1023122).sum := by decide
  have hdescent : baseEnd_1023122 < baseStart_1023122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023165 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1023165 : Nat := 118140960795 + 1023165 * 2 ^ 59
def prefixEnd_1023165 : Nat := 4983230072969 + 3 ^ 40 * 1023165 * 2
def baseEnd_1023165 : Nat := 350250289238396397288037

theorem tailTrace_1023165 : CollatzResearch.WordTrace tailWord_1023165 prefixEnd_1023165 350250289238396397288037 := by
  unfold tailWord_1023165
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317893338255422515134949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24878595558836948343423299 37317893338255422515134949)
  ·
    refine ⟨6997105000922891721587803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37317893338255422515134949 6997105000922891721587803)
    ·
      refine ⟨10495657501384337582381705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997105000922891721587803 10495657501384337582381705)
      ·
        refine ⟨7871743126038253186786279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10495657501384337582381705 7871743126038253186786279)
        ·
          refine ⟨11807614689057379780179419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871743126038253186786279 11807614689057379780179419)
          ·
            refine ⟨17711422033586069670269129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807614689057379780179419 17711422033586069670269129)
            ·
              refine ⟨13283566525189552252701847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17711422033586069670269129 13283566525189552252701847)
              ·
                refine ⟨19925349787784328379052771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283566525189552252701847 19925349787784328379052771)
                ·
                  refine ⟨29888024681676492568579157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19925349787784328379052771 29888024681676492568579157)
                  ·
                    refine ⟨350250289238396397288037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29888024681676492568579157 350250289238396397288037)
                    ·
                      rfl

theorem cell22_1023165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1023165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023165 prefixEnd_1023165 := by exact prefixLift 1023165
  have htrace : WordTrace (prefixWord ++ tailWord_1023165) baseStart_1023165 baseEnd_1023165 := by
    simpa [prefixWord, tailWord_1023165, baseEnd_1023165] using wordTrace_append hprefix tailTrace_1023165
  have hstable : (prefixWord ++ tailWord_1023165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023165).length < 2 ^ (prefixWord ++ tailWord_1023165).sum := by decide
  have hdescent : baseEnd_1023165 < baseStart_1023165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023167 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 3, 3]
def baseStart_1023167 : Nat := 118140960795 + 1023167 * 2 ^ 59
def prefixEnd_1023167 : Nat := 4983230072969 + 3 ^ 40 * 1023167 * 2
def baseEnd_1023167 : Nat := 350250973879269058738031

theorem tailTrace_1023167 : CollatzResearch.WordTrace tailWord_1023167 prefixEnd_1023167 350250973879269058738031 := by
  unfold tailWord_1023167
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317966284248176856707755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24878644189498784571138503 37317966284248176856707755)
  ·
    refine ⟨55976949426372265285061633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37317966284248176856707755 55976949426372265285061633)
    ·
      refine ⟨41982712069779198963796225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55976949426372265285061633 41982712069779198963796225)
      ·
        refine ⟨31487034052334399222847169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41982712069779198963796225 31487034052334399222847169)
        ·
          refine ⟨23615275539250799417135377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31487034052334399222847169 23615275539250799417135377)
          ·
            refine ⟨17711456654438099562851533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23615275539250799417135377 17711456654438099562851533)
            ·
              refine ⟨6641796245414287336069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17711456654438099562851533 6641796245414287336069325)
              ·
                refine ⟨2490673592030357751025997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6641796245414287336069325 2490673592030357751025997)
                ·
                  refine ⟨934002597011384156634749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2490673592030357751025997 934002597011384156634749)
                  ·
                    refine ⟨350250973879269058738031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934002597011384156634749 350250973879269058738031)
                    ·
                      rfl

theorem cell22_1023167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_1023167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023167 prefixEnd_1023167 := by exact prefixLift 1023167
  have htrace : WordTrace (prefixWord ++ tailWord_1023167) baseStart_1023167 baseEnd_1023167 := by
    simpa [prefixWord, tailWord_1023167, baseEnd_1023167] using wordTrace_append hprefix tailTrace_1023167
  have hstable : (prefixWord ++ tailWord_1023167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023167).length < 2 ^ (prefixWord ++ tailWord_1023167).sum := by decide
  have hdescent : baseEnd_1023167 < baseStart_1023167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023201 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1023201 : Nat := 118140960795 + 1023201 * 2 ^ 59
def prefixEnd_1023201 : Nat := 4983230072969 + 3 ^ 40 * 1023201 * 2
def baseEnd_1023201 : Nat := 350262612774104303387927

theorem tailTrace_1023201 : CollatzResearch.WordTrace tailWord_1023201 prefixEnd_1023201 350262612774104303387927 := by
  unfold tailWord_1023201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319206366125000663445457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24879470910750000442296971 37319206366125000663445457)
  ·
    refine ⟨27989404774593750497584093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37319206366125000663445457 27989404774593750497584093)
    ·
      refine ⟨10496026790472656436594035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27989404774593750497584093 10496026790472656436594035)
      ·
        refine ⟨15744040185708984654891053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496026790472656436594035 15744040185708984654891053)
        ·
          refine ⟨5904015069640869245584145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15744040185708984654891053 5904015069640869245584145)
          ·
            refine ⟨4428011302230651934188109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904015069640869245584145 4428011302230651934188109)
            ·
              refine ⟨1660504238336494475320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428011302230651934188109 1660504238336494475320541)
              ·
                refine ⟨622689089376185428245203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1660504238336494475320541 622689089376185428245203)
                ·
                  refine ⟨934033634064278142367805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622689089376185428245203 934033634064278142367805)
                  ·
                    refine ⟨350262612774104303387927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934033634064278142367805 350262612774104303387927)
                    ·
                      rfl

theorem cell22_1023201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1023201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023201 prefixEnd_1023201 := by exact prefixLift 1023201
  have htrace : WordTrace (prefixWord ++ tailWord_1023201) baseStart_1023201 baseEnd_1023201 := by
    simpa [prefixWord, tailWord_1023201, baseEnd_1023201] using wordTrace_append hprefix tailTrace_1023201
  have hstable : (prefixWord ++ tailWord_1023201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023201).length < 2 ^ (prefixWord ++ tailWord_1023201).sum := by decide
  have hdescent : baseEnd_1023201 < baseStart_1023201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023218 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1023218 : Nat := 118140960795 + 1023218 * 2 ^ 59
def prefixEnd_1023218 : Nat := 4983230072969 + 3 ^ 40 * 1023218 * 2
def baseEnd_1023218 : Nat := 350268432221521925712875

theorem tailTrace_1023218 : CollatzResearch.WordTrace tailWord_1023218 prefixEnd_1023218 350268432221521925712875 := by
  unfold tailWord_1023218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329956601765853141703577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24879884271375608377876205 9329956601765853141703577)
  ·
    refine ⟨6997467451324389856277683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9329956601765853141703577 6997467451324389856277683)
    ·
      refine ⟨10496201176986584784416525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997467451324389856277683 10496201176986584784416525)
      ·
        refine ⟨3936075441369969294156197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10496201176986584784416525 3936075441369969294156197)
        ·
          refine ⟨738014145256869242654287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3936075441369969294156197 738014145256869242654287)
          ·
            refine ⟨1107021217885303863981431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738014145256869242654287 1107021217885303863981431)
            ·
              refine ⟨1660531826827955795972147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107021217885303863981431 1660531826827955795972147)
              ·
                refine ⟨2490797740241933693958221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660531826827955795972147 2490797740241933693958221)
                ·
                  refine ⟨934049152590725135234333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2490797740241933693958221 934049152590725135234333)
                  ·
                    refine ⟨350268432221521925712875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934049152590725135234333 350268432221521925712875)
                    ·
                      rfl

theorem cell22_1023218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1023218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023218 prefixEnd_1023218 := by exact prefixLift 1023218
  have htrace : WordTrace (prefixWord ++ tailWord_1023218) baseStart_1023218 baseEnd_1023218 := by
    simpa [prefixWord, tailWord_1023218, baseEnd_1023218] using wordTrace_append hprefix tailTrace_1023218
  have hstable : (prefixWord ++ tailWord_1023218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023218).length < 2 ^ (prefixWord ++ tailWord_1023218).sum := by decide
  have hdescent : baseEnd_1023218 < baseStart_1023218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023244 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1023244 : Nat := 118140960795 + 1023244 * 2 ^ 59
def prefixEnd_1023244 : Nat := 4983230072969 + 3 ^ 40 * 1023244 * 2
def baseEnd_1023244 : Nat := 350277332552866524562795

theorem tailTrace_1023244 : CollatzResearch.WordTrace tailWord_1023244 prefixEnd_1023244 350277332552866524562795 := by
  unfold tailWord_1023244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660387352484609503630393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24880516469979479338173857 18660387352484609503630393)
  ·
    refine ⟨13995290514363457127722795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18660387352484609503630393 13995290514363457127722795)
    ·
      refine ⟨20992935771545185691584193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995290514363457127722795 20992935771545185691584193)
      ·
        refine ⟨15744701828658889268688145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20992935771545185691584193 15744701828658889268688145)
        ·
          refine ⟨11808526371494166951516109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15744701828658889268688145 11808526371494166951516109)
          ·
            refine ⟨4428197389310312606818541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11808526371494166951516109 4428197389310312606818541)
            ·
              refine ⟨1660574020991367227556953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428197389310312606818541 1660574020991367227556953)
              ·
                refine ⟨1245430515743525420667715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660574020991367227556953 1245430515743525420667715)
                ·
                  refine ⟨1868145773615288131001573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245430515743525420667715 1868145773615288131001573)
                  ·
                    refine ⟨350277332552866524562795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868145773615288131001573 350277332552866524562795)
                    ·
                      rfl

theorem cell22_1023244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1023244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023244 prefixEnd_1023244 := by exact prefixLift 1023244
  have htrace : WordTrace (prefixWord ++ tailWord_1023244) baseStart_1023244 baseEnd_1023244 := by
    simpa [prefixWord, tailWord_1023244, baseEnd_1023244] using wordTrace_append hprefix tailTrace_1023244
  have hstable : (prefixWord ++ tailWord_1023244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023244).length < 2 ^ (prefixWord ++ tailWord_1023244).sum := by decide
  have hdescent : baseEnd_1023244 < baseStart_1023244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023325 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1023325 : Nat := 118140960795 + 1023325 * 2 ^ 59
def prefixEnd_1023325 : Nat := 4983230072969 + 3 ^ 40 * 1023325 * 2
def baseEnd_1023325 : Nat := 350305060508209313287547

theorem tailTrace_1023325 : CollatzResearch.WordTrace tailWord_1023325 prefixEnd_1023325 350305060508209313287547 := by
  unfold tailWord_1023325
  simp only [CollatzResearch.WordTrace]
  refine ⟨37323729017675769840959429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24882486011783846560639619 37323729017675769840959429)
  ·
    refine ⟨6998199190814206845179893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37323729017675769840959429 6998199190814206845179893)
    ·
      refine ⟨656081174138831891735615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6998199190814206845179893 656081174138831891735615)
      ·
        refine ⟨984121761208247837603423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656081174138831891735615 984121761208247837603423)
        ·
          refine ⟨1476182641812371756405135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984121761208247837603423 1476182641812371756405135)
          ·
            refine ⟨2214273962718557634607703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476182641812371756405135 2214273962718557634607703)
            ·
              refine ⟨3321410944077836451911555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214273962718557634607703 3321410944077836451911555)
              ·
                refine ⟨4982116416116754677867333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321410944077836451911555 4982116416116754677867333)
                ·
                  refine ⟨934146828021891502100125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4982116416116754677867333 934146828021891502100125)
                  ·
                    refine ⟨350305060508209313287547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934146828021891502100125 350305060508209313287547)
                    ·
                      rfl

theorem cell22_1023325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1023325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023325 prefixEnd_1023325 := by exact prefixLift 1023325
  have htrace : WordTrace (prefixWord ++ tailWord_1023325) baseStart_1023325 baseEnd_1023325 := by
    simpa [prefixWord, tailWord_1023325, baseEnd_1023325] using wordTrace_append hprefix tailTrace_1023325
  have hstable : (prefixWord ++ tailWord_1023325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023325).length < 2 ^ (prefixWord ++ tailWord_1023325).sum := by decide
  have hdescent : baseEnd_1023325 < baseStart_1023325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023400 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_1023400 : Nat := 118140960795 + 1023400 * 2 ^ 59
def prefixEnd_1023400 : Nat := 4983230072969 + 3 ^ 40 * 1023400 * 2
def baseEnd_1023400 : Nat := 116776911513644705887439

theorem tailTrace_1023400 : CollatzResearch.WordTrace tailWord_1023400 prefixEnd_1023400 116776911513644705887439 := by
  unfold tailWord_1023400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663232246202028824969827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24884309661602705099959769 18663232246202028824969827)
  ·
    refine ⟨27994848369303043237454741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663232246202028824969827 27994848369303043237454741)
    ·
      refine ⟨1312258517311080151755691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27994848369303043237454741 1312258517311080151755691)
      ·
        refine ⟨1968387775966620227633537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312258517311080151755691 1968387775966620227633537)
        ·
          refine ⟨1476290831974965170725153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968387775966620227633537 1476290831974965170725153)
          ·
            refine ⟨1107218123981223878043865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476290831974965170725153 1107218123981223878043865)
            ·
              refine ⟨830413592985917908532899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107218123981223878043865 830413592985917908532899)
              ·
                refine ⟨1245620389478876862799349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830413592985917908532899 1245620389478876862799349)
                ·
                  refine ⟨116776911513644705887439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245620389478876862799349 116776911513644705887439)
                  ·
                    rfl

theorem cell22_1023400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_1023400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023400 prefixEnd_1023400 := by exact prefixLift 1023400
  have htrace : WordTrace (prefixWord ++ tailWord_1023400) baseStart_1023400 baseEnd_1023400 := by
    simpa [prefixWord, tailWord_1023400, baseEnd_1023400] using wordTrace_append hprefix tailTrace_1023400
  have hstable : (prefixWord ++ tailWord_1023400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023400).length < 2 ^ (prefixWord ++ tailWord_1023400).sum := by decide
  have hdescent : baseEnd_1023400 < baseStart_1023400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023407 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1023407 : Nat := 118140960795 + 1023407 * 2 ^ 59
def prefixEnd_1023407 : Nat := 4983230072969 + 3 ^ 40 * 1023407 * 2
def baseEnd_1023407 : Nat := 350333130783988432737295

theorem tailTrace_1023407 : CollatzResearch.WordTrace tailWord_1023407 prefixEnd_1023407 350333130783988432737295 := by
  unfold tailWord_1023407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326719803378697845444475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24884479868919131896962983 37326719803378697845444475)
  ·
    refine ⟨55990079705068046768166713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37326719803378697845444475 55990079705068046768166713)
    ·
      refine ⟨41992559778801035076125035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55990079705068046768166713 41992559778801035076125035)
      ·
        refine ⟨62988839668201552614187553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41992559778801035076125035 62988839668201552614187553)
        ·
          refine ⟨47241629751151164460640665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62988839668201552614187553 47241629751151164460640665)
          ·
            refine ⟨35431222313363373345480499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47241629751151164460640665 35431222313363373345480499)
            ·
              refine ⟨53146833470045060018220749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35431222313363373345480499 53146833470045060018220749)
              ·
                refine ⟨19930062551266897506832781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53146833470045060018220749 19930062551266897506832781)
                ·
                  refine ⟨7473773456725086565062293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19930062551266897506832781 7473773456725086565062293)
                  ·
                    refine ⟨350333130783988432737295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7473773456725086565062293 350333130783988432737295)
                    ·
                      rfl

theorem cell22_1023407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1023407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023407 prefixEnd_1023407 := by exact prefixLift 1023407
  have htrace : WordTrace (prefixWord ++ tailWord_1023407) baseStart_1023407 baseEnd_1023407 := by
    simpa [prefixWord, tailWord_1023407, baseEnd_1023407] using wordTrace_append hprefix tailTrace_1023407
  have hstable : (prefixWord ++ tailWord_1023407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023407).length < 2 ^ (prefixWord ++ tailWord_1023407).sum := by decide
  have hdescent : baseEnd_1023407 < baseStart_1023407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023409 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1023409 : Nat := 118140960795 + 1023409 * 2 ^ 59
def prefixEnd_1023409 : Nat := 4983230072969 + 3 ^ 40 * 1023409 * 2
def baseEnd_1023409 : Nat := 350333815424861094187289

theorem tailTrace_1023409 : CollatzResearch.WordTrace tailWord_1023409 prefixEnd_1023409 350333815424861094187289 := by
  unfold tailWord_1023409
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326792749371452187017281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24884528499580968124678187 37326792749371452187017281)
  ·
    refine ⟨27995094562028589140262961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37326792749371452187017281 27995094562028589140262961)
    ·
      refine ⟨20996320921521441855197221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27995094562028589140262961 20996320921521441855197221)
      ·
        refine ⟨3936810172785270347849479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20996320921521441855197221 3936810172785270347849479)
        ·
          refine ⟨5905215259177905521774219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936810172785270347849479 5905215259177905521774219)
          ·
            refine ⟨8857822888766858282661329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905215259177905521774219 8857822888766858282661329)
            ·
              refine ⟨6643367166575143711995997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8857822888766858282661329 6643367166575143711995997)
              ·
                refine ⟨2491262687465678891998499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643367166575143711995997 2491262687465678891998499)
                ·
                  refine ⟨3736894031198518337997749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491262687465678891998499 3736894031198518337997749)
                  ·
                    refine ⟨350333815424861094187289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3736894031198518337997749 350333815424861094187289)
                    ·
                      rfl

theorem cell22_1023409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1023409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023409 prefixEnd_1023409 := by exact prefixLift 1023409
  have htrace : WordTrace (prefixWord ++ tailWord_1023409) baseStart_1023409 baseEnd_1023409 := by
    simpa [prefixWord, tailWord_1023409, baseEnd_1023409] using wordTrace_append hprefix tailTrace_1023409
  have hstable : (prefixWord ++ tailWord_1023409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023409).length < 2 ^ (prefixWord ++ tailWord_1023409).sum := by decide
  have hdescent : baseEnd_1023409 < baseStart_1023409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023413 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1023413 : Nat := 118140960795 + 1023413 * 2 ^ 59
def prefixEnd_1023413 : Nat := 4983230072969 + 3 ^ 40 * 1023413 * 2
def baseEnd_1023413 : Nat := 350335184706606417087277

theorem tailTrace_1023413 : CollatzResearch.WordTrace tailWord_1023413 prefixEnd_1023413 350335184706606417087277 := by
  unfold tailWord_1023413
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326938641356960870162893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24884625760904640580108595 37326938641356960870162893)
  ·
    refine ⟨13997601990508860326311085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37326938641356960870162893 13997601990508860326311085)
    ·
      refine ⟨5249100746440822622366657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13997601990508860326311085 5249100746440822622366657)
      ·
        refine ⟨3936825559830616966774993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5249100746440822622366657 3936825559830616966774993)
        ·
          refine ⟨2952619169872962725081245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3936825559830616966774993 2952619169872962725081245)
          ·
            refine ⟨1107232188702361021905467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952619169872962725081245 1107232188702361021905467)
            ·
              refine ⟨1660848283053541532858201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107232188702361021905467 1660848283053541532858201)
              ·
                refine ⟨1245636212290156149643651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660848283053541532858201 1245636212290156149643651)
                ·
                  refine ⟨1868454318435234224465477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245636212290156149643651 1868454318435234224465477)
                  ·
                    refine ⟨350335184706606417087277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868454318435234224465477 350335184706606417087277)
                    ·
                      rfl

theorem cell22_1023413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1023413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023413 prefixEnd_1023413 := by exact prefixLift 1023413
  have htrace : WordTrace (prefixWord ++ tailWord_1023413) baseStart_1023413 baseEnd_1023413 := by
    simpa [prefixWord, tailWord_1023413, baseEnd_1023413] using wordTrace_append hprefix tailTrace_1023413
  have hstable : (prefixWord ++ tailWord_1023413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023413).length < 2 ^ (prefixWord ++ tailWord_1023413).sum := by decide
  have hdescent : baseEnd_1023413 < baseStart_1023413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023424 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_1023424 : Nat := 118140960795 + 1023424 * 2 ^ 59
def prefixEnd_1023424 : Nat := 4983230072969 + 3 ^ 40 * 1023424 * 2
def baseEnd_1023424 : Nat := 350338950231406055062243

theorem tailTrace_1023424 : CollatzResearch.WordTrace tailWord_1023424 prefixEnd_1023424 350338950231406055062243 := by
  unfold tailWord_1023424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663669922158554874406663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24884893229544739832542217 18663669922158554874406663)
  ·
    refine ⟨27995504883237832311609995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663669922158554874406663 27995504883237832311609995)
    ·
      refine ⟨41993257324856748467414993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27995504883237832311609995 41993257324856748467414993)
      ·
        refine ⟨31494942993642561350561245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41993257324856748467414993 31494942993642561350561245)
        ·
          refine ⟨11810603622615960506460467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31494942993642561350561245 11810603622615960506460467)
          ·
            refine ⟨17715905433923940759690701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810603622615960506460467 17715905433923940759690701)
            ·
              refine ⟨6643464537721477784884013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17715905433923940759690701 6643464537721477784884013)
              ·
                refine ⟨2491299201645554169331505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643464537721477784884013 2491299201645554169331505)
                ·
                  refine ⟨1868474401234165626998629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491299201645554169331505 1868474401234165626998629)
                  ·
                    refine ⟨350338950231406055062243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868474401234165626998629 350338950231406055062243)
                    ·
                      rfl

theorem cell22_1023424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_1023424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023424 prefixEnd_1023424 := by exact prefixLift 1023424
  have htrace : WordTrace (prefixWord ++ tailWord_1023424) baseStart_1023424 baseEnd_1023424 := by
    simpa [prefixWord, tailWord_1023424, baseEnd_1023424] using wordTrace_append hprefix tailTrace_1023424
  have hstable : (prefixWord ++ tailWord_1023424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023424).length < 2 ^ (prefixWord ++ tailWord_1023424).sum := by decide
  have hdescent : baseEnd_1023424 < baseStart_1023424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023670 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1023670 : Nat := 118140960795 + 1023670 * 2 ^ 59
def prefixEnd_1023670 : Nat := 4983230072969 + 3 ^ 40 * 1023670 * 2
def baseEnd_1023670 : Nat := 116807720352914471137163

theorem tailTrace_1023670 : CollatzResearch.WordTrace tailWord_1023670 prefixEnd_1023670 116807720352914471137163 := by
  unfold tailWord_1023670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333519512589118360141779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24890874800950595841512309 2333519512589118360141779)
  ·
    refine ⟨3500279268883677540212669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333519512589118360141779 3500279268883677540212669)
    ·
      refine ⟨1312604725831379077579751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3500279268883677540212669 1312604725831379077579751)
      ·
        refine ⟨1968907088747068616369627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312604725831379077579751 1968907088747068616369627)
        ·
          refine ⟨2953360633120602924554441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968907088747068616369627 2953360633120602924554441)
          ·
            refine ⟨2215020474840452193415831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953360633120602924554441 2215020474840452193415831)
            ·
              refine ⟨3322530712260678290123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215020474840452193415831 3322530712260678290123747)
              ·
                refine ⟨4983796068391017435185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322530712260678290123747 4983796068391017435185621)
                ·
                  refine ⟨116807720352914471137163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4983796068391017435185621 116807720352914471137163)
                  ·
                    rfl

theorem cell22_1023670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1023670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023670 prefixEnd_1023670 := by exact prefixLift 1023670
  have htrace : WordTrace (prefixWord ++ tailWord_1023670) baseStart_1023670 baseEnd_1023670 := by
    simpa [prefixWord, tailWord_1023670, baseEnd_1023670] using wordTrace_append hprefix tailTrace_1023670
  have hstable : (prefixWord ++ tailWord_1023670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023670).length < 2 ^ (prefixWord ++ tailWord_1023670).sum := by decide
  have hdescent : baseEnd_1023670 < baseStart_1023670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023696 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_1023696 : Nat := 118140960795 + 1023696 * 2 ^ 59
def prefixEnd_1023696 : Nat := 4983230072969 + 3 ^ 40 * 1023696 * 2
def baseEnd_1023696 : Nat := 350432061390088012261409

theorem tailTrace_1023696 : CollatzResearch.WordTrace tailWord_1023696 prefixEnd_1023696 350432061390088012261409 := by
  unfold tailWord_1023696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668630249665850101357471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24891506999554466801809961 18668630249665850101357471)
  ·
    refine ⟨28002945374498775152036207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18668630249665850101357471 28002945374498775152036207)
    ·
      refine ⟨42004418061748162728054311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002945374498775152036207 42004418061748162728054311)
      ·
        refine ⟨63006627092622244092081467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42004418061748162728054311 63006627092622244092081467)
        ·
          refine ⟨94509940638933366138122201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63006627092622244092081467 94509940638933366138122201)
          ·
            refine ⟨70882455479200024603591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94509940638933366138122201 70882455479200024603591651)
            ·
              refine ⟨106323683218800036905387477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70882455479200024603591651 106323683218800036905387477)
              ·
                refine ⟨2491961325440625864970019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106323683218800036905387477 2491961325440625864970019)
                ·
                  refine ⟨3737941988160938797455029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491961325440625864970019 3737941988160938797455029)
                  ·
                    refine ⟨350432061390088012261409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3737941988160938797455029 350432061390088012261409)
                    ·
                      rfl

theorem cell22_1023696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_1023696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023696 prefixEnd_1023696 := by exact prefixLift 1023696
  have htrace : WordTrace (prefixWord ++ tailWord_1023696) baseStart_1023696 baseEnd_1023696 := by
    simpa [prefixWord, tailWord_1023696, baseEnd_1023696] using wordTrace_append hprefix tailTrace_1023696
  have hstable : (prefixWord ++ tailWord_1023696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023696).length < 2 ^ (prefixWord ++ tailWord_1023696).sum := by decide
  have hdescent : baseEnd_1023696 < baseStart_1023696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023698 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1023698 : Nat := 118140960795 + 1023698 * 2 ^ 59
def prefixEnd_1023698 : Nat := 4983230072969 + 3 ^ 40 * 1023698 * 2
def baseEnd_1023698 : Nat := 116810915343653557903801

theorem tailTrace_1023698 : CollatzResearch.WordTrace tailWord_1023698 prefixEnd_1023698 116810915343653557903801 := by
  unfold tailWord_1023698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334333361331113636071937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24891555630216303029525165 9334333361331113636071937)
  ·
    refine ⟨7000750020998335227053953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9334333361331113636071937 7000750020998335227053953)
    ·
      refine ⟨5250562515748751420290465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7000750020998335227053953 5250562515748751420290465)
      ·
        refine ⟨3937921886811563565217849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5250562515748751420290465 3937921886811563565217849)
        ·
          refine ⟨2953441415108672673913387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937921886811563565217849 2953441415108672673913387)
          ·
            refine ⟨4430162122663009010870081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953441415108672673913387 4430162122663009010870081)
            ·
              refine ⟨3322621591997256758152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430162122663009010870081 3322621591997256758152561)
              ·
                refine ⟨2491966193997942568614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322621591997256758152561 2491966193997942568614421)
                ·
                  refine ⟨116810915343653557903801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2491966193997942568614421 116810915343653557903801)
                  ·
                    rfl

theorem cell22_1023698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1023698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023698 prefixEnd_1023698 := by exact prefixLift 1023698
  have htrace : WordTrace (prefixWord ++ tailWord_1023698) baseStart_1023698 baseEnd_1023698 := by
    simpa [prefixWord, tailWord_1023698, baseEnd_1023698] using wordTrace_append hprefix tailTrace_1023698
  have hstable : (prefixWord ++ tailWord_1023698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023698).length < 2 ^ (prefixWord ++ tailWord_1023698).sum := by decide
  have hdescent : baseEnd_1023698 < baseStart_1023698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023700 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1023700 : Nat := 118140960795 + 1023700 * 2 ^ 59
def prefixEnd_1023700 : Nat := 4983230072969 + 3 ^ 40 * 1023700 * 2
def baseEnd_1023700 : Nat := 350433430671833335161397

theorem tailTrace_1023700 : CollatzResearch.WordTrace tailWord_1023700 prefixEnd_1023700 350433430671833335161397 := by
  unfold tailWord_1023700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668703195658604442930277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24891604260878139257240369 18668703195658604442930277)
  ·
    refine ⟨3500381849185988333049427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18668703195658604442930277 3500381849185988333049427)
    ·
      refine ⟨5250572773778982499574141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500381849185988333049427 5250572773778982499574141)
      ·
        refine ⟨1968964790167118437340303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5250572773778982499574141 1968964790167118437340303)
        ·
          refine ⟨2953447185250677656010455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968964790167118437340303 2953447185250677656010455)
          ·
            refine ⟨4430170777876016484015683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953447185250677656010455 4430170777876016484015683)
            ·
              refine ⟨6645256166814024726023525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430170777876016484015683 6645256166814024726023525)
              ·
                refine ⟨1245985531277629636129411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6645256166814024726023525 1245985531277629636129411)
                ·
                  refine ⟨1868978296916444454194117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245985531277629636129411 1868978296916444454194117)
                  ·
                    refine ⟨350433430671833335161397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868978296916444454194117 350433430671833335161397)
                    ·
                      rfl

theorem cell22_1023700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1023700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023700 prefixEnd_1023700 := by exact prefixLift 1023700
  have htrace : WordTrace (prefixWord ++ tailWord_1023700) baseStart_1023700 baseEnd_1023700 := by
    simpa [prefixWord, tailWord_1023700, baseEnd_1023700] using wordTrace_append hprefix tailTrace_1023700
  have hstable : (prefixWord ++ tailWord_1023700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023700).length < 2 ^ (prefixWord ++ tailWord_1023700).sum := by decide
  have hdescent : baseEnd_1023700 < baseStart_1023700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023711 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1023711 : Nat := 118140960795 + 1023711 * 2 ^ 59
def prefixEnd_1023711 : Nat := 4983230072969 + 3 ^ 40 * 1023711 * 2
def baseEnd_1023711 : Nat := 350437196196632973136363

theorem tailTrace_1023711 : CollatzResearch.WordTrace tailWord_1023711 prefixEnd_1023711 350437196196632973136363 := by
  unfold tailWord_1023711
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337807594277357764510987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24891871729518238509673991 37337807594277357764510987)
  ·
    refine ⟨56006711391416036646766481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37337807594277357764510987 56006711391416036646766481)
    ·
      refine ⟨42005033543562027485074861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56006711391416036646766481 42005033543562027485074861)
      ·
        refine ⟨15751887578835760306903073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42005033543562027485074861 15751887578835760306903073)
        ·
          refine ⟨11813915684126820230177305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15751887578835760306903073 11813915684126820230177305)
          ·
            refine ⟨8860436763095115172632979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11813915684126820230177305 8860436763095115172632979)
            ·
              refine ⟨13290655144642672758949469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860436763095115172632979 13290655144642672758949469)
              ·
                refine ⟨4983995679241002284606051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13290655144642672758949469 4983995679241002284606051)
                ·
                  refine ⟨7475993518861503426909077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983995679241002284606051 7475993518861503426909077)
                  ·
                    refine ⟨350437196196632973136363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7475993518861503426909077 350437196196632973136363)
                    ·
                      rfl

theorem cell22_1023711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1023711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023711 prefixEnd_1023711 := by exact prefixLift 1023711
  have htrace : WordTrace (prefixWord ++ tailWord_1023711) baseStart_1023711 baseEnd_1023711 := by
    simpa [prefixWord, tailWord_1023711, baseEnd_1023711] using wordTrace_append hprefix tailTrace_1023711
  have hstable : (prefixWord ++ tailWord_1023711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023711).length < 2 ^ (prefixWord ++ tailWord_1023711).sum := by decide
  have hdescent : baseEnd_1023711 < baseStart_1023711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023730 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1023730 : Nat := 118140960795 + 1023730 * 2 ^ 59
def prefixEnd_1023730 : Nat := 4983230072969 + 3 ^ 40 * 1023730 * 2
def baseEnd_1023730 : Nat := 350443700284923256911305

theorem tailTrace_1023730 : CollatzResearch.WordTrace tailWord_1023730 prefixEnd_1023730 350443700284923256911305 := by
  unfold tailWord_1023730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334625145302131002363161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24892333720805682672968429 9334625145302131002363161)
  ·
    refine ⟨7000968858976598251772371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9334625145302131002363161 7000968858976598251772371)
    ·
      refine ⟨10501453288464897377658557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000968858976598251772371 10501453288464897377658557)
      ·
        refine ⟨3938044983174336516621959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10501453288464897377658557 3938044983174336516621959)
        ·
          refine ⟨5907067474761504774932939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938044983174336516621959 5907067474761504774932939)
          ·
            refine ⟨8860601212142257162399409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907067474761504774932939 8860601212142257162399409)
            ·
              refine ⟨6645450909106692871799557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860601212142257162399409 6645450909106692871799557)
              ·
                refine ⟨1246022045457504913462417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6645450909106692871799557 1246022045457504913462417)
                ·
                  refine ⟨934516534093128685096813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1246022045457504913462417 934516534093128685096813)
                  ·
                    refine ⟨350443700284923256911305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934516534093128685096813 350443700284923256911305)
                    ·
                      rfl

theorem cell22_1023730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1023730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023730 prefixEnd_1023730 := by exact prefixLift 1023730
  have htrace : WordTrace (prefixWord ++ tailWord_1023730) baseStart_1023730 baseEnd_1023730 := by
    simpa [prefixWord, tailWord_1023730, baseEnd_1023730] using wordTrace_append hprefix tailTrace_1023730
  have hstable : (prefixWord ++ tailWord_1023730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023730).length < 2 ^ (prefixWord ++ tailWord_1023730).sum := by decide
  have hdescent : baseEnd_1023730 < baseStart_1023730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023732 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1023732 : Nat := 118140960795 + 1023732 * 2 ^ 59
def prefixEnd_1023732 : Nat := 4983230072969 + 3 ^ 40 * 1023732 * 2
def baseEnd_1023732 : Nat := 116814794975265306120433

theorem tailTrace_1023732 : CollatzResearch.WordTrace tailWord_1023732 prefixEnd_1023732 116814794975265306120433 := by
  unfold tailWord_1023732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669286763600639175512725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24892382351467518900683633 18669286763600639175512725)
  ·
    refine ⟨875122817043779961352159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18669286763600639175512725 875122817043779961352159)
    ·
      refine ⟨1312684225565669942028239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875122817043779961352159 1312684225565669942028239)
      ·
        refine ⟨1969026338348504913042359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312684225565669942028239 1969026338348504913042359)
        ·
          refine ⟨2953539507522757369563539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969026338348504913042359 2953539507522757369563539)
          ·
            refine ⟨4430309261284136054345309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953539507522757369563539 4430309261284136054345309)
            ·
              refine ⟨1661365972981551020379491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4430309261284136054345309 1661365972981551020379491)
              ·
                refine ⟨2492048959472326530569237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661365972981551020379491 2492048959472326530569237)
                ·
                  refine ⟨116814794975265306120433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2492048959472326530569237 116814794975265306120433)
                  ·
                    rfl

theorem cell22_1023732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1023732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023732 prefixEnd_1023732 := by exact prefixLift 1023732
  have htrace : WordTrace (prefixWord ++ tailWord_1023732) baseStart_1023732 baseEnd_1023732 := by
    simpa [prefixWord, tailWord_1023732, baseEnd_1023732] using wordTrace_append hprefix tailTrace_1023732
  have hstable : (prefixWord ++ tailWord_1023732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023732).length < 2 ^ (prefixWord ++ tailWord_1023732).sum := by decide
  have hdescent : baseEnd_1023732 < baseStart_1023732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023741 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1023741 : Nat := 118140960795 + 1023741 * 2 ^ 59
def prefixEnd_1023741 : Nat := 4983230072969 + 3 ^ 40 * 1023741 * 2
def baseEnd_1023741 : Nat := 350447465809722894886271

theorem tailTrace_1023741 : CollatzResearch.WordTrace tailWord_1023741 prefixEnd_1023741 350447465809722894886271 := by
  unfold tailWord_1023741
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338901784168672888103077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24892601189445781925402051 37338901784168672888103077)
  ·
    refine ⟨7001044084531626166519327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37338901784168672888103077 7001044084531626166519327)
    ·
      refine ⟨10501566126797439249778991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001044084531626166519327 10501566126797439249778991)
      ·
        refine ⟨15752349190196158874668487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501566126797439249778991 15752349190196158874668487)
        ·
          refine ⟨23628523785294238312002731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752349190196158874668487 23628523785294238312002731)
          ·
            refine ⟨35442785677941357468004097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23628523785294238312002731 35442785677941357468004097)
            ·
              refine ⟨26582089258456018101003073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35442785677941357468004097 26582089258456018101003073)
              ·
                refine ⟨19936566943842013575752305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26582089258456018101003073 19936566943842013575752305)
                ·
                  refine ⟨14952425207881510181814229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19936566943842013575752305 14952425207881510181814229)
                  ·
                    refine ⟨350447465809722894886271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14952425207881510181814229 350447465809722894886271)
                    ·
                      rfl

theorem cell22_1023741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1023741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023741 prefixEnd_1023741 := by exact prefixLift 1023741
  have htrace : WordTrace (prefixWord ++ tailWord_1023741) baseStart_1023741 baseEnd_1023741 := by
    simpa [prefixWord, tailWord_1023741, baseEnd_1023741] using wordTrace_append hprefix tailTrace_1023741
  have hstable : (prefixWord ++ tailWord_1023741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023741).length < 2 ^ (prefixWord ++ tailWord_1023741).sum := by decide
  have hdescent : baseEnd_1023741 < baseStart_1023741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023762 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1023762 : Nat := 118140960795 + 1023762 * 2 ^ 59
def prefixEnd_1023762 : Nat := 4983230072969 + 3 ^ 40 * 1023762 * 2
def baseEnd_1023762 : Nat := 350454654538885840111207

theorem tailTrace_1023762 : CollatzResearch.WordTrace tailWord_1023762 prefixEnd_1023762 350454654538885840111207 := by
  unfold tailWord_1023762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334916929273148368654385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24893111811395062316411693 9334916929273148368654385)
  ·
    refine ⟨7001187696954861276490789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9334916929273148368654385 7001187696954861276490789)
    ·
      refine ⟨1312722693179036489342023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7001187696954861276490789 1312722693179036489342023)
      ·
        refine ⟨1969084039768554734013035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312722693179036489342023 1969084039768554734013035)
        ·
          refine ⟨2953626059652832101019553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969084039768554734013035 2953626059652832101019553)
          ·
            refine ⟨2215219544739624075764665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953626059652832101019553 2215219544739624075764665)
            ·
              refine ⟨1661414658554718056823499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215219544739624075764665 1661414658554718056823499)
              ·
                refine ⟨2492121987832077085235249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661414658554718056823499 2492121987832077085235249)
                ·
                  refine ⟨1869091490874057813926437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2492121987832077085235249 1869091490874057813926437)
                  ·
                    refine ⟨350454654538885840111207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869091490874057813926437 350454654538885840111207)
                    ·
                      rfl

theorem cell22_1023762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1023762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023762 prefixEnd_1023762 := by exact prefixLift 1023762
  have htrace : WordTrace (prefixWord ++ tailWord_1023762) baseStart_1023762 baseEnd_1023762 := by
    simpa [prefixWord, tailWord_1023762, baseEnd_1023762] using wordTrace_append hprefix tailTrace_1023762
  have hstable : (prefixWord ++ tailWord_1023762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023762).length < 2 ^ (prefixWord ++ tailWord_1023762).sum := by decide
  have hdescent : baseEnd_1023762 < baseStart_1023762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023764 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1023764 : Nat := 118140960795 + 1023764 * 2 ^ 59
def prefixEnd_1023764 : Nat := 4983230072969 + 3 ^ 40 * 1023764 * 2
def baseEnd_1023764 : Nat := 350455339179758501561201

theorem tailTrace_1023764 : CollatzResearch.WordTrace tailWord_1023764 prefixEnd_1023764 350455339179758501561201 := by
  unfold tailWord_1023764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669870331542673908095173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24893160442056898544126897 18669870331542673908095173)
  ·
    refine ⟨3500600687164251357767845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18669870331542673908095173 3500600687164251357767845)
    ·
      refine ⟨656362628843297129581471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3500600687164251357767845 656362628843297129581471)
      ·
        refine ⟨984543943264945694372207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656362628843297129581471 984543943264945694372207)
        ·
          refine ⟨1476815914897418541558311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984543943264945694372207 1476815914897418541558311)
          ·
            refine ⟨2215223872346127812337467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476815914897418541558311 2215223872346127812337467)
            ·
              refine ⟨3322835808519191718506201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215223872346127812337467 3322835808519191718506201)
              ·
                refine ⟨2492126856389393788879651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322835808519191718506201 2492126856389393788879651)
                ·
                  refine ⟨3738190284584090683319477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492126856389393788879651 3738190284584090683319477)
                  ·
                    refine ⟨350455339179758501561201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3738190284584090683319477 350455339179758501561201)
                    ·
                      rfl

theorem cell22_1023764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1023764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023764 prefixEnd_1023764 := by exact prefixLift 1023764
  have htrace : WordTrace (prefixWord ++ tailWord_1023764) baseStart_1023764 baseEnd_1023764 := by
    simpa [prefixWord, tailWord_1023764, baseEnd_1023764] using wordTrace_append hprefix tailTrace_1023764
  have hstable : (prefixWord ++ tailWord_1023764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023764).length < 2 ^ (prefixWord ++ tailWord_1023764).sum := by decide
  have hdescent : baseEnd_1023764 < baseStart_1023764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023788 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_1023788 : Nat := 118140960795 + 1023788 * 2 ^ 59
def prefixEnd_1023788 : Nat := 4983230072969 + 3 ^ 40 * 1023788 * 2
def baseEnd_1023788 : Nat := 116821184956743479653709

theorem tailTrace_1023788 : CollatzResearch.WordTrace tailWord_1023788 prefixEnd_1023788 116821184956743479653709 := by
  unfold tailWord_1023788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670308007499199957532009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24893744009998933276709345 18670308007499199957532009)
  ·
    refine ⟨14002731005624399968149007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18670308007499199957532009 14002731005624399968149007)
    ·
      refine ⟨21004096508436599952223511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14002731005624399968149007 21004096508436599952223511)
      ·
        refine ⟨31506144762654899928335267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21004096508436599952223511 31506144762654899928335267)
        ·
          refine ⟨47259217143982349892502901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31506144762654899928335267 47259217143982349892502901)
          ·
            refine ⟨4430551607248345302422147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47259217143982349892502901 4430551607248345302422147)
            ·
              refine ⟨6645827410872517953633221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430551607248345302422147 6645827410872517953633221)
              ·
                refine ⟨1246092639538597116306229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6645827410872517953633221 1246092639538597116306229)
                ·
                  refine ⟨116821184956743479653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246092639538597116306229 116821184956743479653709)
                  ·
                    rfl

theorem cell22_1023788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_1023788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023788 prefixEnd_1023788 := by exact prefixLift 1023788
  have htrace : WordTrace (prefixWord ++ tailWord_1023788) baseStart_1023788 baseEnd_1023788 := by
    simpa [prefixWord, tailWord_1023788, baseEnd_1023788] using wordTrace_append hprefix tailTrace_1023788
  have hstable : (prefixWord ++ tailWord_1023788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023788).length < 2 ^ (prefixWord ++ tailWord_1023788).sum := by decide
  have hdescent : baseEnd_1023788 < baseStart_1023788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023805 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1023805 : Nat := 118140960795 + 1023805 * 2 ^ 59
def prefixEnd_1023805 : Nat := 4983230072969 + 3 ^ 40 * 1023805 * 2
def baseEnd_1023805 : Nat := 116823124772549353762025

theorem tailTrace_1023805 : CollatzResearch.WordTrace tailWord_1023805 prefixEnd_1023805 116823124772549353762025 := by
  unfold tailWord_1023805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37341236055936811818432869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24894157370624541212288579 37341236055936811818432869)
  ·
    refine ⟨7001481760488152215956163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37341236055936811818432869 7001481760488152215956163)
    ·
      refine ⟨10502222640732228323934245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001481760488152215956163 10502222640732228323934245)
      ·
        refine ⟨1969166745137292810737671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10502222640732228323934245 1969166745137292810737671)
        ·
          refine ⟨2953750117705939216106507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969166745137292810737671 2953750117705939216106507)
          ·
            refine ⟨4430625176558908824159761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953750117705939216106507 4430625176558908824159761)
            ·
              refine ⟨3322968882419181618119821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430625176558908824159761 3322968882419181618119821)
              ·
                refine ⟨1246113330907193106794933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3322968882419181618119821 1246113330907193106794933)
                ·
                  refine ⟨116823124772549353762025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246113330907193106794933 116823124772549353762025)
                  ·
                    rfl

theorem cell22_1023805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1023805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023805 prefixEnd_1023805 := by exact prefixLift 1023805
  have htrace : WordTrace (prefixWord ++ tailWord_1023805) baseStart_1023805 baseEnd_1023805 := by
    simpa [prefixWord, tailWord_1023805, baseEnd_1023805] using wordTrace_append hprefix tailTrace_1023805
  have hstable : (prefixWord ++ tailWord_1023805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023805).length < 2 ^ (prefixWord ++ tailWord_1023805).sum := by decide
  have hdescent : baseEnd_1023805 < baseStart_1023805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023818 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1023818 : Nat := 118140960795 + 1023818 * 2 ^ 59
def prefixEnd_1023818 : Nat := 4983230072969 + 3 ^ 40 * 1023818 * 2
def baseEnd_1023818 : Nat := 350473824483320360711035

theorem tailTrace_1023818 : CollatzResearch.WordTrace tailWord_1023818 prefixEnd_1023818 350473824483320360711035 := by
  unfold tailWord_1023818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335427551222428759664027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24894473469926476692437405 9335427551222428759664027)
  ·
    refine ⟨14003141326833643139496041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335427551222428759664027 14003141326833643139496041)
    ·
      refine ⟨10502355995125232354622031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14003141326833643139496041 10502355995125232354622031)
      ·
        refine ⟨15753533992687848531933047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10502355995125232354622031 15753533992687848531933047)
        ·
          refine ⟨23630300989031772797899571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753533992687848531933047 23630300989031772797899571)
          ·
            refine ⟨35445451483547659196849357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23630300989031772797899571 35445451483547659196849357)
            ·
              refine ⟨13292044306330372198818509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35445451483547659196849357 13292044306330372198818509)
              ·
                refine ⟨4984516614873889574556941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13292044306330372198818509 4984516614873889574556941)
                ·
                  refine ⟨1869193730577708590458853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4984516614873889574556941 1869193730577708590458853)
                  ·
                    refine ⟨350473824483320360711035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869193730577708590458853 350473824483320360711035)
                    ·
                      rfl

theorem cell22_1023818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1023818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023818 prefixEnd_1023818 := by exact prefixLift 1023818
  have htrace : WordTrace (prefixWord ++ tailWord_1023818) baseStart_1023818 baseEnd_1023818 := by
    simpa [prefixWord, tailWord_1023818, baseEnd_1023818] using wordTrace_append hprefix tailTrace_1023818
  have hstable : (prefixWord ++ tailWord_1023818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023818).length < 2 ^ (prefixWord ++ tailWord_1023818).sum := by decide
  have hdescent : baseEnd_1023818 < baseStart_1023818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023957 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1023957 : Nat := 118140960795 + 1023957 * 2 ^ 59
def prefixEnd_1023957 : Nat := 4983230072969 + 3 ^ 40 * 1023957 * 2
def baseEnd_1023957 : Nat := 116840469007990110495203

theorem tailTrace_1023957 : CollatzResearch.WordTrace tailWord_1023957 prefixEnd_1023957 116840469007990110495203 := by
  unfold tailWord_1023957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346779951386141777966125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24897853300924094518644083 37346779951386141777966125)
  ·
    refine ⟨14005042481769803166737297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37346779951386141777966125 14005042481769803166737297)
    ·
      refine ⟨10503781861327352375052973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14005042481769803166737297 10503781861327352375052973)
      ·
        refine ⟨3938918197997757140644865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10503781861327352375052973 3938918197997757140644865)
        ·
          refine ⟨2954188648498317855483649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3938918197997757140644865 2954188648498317855483649)
          ·
            refine ⟨2215641486373738391612737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954188648498317855483649 2215641486373738391612737)
            ·
              refine ⟨1661731114780303793709553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215641486373738391612737 1661731114780303793709553)
              ·
                refine ⟨1246298336085227845282165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661731114780303793709553 1246298336085227845282165)
                ·
                  refine ⟨116840469007990110495203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246298336085227845282165 116840469007990110495203)
                  ·
                    rfl

theorem cell22_1023957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1023957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023957 prefixEnd_1023957 := by exact prefixLift 1023957
  have htrace : WordTrace (prefixWord ++ tailWord_1023957) baseStart_1023957 baseEnd_1023957 := by
    simpa [prefixWord, tailWord_1023957, baseEnd_1023957] using wordTrace_append hprefix tailTrace_1023957
  have hstable : (prefixWord ++ tailWord_1023957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023957).length < 2 ^ (prefixWord ++ tailWord_1023957).sum := by decide
  have hdescent : baseEnd_1023957 < baseStart_1023957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023968 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_1023968 : Nat := 118140960795 + 1023968 * 2 ^ 59
def prefixEnd_1023968 : Nat := 4983230072969 + 3 ^ 40 * 1023968 * 2
def baseEnd_1023968 : Nat := 116841724182923323153525

theorem tailTrace_1023968 : CollatzResearch.WordTrace tailWord_1023968 prefixEnd_1023968 116841724182923323153525 := by
  unfold tailWord_1023968
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673590577173145328308279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24898120769564193771077705 18673590577173145328308279)
  ·
    refine ⟨28010385865759717992462419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673590577173145328308279 28010385865759717992462419)
    ·
      refine ⟨42015578798639576988693629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28010385865759717992462419 42015578798639576988693629)
      ·
        refine ⟨15755842049489841370760111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42015578798639576988693629 15755842049489841370760111)
        ·
          refine ⟨23633763074234762056140167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755842049489841370760111 23633763074234762056140167)
          ·
            refine ⟨35450644611352143084210251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23633763074234762056140167 35450644611352143084210251)
            ·
              refine ⟨53175966917028214626315377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35450644611352143084210251 53175966917028214626315377)
              ·
                refine ⟨39881975187771160969736533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53175966917028214626315377 39881975187771160969736533)
                ·
                  refine ⟨116841724182923323153525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 39881975187771160969736533 116841724182923323153525)
                  ·
                    rfl

theorem cell22_1023968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_1023968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1023968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1023968 prefixEnd_1023968 := by exact prefixLift 1023968
  have htrace : WordTrace (prefixWord ++ tailWord_1023968) baseStart_1023968 baseEnd_1023968 := by
    simpa [prefixWord, tailWord_1023968, baseEnd_1023968] using wordTrace_append hprefix tailTrace_1023968
  have hstable : (prefixWord ++ tailWord_1023968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023968).length < 2 ^ (prefixWord ++ tailWord_1023968).sum := by decide
  have hdescent : baseEnd_1023968 < baseStart_1023968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024077 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1024077 : Nat := 118140960795 + 1024077 * 2 ^ 59
def prefixEnd_1024077 : Nat := 4983230072969 + 3 ^ 40 * 1024077 * 2
def baseEnd_1024077 : Nat := 350562485476330018485241

theorem tailTrace_1024077 : CollatzResearch.WordTrace tailWord_1024077 prefixEnd_1024077 350562485476330018485241 := by
  unfold tailWord_1024077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37351156710951402272334485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24900771140634268181556323 37351156710951402272334485)
  ·
    refine ⟨1750835470825846981515679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37351156710951402272334485 1750835470825846981515679)
    ·
      refine ⟨2626253206238770472273519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750835470825846981515679 2626253206238770472273519)
      ·
        refine ⟨3939379809358155708410279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626253206238770472273519 3939379809358155708410279)
        ·
          refine ⟨5909069714037233562615419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939379809358155708410279 5909069714037233562615419)
          ·
            refine ⟨8863604571055850343923129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909069714037233562615419 8863604571055850343923129)
            ·
              refine ⟨6647703428291887757942347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863604571055850343923129 6647703428291887757942347)
              ·
                refine ⟨9971555142437831636913521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647703428291887757942347 9971555142437831636913521)
                ·
                  refine ⟨7478666356828373727685141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9971555142437831636913521 7478666356828373727685141)
                  ·
                    refine ⟨350562485476330018485241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7478666356828373727685141 350562485476330018485241)
                    ·
                      rfl

theorem cell22_1024077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1024077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024077 prefixEnd_1024077 := by exact prefixLift 1024077
  have htrace : WordTrace (prefixWord ++ tailWord_1024077) baseStart_1024077 baseEnd_1024077 := by
    simpa [prefixWord, tailWord_1024077, baseEnd_1024077] using wordTrace_append hprefix tailTrace_1024077
  have hstable : (prefixWord ++ tailWord_1024077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024077).length < 2 ^ (prefixWord ++ tailWord_1024077).sum := by decide
  have hdescent : baseEnd_1024077 < baseStart_1024077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024090 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1024090 : Nat := 118140960795 + 1024090 * 2 ^ 59
def prefixEnd_1024090 : Nat := 4983230072969 + 3 ^ 40 * 1024090 * 2
def baseEnd_1024090 : Nat := 350566935642002317910201

theorem tailTrace_1024090 : CollatzResearch.WordTrace tailWord_1024090 prefixEnd_1024090 350566935642002317910201 := by
  unfold tailWord_1024090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337907714976076373139431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24901087239936203661705149 9337907714976076373139431)
  ·
    refine ⟨14006861572464114559709147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9337907714976076373139431 14006861572464114559709147)
    ·
      refine ⟨21010292358696171839563721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14006861572464114559709147 21010292358696171839563721)
      ·
        refine ⟨15757719269022128879672791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21010292358696171839563721 15757719269022128879672791)
        ·
          refine ⟨23636578903533193319509187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15757719269022128879672791 23636578903533193319509187)
          ·
            refine ⟨35454868355299789979263781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23636578903533193319509187 35454868355299789979263781)
            ·
              refine ⟨6647787816618710621111959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35454868355299789979263781 6647787816618710621111959)
              ·
                refine ⟨9971681724928065931667939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647787816618710621111959 9971681724928065931667939)
                ·
                  refine ⟨14957522587392098897501909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971681724928065931667939 14957522587392098897501909)
                  ·
                    refine ⟨350566935642002317910201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14957522587392098897501909 350566935642002317910201)
                    ·
                      rfl

theorem cell22_1024090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1024090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024090 prefixEnd_1024090 := by exact prefixLift 1024090
  have htrace : WordTrace (prefixWord ++ tailWord_1024090) baseStart_1024090 baseEnd_1024090 := by
    simpa [prefixWord, tailWord_1024090, baseEnd_1024090] using wordTrace_append hprefix tailTrace_1024090
  have hstable : (prefixWord ++ tailWord_1024090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024090).length < 2 ^ (prefixWord ++ tailWord_1024090).sum := by decide
  have hdescent : baseEnd_1024090 < baseStart_1024090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024154 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_1024154 : Nat := 118140960795 + 1024154 * 2 ^ 59
def prefixEnd_1024154 : Nat := 4983230072969 + 3 ^ 40 * 1024154 * 2
def baseEnd_1024154 : Nat := 116862948049975828103335

theorem tailTrace_1024154 : CollatzResearch.WordTrace tailWord_1024154 prefixEnd_1024154 116862948049975828103335 := by
  unfold tailWord_1024154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338491282918111105721879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24902643421114962948591677 9338491282918111105721879)
  ·
    refine ⟨14007736924377166658582819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9338491282918111105721879 14007736924377166658582819)
    ·
      refine ⟨21011605386565749987874229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007736924377166658582819 21011605386565749987874229)
      ·
        refine ⟨1969838004990539061363209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21011605386565749987874229 1969838004990539061363209)
        ·
          refine ⟨1477378503742904296022407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1969838004990539061363209 1477378503742904296022407)
          ·
            refine ⟨2216067755614356444033611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477378503742904296022407 2216067755614356444033611)
            ·
              refine ⟨3324101633421534666050417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216067755614356444033611 3324101633421534666050417)
              ·
                refine ⟨2493076225066150999537813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324101633421534666050417 2493076225066150999537813)
                ·
                  refine ⟨116862948049975828103335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2493076225066150999537813 116862948049975828103335)
                  ·
                    rfl

theorem cell22_1024154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_1024154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024154 prefixEnd_1024154 := by exact prefixLift 1024154
  have htrace : WordTrace (prefixWord ++ tailWord_1024154) baseStart_1024154 baseEnd_1024154 := by
    simpa [prefixWord, tailWord_1024154, baseEnd_1024154] using wordTrace_append hprefix tailTrace_1024154
  have hstable : (prefixWord ++ tailWord_1024154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024154).length < 2 ^ (prefixWord ++ tailWord_1024154).sum := by decide
  have hdescent : baseEnd_1024154 < baseStart_1024154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024173 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1024173 : Nat := 118140960795 + 1024173 * 2 ^ 59
def prefixEnd_1024173 : Nat := 4983230072969 + 3 ^ 40 * 1024173 * 2
def baseEnd_1024173 : Nat := 350595348238217768084947

theorem tailTrace_1024173 : CollatzResearch.WordTrace tailWord_1024173 prefixEnd_1024173 350595348238217768084947 := by
  unfold tailWord_1024173
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354658118603610667829173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24903105412402407111886115 37354658118603610667829173)
  ·
    refine ⟨3501999198619088500108985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37354658118603610667829173 3501999198619088500108985)
    ·
      refine ⟨2626499398964316375081739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3501999198619088500108985 2626499398964316375081739)
      ·
        refine ⟨3939749098446474562622609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626499398964316375081739 3939749098446474562622609)
        ·
          refine ⟨2954811823834855921966957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3939749098446474562622609 2954811823834855921966957)
          ·
            refine ⟨1108054433938070970737609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2954811823834855921966957 1108054433938070970737609)
            ·
              refine ⟨831040825453553228053207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108054433938070970737609 831040825453553228053207)
              ·
                refine ⟨1246561238180329842079811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831040825453553228053207 1246561238180329842079811)
                ·
                  refine ⟨1869841857270494763119717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246561238180329842079811 1869841857270494763119717)
                  ·
                    refine ⟨350595348238217768084947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1869841857270494763119717 350595348238217768084947)
                    ·
                      rfl

theorem cell22_1024173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1024173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024173 prefixEnd_1024173 := by exact prefixLift 1024173
  have htrace : WordTrace (prefixWord ++ tailWord_1024173) baseStart_1024173 baseEnd_1024173 := by
    simpa [prefixWord, tailWord_1024173, baseEnd_1024173] using wordTrace_append hprefix tailTrace_1024173
  have hstable : (prefixWord ++ tailWord_1024173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024173).length < 2 ^ (prefixWord ++ tailWord_1024173).sum := by decide
  have hdescent : baseEnd_1024173 < baseStart_1024173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024291 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 1, 4]
def baseStart_1024291 : Nat := 118140960795 + 1024291 * 2 ^ 59
def prefixEnd_1024291 : Nat := 4983230072969 + 3 ^ 40 * 1024291 * 2
def baseEnd_1024291 : Nat := 350635742049704793634585

theorem tailTrace_1024291 : CollatzResearch.WordTrace tailWord_1024291 prefixEnd_1024291 350635742049704793634585 := by
  unfold tailWord_1024291
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358961932176116820624727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24905974621450744547083151 37358961932176116820624727)
  ·
    refine ⟨56038442898264175230937091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37358961932176116820624727 56038442898264175230937091)
    ·
      refine ⟨84057664347396262846405637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56038442898264175230937091 84057664347396262846405637)
      ·
        refine ⟨15760812065136799283701057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84057664347396262846405637 15760812065136799283701057)
        ·
          refine ⟨11820609048852599462775793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15760812065136799283701057 11820609048852599462775793)
          ·
            refine ⟨8865456786639449597081845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11820609048852599462775793 8865456786639449597081845)
            ·
              refine ⟨831136573747448399726423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8865456786639449597081845 831136573747448399726423)
              ·
                refine ⟨1246704860621172599589635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831136573747448399726423 1246704860621172599589635)
                ·
                  refine ⟨1870057290931758899384453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246704860621172599589635 1870057290931758899384453)
                  ·
                    refine ⟨350635742049704793634585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870057290931758899384453 350635742049704793634585)
                    ·
                      rfl

theorem cell22_1024291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 4].length) (baseStart_1024291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024291 prefixEnd_1024291 := by exact prefixLift 1024291
  have htrace : WordTrace (prefixWord ++ tailWord_1024291) baseStart_1024291 baseEnd_1024291 := by
    simpa [prefixWord, tailWord_1024291, baseEnd_1024291] using wordTrace_append hprefix tailTrace_1024291
  have hstable : (prefixWord ++ tailWord_1024291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024291).length < 2 ^ (prefixWord ++ tailWord_1024291).sum := by decide
  have hdescent : baseEnd_1024291 < baseStart_1024291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024295 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 5]
def baseStart_1024295 : Nat := 118140960795 + 1024295 * 2 ^ 59
def prefixEnd_1024295 : Nat := 4983230072969 + 3 ^ 40 * 1024295 * 2
def baseEnd_1024295 : Nat := 116879037110483372178191

theorem tailTrace_1024295 : CollatzResearch.WordTrace tailWord_1024295 prefixEnd_1024295 116879037110483372178191 := by
  unfold tailWord_1024295
  simp only [CollatzResearch.WordTrace]
  refine ⟨37359107824161625503770339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24906071882774417002513559 37359107824161625503770339)
  ·
    refine ⟨56038661736242438255655509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37359107824161625503770339 56038661736242438255655509)
    ·
      refine ⟨656703067221591073308463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 56038661736242438255655509 656703067221591073308463)
      ·
        refine ⟨985054600832386609962695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656703067221591073308463 985054600832386609962695)
        ·
          refine ⟨1477581901248579914944043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985054600832386609962695 1477581901248579914944043)
          ·
            refine ⟨2216372851872869872416065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477581901248579914944043 2216372851872869872416065)
            ·
              refine ⟨1662279638904652404312049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216372851872869872416065 1662279638904652404312049)
              ·
                refine ⟨1246709729178489303234037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662279638904652404312049 1246709729178489303234037)
                ·
                  refine ⟨116879037110483372178191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246709729178489303234037 116879037110483372178191)
                  ·
                    rfl

theorem cell22_1024295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 5].length) (baseStart_1024295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024295 prefixEnd_1024295 := by exact prefixLift 1024295
  have htrace : WordTrace (prefixWord ++ tailWord_1024295) baseStart_1024295 baseEnd_1024295 := by
    simpa [prefixWord, tailWord_1024295, baseEnd_1024295] using wordTrace_append hprefix tailTrace_1024295
  have hstable : (prefixWord ++ tailWord_1024295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024295).length < 2 ^ (prefixWord ++ tailWord_1024295).sum := by decide
  have hdescent : baseEnd_1024295 < baseStart_1024295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024336 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_1024336 : Nat := 118140960795 + 1024336 * 2 ^ 59
def prefixEnd_1024336 : Nat := 4983230072969 + 3 ^ 40 * 1024336 * 2
def baseEnd_1024336 : Nat := 350651146469339676259447

theorem tailTrace_1024336 : CollatzResearch.WordTrace tailWord_1024336 prefixEnd_1024336 350651146469339676259447 := by
  unfold tailWord_1024336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680301608506544753006431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24907068811342059670675241 18680301608506544753006431)
  ·
    refine ⟨28020452412759817129509647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680301608506544753006431 28020452412759817129509647)
    ·
      refine ⟨42030678619139725694264471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28020452412759817129509647 42030678619139725694264471)
      ·
        refine ⟨63046017928709588541396707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42030678619139725694264471 63046017928709588541396707)
        ·
          refine ⟨94569026893064382812095061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63046017928709588541396707 94569026893064382812095061)
          ·
            refine ⟨1108230783903098236079239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 94569026893064382812095061 1108230783903098236079239)
            ·
              refine ⟨1662346175854647354118859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108230783903098236079239 1662346175854647354118859)
              ·
                refine ⟨2493519263781971031178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662346175854647354118859 2493519263781971031178289)
                ·
                  refine ⟨1870139447836478273383717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493519263781971031178289 1870139447836478273383717)
                  ·
                    refine ⟨350651146469339676259447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870139447836478273383717 350651146469339676259447)
                    ·
                      rfl

theorem cell22_1024336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_1024336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024336 prefixEnd_1024336 := by exact prefixLift 1024336
  have htrace : WordTrace (prefixWord ++ tailWord_1024336) baseStart_1024336 baseEnd_1024336 := by
    simpa [prefixWord, tailWord_1024336, baseEnd_1024336] using wordTrace_append hprefix tailTrace_1024336
  have hstable : (prefixWord ++ tailWord_1024336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024336).length < 2 ^ (prefixWord ++ tailWord_1024336).sum := by decide
  have hdescent : baseEnd_1024336 < baseStart_1024336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024417 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1024417 : Nat := 118140960795 + 1024417 * 2 ^ 59
def prefixEnd_1024417 : Nat := 4983230072969 + 3 ^ 40 * 1024417 * 2
def baseEnd_1024417 : Nat := 350678874424682464984199

theorem tailTrace_1024417 : CollatzResearch.WordTrace tailWord_1024417 prefixEnd_1024417 350678874424682464984199 := by
  unfold tailWord_1024417
  simp only [CollatzResearch.WordTrace]
  refine ⟨37363557529719640339711505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24909038353146426893141003 37363557529719640339711505)
  ·
    refine ⟨28022668147289730254783629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37363557529719640339711505 28022668147289730254783629)
    ·
      refine ⟨10508500555233648845543861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28022668147289730254783629 10508500555233648845543861)
      ·
        refine ⟨985171927053154579269737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10508500555233648845543861 985171927053154579269737)
        ·
          refine ⟨738878945289865934452303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985171927053154579269737 738878945289865934452303)
          ·
            refine ⟨1108318417934798901678455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738878945289865934452303 1108318417934798901678455)
            ·
              refine ⟨1662477626902198352517683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108318417934798901678455 1662477626902198352517683)
              ·
                refine ⟨2493716440353297528776525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662477626902198352517683 2493716440353297528776525)
                ·
                  refine ⟨935143665132486573291197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2493716440353297528776525 935143665132486573291197)
                  ·
                    refine ⟨350678874424682464984199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935143665132486573291197 350678874424682464984199)
                    ·
                      rfl

theorem cell22_1024417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1024417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024417 prefixEnd_1024417 := by exact prefixLift 1024417
  have htrace : WordTrace (prefixWord ++ tailWord_1024417) baseStart_1024417 baseEnd_1024417 := by
    simpa [prefixWord, tailWord_1024417, baseEnd_1024417] using wordTrace_append hprefix tailTrace_1024417
  have hstable : (prefixWord ++ tailWord_1024417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024417).length < 2 ^ (prefixWord ++ tailWord_1024417).sum := by decide
  have hdescent : baseEnd_1024417 < baseStart_1024417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024456 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1024456 : Nat := 118140960795 + 1024456 * 2 ^ 59
def prefixEnd_1024456 : Nat := 4983230072969 + 3 ^ 40 * 1024456 * 2
def baseEnd_1024456 : Nat := 350692224921699363259079

theorem tailTrace_1024456 : CollatzResearch.WordTrace tailWord_1024456 prefixEnd_1024456 350692224921699363259079 := by
  unfold tailWord_1024456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682489988289175000190611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24909986651052233333587481 18682489988289175000190611)
  ·
    refine ⟨28023734982433762500285917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18682489988289175000190611 28023734982433762500285917)
    ·
      refine ⟨10508900618412660937607219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28023734982433762500285917 10508900618412660937607219)
      ·
        refine ⟨15763350927618991406410829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10508900618412660937607219 15763350927618991406410829)
        ·
          refine ⟨5911256597857121777404061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15763350927618991406410829 5911256597857121777404061)
          ·
            refine ⟨2216721224196420666526523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5911256597857121777404061 2216721224196420666526523)
            ·
              refine ⟨3325081836294630999789785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216721224196420666526523 3325081836294630999789785)
              ·
                refine ⟨2493811377220973249842339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325081836294630999789785 2493811377220973249842339)
                ·
                  refine ⟨3740717065831459874763509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493811377220973249842339 3740717065831459874763509)
                  ·
                    refine ⟨350692224921699363259079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3740717065831459874763509 350692224921699363259079)
                    ·
                      rfl

theorem cell22_1024456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1024456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024456 prefixEnd_1024456 := by exact prefixLift 1024456
  have htrace : WordTrace (prefixWord ++ tailWord_1024456) baseStart_1024456 baseEnd_1024456 := by
    simpa [prefixWord, tailWord_1024456, baseEnd_1024456] using wordTrace_append hprefix tailTrace_1024456
  have hstable : (prefixWord ++ tailWord_1024456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024456).length < 2 ^ (prefixWord ++ tailWord_1024456).sum := by decide
  have hdescent : baseEnd_1024456 < baseStart_1024456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024460 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_1024460 : Nat := 118140960795 + 1024460 * 2 ^ 59
def prefixEnd_1024460 : Nat := 4983230072969 + 3 ^ 40 * 1024460 * 2
def baseEnd_1024460 : Nat := 350693594203444686159067

theorem tailTrace_1024460 : CollatzResearch.WordTrace tailWord_1024460 prefixEnd_1024460 350693594203444686159067 := by
  unfold tailWord_1024460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682562934281929341763417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24910083912375905789017889 18682562934281929341763417)
  ·
    refine ⟨14011922200711447006322563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18682562934281929341763417 14011922200711447006322563)
    ·
      refine ⟨21017883301067170509483845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14011922200711447006322563 21017883301067170509483845)
      ·
        refine ⟨3940853118950094470528221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21017883301067170509483845 3940853118950094470528221)
        ·
          refine ⟨1477819919606285426448083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3940853118950094470528221 1477819919606285426448083)
          ·
            refine ⟨2216729879409428139672125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477819919606285426448083 2216729879409428139672125)
            ·
              refine ⟨831273704778535552377047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216729879409428139672125 831273704778535552377047)
              ·
                refine ⟨1246910557167803328565571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831273704778535552377047 1246910557167803328565571)
                ·
                  refine ⟨1870365835751704992848357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246910557167803328565571 1870365835751704992848357)
                  ·
                    refine ⟨350693594203444686159067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870365835751704992848357 350693594203444686159067)
                    ·
                      rfl

theorem cell22_1024460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_1024460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024460 prefixEnd_1024460 := by exact prefixLift 1024460
  have htrace : WordTrace (prefixWord ++ tailWord_1024460) baseStart_1024460 baseEnd_1024460 := by
    simpa [prefixWord, tailWord_1024460, baseEnd_1024460] using wordTrace_append hprefix tailTrace_1024460
  have hstable : (prefixWord ++ tailWord_1024460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024460).length < 2 ^ (prefixWord ++ tailWord_1024460).sum := by decide
  have hdescent : baseEnd_1024460 < baseStart_1024460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024469 : List Nat := [1, 3, 2, 3, 1, 12]
def baseStart_1024469 : Nat := 118140960795 + 1024469 * 2 ^ 59
def prefixEnd_1024469 : Nat := 4983230072969 + 3 ^ 40 * 1024469 * 2
def baseEnd_1024469 : Nat := 4329588581325576082519

theorem tailTrace_1024469 : CollatzResearch.WordTrace tailWord_1024469 prefixEnd_1024469 4329588581325576082519 := by
  unfold tailWord_1024469
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365454125531253220604461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910302750354168813736307 37365454125531253220604461)
  ·
    refine ⟨14012045297074219957726673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37365454125531253220604461 14012045297074219957726673)
    ·
      refine ⟨10509033972805664968295005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14012045297074219957726673 10509033972805664968295005)
      ·
        refine ⟨3940887739802124363110627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10509033972805664968295005 3940887739802124363110627)
        ·
          refine ⟨5911331609703186544665941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940887739802124363110627 5911331609703186544665941)
          ·
            refine ⟨4329588581325576082519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5911331609703186544665941 4329588581325576082519)
            ·
              rfl

theorem cell22_1024469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 12].length) (baseStart_1024469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024469 prefixEnd_1024469 := by exact prefixLift 1024469
  have htrace : WordTrace (prefixWord ++ tailWord_1024469) baseStart_1024469 baseEnd_1024469 := by
    simpa [prefixWord, tailWord_1024469, baseEnd_1024469] using wordTrace_append hprefix tailTrace_1024469
  have hstable : (prefixWord ++ tailWord_1024469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024469).length < 2 ^ (prefixWord ++ tailWord_1024469).sum := by decide
  have hdescent : baseEnd_1024469 < baseStart_1024469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024473 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_1024473 : Nat := 118140960795 + 1024473 * 2 ^ 59
def prefixEnd_1024473 : Nat := 4983230072969 + 3 ^ 40 * 1024473 * 2
def baseEnd_1024473 : Nat := 350698044369116985584027

theorem tailTrace_1024473 : CollatzResearch.WordTrace tailWord_1024473 prefixEnd_1024473 350698044369116985584027 := by
  unfold tailWord_1024473
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365600017516761903750073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910400011677841269166715 37365600017516761903750073)
  ·
    refine ⟨28024200013137571427812555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37365600017516761903750073 28024200013137571427812555)
    ·
      refine ⟨42036300019706357141718833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28024200013137571427812555 42036300019706357141718833)
      ·
        refine ⟨31527225014779767856289125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42036300019706357141718833 31527225014779767856289125)
        ·
          refine ⟨5911354690271206473054211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31527225014779767856289125 5911354690271206473054211)
          ·
            refine ⟨8867032035406809709581317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911354690271206473054211 8867032035406809709581317)
            ·
              refine ⟨1662568506638776820546497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8867032035406809709581317 1662568506638776820546497)
              ·
                refine ⟨1246926379979082615409873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662568506638776820546497 1246926379979082615409873)
                ·
                  refine ⟨935194784984311961557405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1246926379979082615409873 935194784984311961557405)
                  ·
                    refine ⟨350698044369116985584027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935194784984311961557405 350698044369116985584027)
                    ·
                      rfl

theorem cell22_1024473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_1024473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024473 prefixEnd_1024473 := by exact prefixLift 1024473
  have htrace : WordTrace (prefixWord ++ tailWord_1024473) baseStart_1024473 baseEnd_1024473 := by
    simpa [prefixWord, tailWord_1024473, baseEnd_1024473] using wordTrace_append hprefix tailTrace_1024473
  have hstable : (prefixWord ++ tailWord_1024473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024473).length < 2 ^ (prefixWord ++ tailWord_1024473).sum := by decide
  have hdescent : baseEnd_1024473 < baseStart_1024473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024484 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1024484 : Nat := 118140960795 + 1024484 * 2 ^ 59
def prefixEnd_1024484 : Nat := 4983230072969 + 3 ^ 40 * 1024484 * 2
def baseEnd_1024484 : Nat := 350701809893916623558993

theorem tailTrace_1024484 : CollatzResearch.WordTrace tailWord_1024484 prefixEnd_1024484 350701809893916623558993 := by
  unfold tailWord_1024484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683000610238455391200253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24910667480317940521600337 18683000610238455391200253)
  ·
    refine ⟨7006125228839420771700095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18683000610238455391200253 7006125228839420771700095)
    ·
      refine ⟨10509187843259131157550143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006125228839420771700095 10509187843259131157550143)
      ·
        refine ⟨15763781764888696736325215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509187843259131157550143 15763781764888696736325215)
        ·
          refine ⟨23645672647333045104487823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15763781764888696736325215 23645672647333045104487823)
          ·
            refine ⟨35468508970999567656731735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645672647333045104487823 35468508970999567656731735)
            ·
              refine ⟨53202763456499351485097603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35468508970999567656731735 53202763456499351485097603)
              ·
                refine ⟨79804145184749027227646405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53202763456499351485097603 79804145184749027227646405)
                ·
                  refine ⟨14963277222140442605183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79804145184749027227646405 14963277222140442605183701)
                  ·
                    refine ⟨350701809893916623558993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14963277222140442605183701 350701809893916623558993)
                    ·
                      rfl

theorem cell22_1024484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1024484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024484 prefixEnd_1024484 := by exact prefixLift 1024484
  have htrace : WordTrace (prefixWord ++ tailWord_1024484) baseStart_1024484 baseEnd_1024484 := by
    simpa [prefixWord, tailWord_1024484, baseEnd_1024484] using wordTrace_append hprefix tailTrace_1024484
  have hstable : (prefixWord ++ tailWord_1024484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024484).length < 2 ^ (prefixWord ++ tailWord_1024484).sum := by decide
  have hdescent : baseEnd_1024484 < baseStart_1024484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024499 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_1024499 : Nat := 118140960795 + 1024499 * 2 ^ 59
def prefixEnd_1024499 : Nat := 4983230072969 + 3 ^ 40 * 1024499 * 2
def baseEnd_1024499 : Nat := 350706944700461584433947

theorem tailTrace_1024499 : CollatzResearch.WordTrace tailWord_1024499 prefixEnd_1024499 350706944700461584433947 := by
  unfold tailWord_1024499
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366548315422568344196551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24911032210281712229464367 37366548315422568344196551)
  ·
    refine ⟨56049822473133852516294827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37366548315422568344196551 56049822473133852516294827)
    ·
      refine ⟨84074733709700778774442241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56049822473133852516294827 84074733709700778774442241)
      ·
        refine ⟨63056050282275584080831681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84074733709700778774442241 63056050282275584080831681)
        ·
          refine ⟨47292037711706688060623761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63056050282275584080831681 47292037711706688060623761)
          ·
            refine ⟨35469028283780016045467821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47292037711706688060623761 35469028283780016045467821)
            ·
              refine ⟨13300885606417506017050433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35469028283780016045467821 13300885606417506017050433)
              ·
                refine ⟨9975664204813129512787825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13300885606417506017050433 9975664204813129512787825)
                ·
                  refine ⟨7481748153609847134590869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9975664204813129512787825 7481748153609847134590869)
                  ·
                    refine ⟨350706944700461584433947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7481748153609847134590869 350706944700461584433947)
                    ·
                      rfl

theorem cell22_1024499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_1024499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024499 prefixEnd_1024499 := by exact prefixLift 1024499
  have htrace : WordTrace (prefixWord ++ tailWord_1024499) baseStart_1024499 baseEnd_1024499 := by
    simpa [prefixWord, tailWord_1024499, baseEnd_1024499] using wordTrace_append hprefix tailTrace_1024499
  have hstable : (prefixWord ++ tailWord_1024499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024499).length < 2 ^ (prefixWord ++ tailWord_1024499).sum := by decide
  have hdescent : baseEnd_1024499 < baseStart_1024499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024561 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1024561 : Nat := 118140960795 + 1024561 * 2 ^ 59
def prefixEnd_1024561 : Nat := 4983230072969 + 3 ^ 40 * 1024561 * 2
def baseEnd_1024561 : Nat := 350728168567514089383757

theorem tailTrace_1024561 : CollatzResearch.WordTrace tailWord_1024561 prefixEnd_1024561 350728168567514089383757 := by
  unfold tailWord_1024561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37368809641197952932953537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24912539760798635288635691 37368809641197952932953537)
  ·
    refine ⟨28026607230898464699715153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37368809641197952932953537 28026607230898464699715153)
    ·
      refine ⟨21019955423173848524786365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28026607230898464699715153 21019955423173848524786365)
      ·
        refine ⟨7882483283690193196794887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21019955423173848524786365 7882483283690193196794887)
        ·
          refine ⟨11823724925535289795192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882483283690193196794887 11823724925535289795192331)
          ·
            refine ⟨17735587388302934692788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823724925535289795192331 17735587388302934692788497)
            ·
              refine ⟨13301690541227201019591373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735587388302934692788497 13301690541227201019591373)
              ·
                refine ⟨4988133952960200382346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301690541227201019591373 4988133952960200382346765)
                ·
                  refine ⟨1870550232360075143380037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4988133952960200382346765 1870550232360075143380037)
                  ·
                    refine ⟨350728168567514089383757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870550232360075143380037 350728168567514089383757)
                    ·
                      rfl

theorem cell22_1024561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1024561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024561 prefixEnd_1024561 := by exact prefixLift 1024561
  have htrace : WordTrace (prefixWord ++ tailWord_1024561) baseStart_1024561 baseEnd_1024561 := by
    simpa [prefixWord, tailWord_1024561, baseEnd_1024561] using wordTrace_append hprefix tailTrace_1024561
  have hstable : (prefixWord ++ tailWord_1024561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024561).length < 2 ^ (prefixWord ++ tailWord_1024561).sum := by decide
  have hdescent : baseEnd_1024561 < baseStart_1024561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024593 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 6]
def baseStart_1024593 : Nat := 118140960795 + 1024593 * 2 ^ 59
def prefixEnd_1024593 : Nat := 4983230072969 + 3 ^ 40 * 1024593 * 2
def baseEnd_1024593 : Nat := 116913040940492224194553

theorem tailTrace_1024593 : CollatzResearch.WordTrace tailWord_1024593 prefixEnd_1024593 116913040940492224194553 := by
  unfold tailWord_1024593
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369976777082022398118433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24913317851388014932078955 37369976777082022398118433)
  ·
    refine ⟨28027482582811516798588825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37369976777082022398118433 28027482582811516798588825)
    ·
      refine ⟨21020611937108637598941619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28027482582811516798588825 21020611937108637598941619)
      ·
        refine ⟨31530917905662956398412429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21020611937108637598941619 31530917905662956398412429)
        ·
          refine ⟨11824094214623608649404661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31530917905662956398412429 11824094214623608649404661)
          ·
            refine ⟨1108508832620963310881687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11824094214623608649404661 1108508832620963310881687)
            ·
              refine ⟨1662763248931444966322531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108508832620963310881687 1662763248931444966322531)
              ·
                refine ⟨2494144873397167449483797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662763248931444966322531 2494144873397167449483797)
                ·
                  refine ⟨116913040940492224194553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2494144873397167449483797 116913040940492224194553)
                  ·
                    rfl

theorem cell22_1024593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_1024593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024593 prefixEnd_1024593 := by exact prefixLift 1024593
  have htrace : WordTrace (prefixWord ++ tailWord_1024593) baseStart_1024593 baseEnd_1024593 := by
    simpa [prefixWord, tailWord_1024593, baseEnd_1024593] using wordTrace_append hprefix tailTrace_1024593
  have hstable : (prefixWord ++ tailWord_1024593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024593).length < 2 ^ (prefixWord ++ tailWord_1024593).sum := by decide
  have hdescent : baseEnd_1024593 < baseStart_1024593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024681 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1024681 : Nat := 118140960795 + 1024681 * 2 ^ 59
def prefixEnd_1024681 : Nat := 4983230072969 + 3 ^ 40 * 1024681 * 2
def baseEnd_1024681 : Nat := 350769247019873776383389

theorem tailTrace_1024681 : CollatzResearch.WordTrace tailWord_1024681 prefixEnd_1024681 350769247019873776383389 := by
  unfold tailWord_1024681
  simp only [CollatzResearch.WordTrace]
  refine ⟨37373186400763213427321897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24915457600508808951547931 37373186400763213427321897)
  ·
    refine ⟨28029889800572410070491423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37373186400763213427321897 28029889800572410070491423)
    ·
      refine ⟨42044834700858615105737135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28029889800572410070491423 42044834700858615105737135)
      ·
        refine ⟨63067252051287922658605703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42044834700858615105737135 63067252051287922658605703)
        ·
          refine ⟨94600878076931883987908555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63067252051287922658605703 94600878076931883987908555)
          ·
            refine ⟨141901317115397825981862833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94600878076931883987908555 141901317115397825981862833)
            ·
              refine ⟨106425987836548369486397125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141901317115397825981862833 106425987836548369486397125)
              ·
                refine ⟨19954872719352819278699461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106425987836548369486397125 19954872719352819278699461)
                ·
                  refine ⟨3741538634878653614756149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19954872719352819278699461 3741538634878653614756149)
                  ·
                    refine ⟨350769247019873776383389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3741538634878653614756149 350769247019873776383389)
                    ·
                      rfl

theorem cell22_1024681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1024681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024681 prefixEnd_1024681 := by exact prefixLift 1024681
  have htrace : WordTrace (prefixWord ++ tailWord_1024681) baseStart_1024681 baseEnd_1024681 := by
    simpa [prefixWord, tailWord_1024681, baseEnd_1024681] using wordTrace_append hprefix tailTrace_1024681
  have hstable : (prefixWord ++ tailWord_1024681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024681).length < 2 ^ (prefixWord ++ tailWord_1024681).sum := by decide
  have hdescent : baseEnd_1024681 < baseStart_1024681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024687 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 1, 3]
def baseStart_1024687 : Nat := 118140960795 + 1024687 * 2 ^ 59
def prefixEnd_1024687 : Nat := 4983230072969 + 3 ^ 40 * 1024687 * 2
def baseEnd_1024687 : Nat := 350771300942491760733371

theorem tailTrace_1024687 : CollatzResearch.WordTrace tailWord_1024687 prefixEnd_1024687 350771300942491760733371 := by
  unfold tailWord_1024687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37373405238741476452040315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24915603492494317634693543 37373405238741476452040315)
  ·
    refine ⟨56060107858112214678060473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37373405238741476452040315 56060107858112214678060473)
    ·
      refine ⟨42045080893584161008545355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56060107858112214678060473 42045080893584161008545355)
      ·
        refine ⟨63067621340376241512818033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42045080893584161008545355 63067621340376241512818033)
        ·
          refine ⟨47300716005282181134613525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63067621340376241512818033 47300716005282181134613525)
          ·
            refine ⟨2217221062747602240685009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47300716005282181134613525 2217221062747602240685009)
            ·
              refine ⟨1662915797060701680513757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217221062747602240685009 1662915797060701680513757)
              ·
                refine ⟨623593423897763130192659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1662915797060701680513757 623593423897763130192659)
                ·
                  refine ⟨935390135846644695288989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623593423897763130192659 935390135846644695288989)
                  ·
                    refine ⟨350771300942491760733371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935390135846644695288989 350771300942491760733371)
                    ·
                      rfl

theorem cell22_1024687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_1024687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024687 prefixEnd_1024687 := by exact prefixLift 1024687
  have htrace : WordTrace (prefixWord ++ tailWord_1024687) baseStart_1024687 baseEnd_1024687 := by
    simpa [prefixWord, tailWord_1024687, baseEnd_1024687] using wordTrace_append hprefix tailTrace_1024687
  have hstable : (prefixWord ++ tailWord_1024687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024687).length < 2 ^ (prefixWord ++ tailWord_1024687).sum := by decide
  have hdescent : baseEnd_1024687 < baseStart_1024687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024728 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_1024728 : Nat := 118140960795 + 1024728 * 2 ^ 59
def prefixEnd_1024728 : Nat := 4983230072969 + 3 ^ 40 * 1024728 * 2
def baseEnd_1024728 : Nat := 116928445360127106819415

theorem tailTrace_1024728 : CollatzResearch.WordTrace tailWord_1024728 prefixEnd_1024728 116928445360127106819415 := by
  unfold tailWord_1024728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687450315796470227141419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24916600421061960302855225 18687450315796470227141419)
  ·
    refine ⟨28031175473694705340712129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18687450315796470227141419 28031175473694705340712129)
    ·
      refine ⟨21023381605271029005534097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28031175473694705340712129 21023381605271029005534097)
      ·
        refine ⟨15767536203953271754150573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21023381605271029005534097 15767536203953271754150573)
        ·
          refine ⟨5912826076482476907806465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15767536203953271754150573 5912826076482476907806465)
          ·
            refine ⟨4434619557361857680854849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5912826076482476907806465 4434619557361857680854849)
            ·
              refine ⟨3325964668021393260641137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434619557361857680854849 3325964668021393260641137)
              ·
                refine ⟨2494473501016044945480853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325964668021393260641137 2494473501016044945480853)
                ·
                  refine ⟨116928445360127106819415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2494473501016044945480853 116928445360127106819415)
                  ·
                    rfl

theorem cell22_1024728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_1024728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024728 prefixEnd_1024728 := by exact prefixLift 1024728
  have htrace : WordTrace (prefixWord ++ tailWord_1024728) baseStart_1024728 baseEnd_1024728 := by
    simpa [prefixWord, tailWord_1024728, baseEnd_1024728] using wordTrace_append hprefix tailTrace_1024728
  have hstable : (prefixWord ++ tailWord_1024728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024728).length < 2 ^ (prefixWord ++ tailWord_1024728).sum := by decide
  have hdescent : baseEnd_1024728 < baseStart_1024728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024730 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_1024730 : Nat := 118140960795 + 1024730 * 2 ^ 59
def prefixEnd_1024730 : Nat := 4983230072969 + 3 ^ 40 * 1024730 * 2
def baseEnd_1024730 : Nat := 350786020721253981908239

theorem tailTrace_1024730 : CollatzResearch.WordTrace tailWord_1024730 prefixEnd_1024730 350786020721253981908239 := by
  unfold tailWord_1024730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343743394396423698963911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24916649051723796530570429 9343743394396423698963911)
  ·
    refine ⟨14015615091594635548445867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343743394396423698963911 14015615091594635548445867)
    ·
      refine ⟨21023422637391953322668801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015615091594635548445867 21023422637391953322668801)
      ·
        refine ⟨15767566978043964992001601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21023422637391953322668801 15767566978043964992001601)
        ·
          refine ⟨11825675233532973744001201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15767566978043964992001601 11825675233532973744001201)
          ·
            refine ⟨8869256425149730308000901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825675233532973744001201 8869256425149730308000901)
            ·
              refine ⟨1662985579715574432750169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8869256425149730308000901 1662985579715574432750169)
              ·
                refine ⟨1247239184786680824562627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662985579715574432750169 1247239184786680824562627)
                ·
                  refine ⟨1870858777180021236843941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247239184786680824562627 1870858777180021236843941)
                  ·
                    refine ⟨350786020721253981908239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1870858777180021236843941 350786020721253981908239)
                    ·
                      rfl

theorem cell22_1024730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_1024730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024730 prefixEnd_1024730 := by exact prefixLift 1024730
  have htrace : WordTrace (prefixWord ++ tailWord_1024730) baseStart_1024730 baseEnd_1024730 := by
    simpa [prefixWord, tailWord_1024730, baseEnd_1024730] using wordTrace_append hprefix tailTrace_1024730
  have hstable : (prefixWord ++ tailWord_1024730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024730).length < 2 ^ (prefixWord ++ tailWord_1024730).sum := by decide
  have hdescent : baseEnd_1024730 < baseStart_1024730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024745 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 4]
def baseStart_1024745 : Nat := 118140960795 + 1024745 * 2 ^ 59
def prefixEnd_1024745 : Nat := 4983230072969 + 3 ^ 40 * 1024745 * 2
def baseEnd_1024745 : Nat := 116930385175932980927731

theorem tailTrace_1024745 : CollatzResearch.WordTrace tailWord_1024745 prefixEnd_1024745 116930385175932980927731 := by
  unfold tailWord_1024745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37375520672531352357651689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24917013781687568238434459 37375520672531352357651689)
  ·
    refine ⟨28031640504398514268238767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37375520672531352357651689 28031640504398514268238767)
    ·
      refine ⟨42047460756597771402358151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28031640504398514268238767 42047460756597771402358151)
      ·
        refine ⟨63071191134896657103537227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42047460756597771402358151 63071191134896657103537227)
        ·
          refine ⟨94606786702344985655305841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63071191134896657103537227 94606786702344985655305841)
          ·
            refine ⟨70955090026758739241479381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94606786702344985655305841 70955090026758739241479381)
            ·
              refine ⟨1663009922502157950972173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70955090026758739241479381 1663009922502157950972173)
              ·
                refine ⟨623628720938309231614565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663009922502157950972173 623628720938309231614565)
                ·
                  refine ⟨116930385175932980927731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623628720938309231614565 116930385175932980927731)
                  ·
                    rfl

theorem cell22_1024745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_1024745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024745 prefixEnd_1024745 := by exact prefixLift 1024745
  have htrace : WordTrace (prefixWord ++ tailWord_1024745) baseStart_1024745 baseEnd_1024745 := by
    simpa [prefixWord, tailWord_1024745, baseEnd_1024745] using wordTrace_append hprefix tailTrace_1024745
  have hstable : (prefixWord ++ tailWord_1024745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024745).length < 2 ^ (prefixWord ++ tailWord_1024745).sum := by decide
  have hdescent : baseEnd_1024745 < baseStart_1024745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024760 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1024760 : Nat := 118140960795 + 1024760 * 2 ^ 59
def prefixEnd_1024760 : Nat := 4983230072969 + 3 ^ 40 * 1024760 * 2
def baseEnd_1024760 : Nat := 350796290334343903658147

theorem tailTrace_1024760 : CollatzResearch.WordTrace tailWord_1024760 prefixEnd_1024760 350796290334343903658147 := by
  unfold tailWord_1024760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688033883738504959723867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24917378511651339946298489 18688033883738504959723867)
  ·
    refine ⟨28032050825607757439585801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18688033883738504959723867 28032050825607757439585801)
    ·
      refine ⟨21024038119205818079689351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28032050825607757439585801 21024038119205818079689351)
      ·
        refine ⟨31536057178808727119534027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21024038119205818079689351 31536057178808727119534027)
        ·
          refine ⟨47304085768213090679301041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31536057178808727119534027 47304085768213090679301041)
          ·
            refine ⟨35478064326159818009475781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47304085768213090679301041 35478064326159818009475781)
            ·
              refine ⟨6652137061154965876776709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35478064326159818009475781 6652137061154965876776709)
              ·
                refine ⟨1247275698966556101895633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6652137061154965876776709 1247275698966556101895633)
                ·
                  refine ⟨935456774224917076421725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247275698966556101895633 935456774224917076421725)
                  ·
                    refine ⟨350796290334343903658147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935456774224917076421725 350796290334343903658147)
                    ·
                      rfl

theorem cell22_1024760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1024760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024760 prefixEnd_1024760 := by exact prefixLift 1024760
  have htrace : WordTrace (prefixWord ++ tailWord_1024760) baseStart_1024760 baseEnd_1024760 := by
    simpa [prefixWord, tailWord_1024760, baseEnd_1024760] using wordTrace_append hprefix tailTrace_1024760
  have hstable : (prefixWord ++ tailWord_1024760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024760).length < 2 ^ (prefixWord ++ tailWord_1024760).sum := by decide
  have hdescent : baseEnd_1024760 < baseStart_1024760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024777 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_1024777 : Nat := 118140960795 + 1024777 * 2 ^ 59
def prefixEnd_1024777 : Nat := 4983230072969 + 3 ^ 40 * 1024777 * 2
def baseEnd_1024777 : Nat := 350802109781761525983095

theorem tailTrace_1024777 : CollatzResearch.WordTrace tailWord_1024777 prefixEnd_1024777 350802109781761525983095 := by
  unfold tailWord_1024777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37376687808415421822816585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24917791872276947881877723 37376687808415421822816585)
  ·
    refine ⟨28032515856311566367112439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37376687808415421822816585 28032515856311566367112439)
    ·
      refine ⟨42048773784467349550668659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28032515856311566367112439 42048773784467349550668659)
      ·
        refine ⟨63073160676701024326002989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42048773784467349550668659 63073160676701024326002989)
        ·
          refine ⟨23652435253762884122251121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63073160676701024326002989 23652435253762884122251121)
          ·
            refine ⟨17739326440322163091688341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23652435253762884122251121 17739326440322163091688341)
            ·
              refine ⟨831530926890101394922891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17739326440322163091688341 831530926890101394922891)
              ·
                refine ⟨1247296390335152092384337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831530926890101394922891 1247296390335152092384337)
                ·
                  refine ⟨935472292751364069288253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247296390335152092384337 935472292751364069288253)
                  ·
                    refine ⟨350802109781761525983095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935472292751364069288253 350802109781761525983095)
                    ·
                      rfl

theorem cell22_1024777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_1024777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024777 prefixEnd_1024777 := by exact prefixLift 1024777
  have htrace : WordTrace (prefixWord ++ tailWord_1024777) baseStart_1024777 baseEnd_1024777 := by
    simpa [prefixWord, tailWord_1024777, baseEnd_1024777] using wordTrace_append hprefix tailTrace_1024777
  have hstable : (prefixWord ++ tailWord_1024777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024777).length < 2 ^ (prefixWord ++ tailWord_1024777).sum := by decide
  have hdescent : baseEnd_1024777 < baseStart_1024777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024813 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1024813 : Nat := 118140960795 + 1024813 * 2 ^ 59
def prefixEnd_1024813 : Nat := 4983230072969 + 3 ^ 40 * 1024813 * 2
def baseEnd_1024813 : Nat := 116938144439156477360995

theorem tailTrace_1024813 : CollatzResearch.WordTrace tailWord_1024813 prefixEnd_1024813 116938144439156477360995 := by
  unfold tailWord_1024813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37378000836284999971127093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24918667224189999980751395 37378000836284999971127093)
  ·
    refine ⟨3504187578401718747293165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37378000836284999971127093 3504187578401718747293165)
    ·
      refine ⟨1314070341900644530234937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3504187578401718747293165 1314070341900644530234937)
      ·
        refine ⟨985552756425483397676203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314070341900644530234937 985552756425483397676203)
        ·
          refine ⟨1478329134638225096514305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985552756425483397676203 1478329134638225096514305)
          ·
            refine ⟨1108746850978668822385729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478329134638225096514305 1108746850978668822385729)
            ·
              refine ⟨831560138234001616789297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108746850978668822385729 831560138234001616789297)
              ·
                refine ⟨623670103675501212591973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831560138234001616789297 623670103675501212591973)
                ·
                  refine ⟨116938144439156477360995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623670103675501212591973 116938144439156477360995)
                  ·
                    rfl

theorem cell22_1024813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1024813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024813 prefixEnd_1024813 := by exact prefixLift 1024813
  have htrace : WordTrace (prefixWord ++ tailWord_1024813) baseStart_1024813 baseEnd_1024813 := by
    simpa [prefixWord, tailWord_1024813, baseEnd_1024813] using wordTrace_append hprefix tailTrace_1024813
  have hstable : (prefixWord ++ tailWord_1024813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024813).length < 2 ^ (prefixWord ++ tailWord_1024813).sum := by decide
  have hdescent : baseEnd_1024813 < baseStart_1024813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024863 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 8]
def baseStart_1024863 : Nat := 118140960795 + 1024863 * 2 ^ 59
def prefixEnd_1024863 : Nat := 4983230072969 + 3 ^ 40 * 1024863 * 2
def baseEnd_1024863 : Nat := 116943849779761989444277

theorem tailTrace_1024863 : CollatzResearch.WordTrace tailWord_1024863 prefixEnd_1024863 116943849779761989444277 := by
  unfold tailWord_1024863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379824486103858510447243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24919882990735905673631495 37379824486103858510447243)
  ·
    refine ⟨56069736729155787765670865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379824486103858510447243 56069736729155787765670865)
    ·
      refine ⟨42052302546866840824253149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56069736729155787765670865 42052302546866840824253149)
      ·
        refine ⟨15769613455075065309094931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42052302546866840824253149 15769613455075065309094931)
        ·
          refine ⟨23654420182612597963642397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15769613455075065309094931 23654420182612597963642397)
          ·
            refine ⟨8870407568479724236365899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23654420182612597963642397 8870407568479724236365899)
            ·
              refine ⟨13305611352719586354548849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870407568479724236365899 13305611352719586354548849)
              ·
                refine ⟨9979208514539689765911637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305611352719586354548849 9979208514539689765911637)
                ·
                  refine ⟨116943849779761989444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9979208514539689765911637 116943849779761989444277)
                  ·
                    rfl

theorem cell22_1024863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_1024863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024863 prefixEnd_1024863 := by exact prefixLift 1024863
  have htrace : WordTrace (prefixWord ++ tailWord_1024863) baseStart_1024863 baseEnd_1024863 := by
    simpa [prefixWord, tailWord_1024863, baseEnd_1024863] using wordTrace_append hprefix tailTrace_1024863
  have hstable : (prefixWord ++ tailWord_1024863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024863).length < 2 ^ (prefixWord ++ tailWord_1024863).sum := by decide
  have hdescent : baseEnd_1024863 < baseStart_1024863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024895 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_1024895 : Nat := 118140960795 + 1024895 * 2 ^ 59
def prefixEnd_1024895 : Nat := 4983230072969 + 3 ^ 40 * 1024895 * 2
def baseEnd_1024895 : Nat := 350842503593248551532733

theorem tailTrace_1024895 : CollatzResearch.WordTrace tailWord_1024895 prefixEnd_1024895 350842503593248551532733 := by
  unfold tailWord_1024895
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380991621987927975612139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24920661081325285317074759 37380991621987927975612139)
  ·
    refine ⟨56071487432981891963418209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37380991621987927975612139 56071487432981891963418209)
    ·
      refine ⟨42053615574736418972563657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56071487432981891963418209 42053615574736418972563657)
      ·
        refine ⟨31540211681052314229422743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42053615574736418972563657 31540211681052314229422743)
        ·
          refine ⟨47310317521578471344134115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31540211681052314229422743 47310317521578471344134115)
          ·
            refine ⟨70965476282367707016201173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47310317521578471344134115 70965476282367707016201173)
            ·
              refine ⟨1663253350367993133192215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70965476282367707016201173 1663253350367993133192215)
              ·
                refine ⟨2494880025551989699788323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663253350367993133192215 2494880025551989699788323)
                ·
                  refine ⟨3742320038327984549682485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494880025551989699788323 3742320038327984549682485)
                  ·
                    refine ⟨350842503593248551532733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3742320038327984549682485 350842503593248551532733)
                    ·
                      rfl

theorem cell22_1024895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_1024895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024895 prefixEnd_1024895 := by exact prefixLift 1024895
  have htrace : WordTrace (prefixWord ++ tailWord_1024895) baseStart_1024895 baseEnd_1024895 := by
    simpa [prefixWord, tailWord_1024895, baseEnd_1024895] using wordTrace_append hprefix tailTrace_1024895
  have hstable : (prefixWord ++ tailWord_1024895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024895).length < 2 ^ (prefixWord ++ tailWord_1024895).sum := by decide
  have hdescent : baseEnd_1024895 < baseStart_1024895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024927 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1024927 : Nat := 118140960795 + 1024927 * 2 ^ 59
def prefixEnd_1024927 : Nat := 4983230072969 + 3 ^ 40 * 1024927 * 2
def baseEnd_1024927 : Nat := 350853457847211134732635

theorem tailTrace_1024927 : CollatzResearch.WordTrace tailWord_1024927 prefixEnd_1024927 350853457847211134732635 := by
  unfold tailWord_1024927
  simp only [CollatzResearch.WordTrace]
  refine ⟨37382158757871997440777035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24921439171914664960518023 37382158757871997440777035)
  ·
    refine ⟨56073238136807996161165553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37382158757871997440777035 56073238136807996161165553)
    ·
      refine ⟨42054928602605997120874165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56073238136807996161165553 42054928602605997120874165)
      ·
        refine ⟨3942649556494312230081953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42054928602605997120874165 3942649556494312230081953)
        ·
          refine ⟨2956987167370734172561465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942649556494312230081953 2956987167370734172561465)
          ·
            refine ⟨2217740375528050629421099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956987167370734172561465 2217740375528050629421099)
            ·
              refine ⟨3326610563292075944131649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217740375528050629421099 3326610563292075944131649)
              ·
                refine ⟨2494957922469056958098737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3326610563292075944131649 2494957922469056958098737)
                ·
                  refine ⟨1871218441851792718574053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2494957922469056958098737 1871218441851792718574053)
                  ·
                    refine ⟨350853457847211134732635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871218441851792718574053 350853457847211134732635)
                    ·
                      rfl

theorem cell22_1024927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1024927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024927 prefixEnd_1024927 := by exact prefixLift 1024927
  have htrace : WordTrace (prefixWord ++ tailWord_1024927) baseStart_1024927 baseEnd_1024927 := by
    simpa [prefixWord, tailWord_1024927, baseEnd_1024927] using wordTrace_append hprefix tailTrace_1024927
  have hstable : (prefixWord ++ tailWord_1024927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024927).length < 2 ^ (prefixWord ++ tailWord_1024927).sum := by decide
  have hdescent : baseEnd_1024927 < baseStart_1024927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024950 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1024950 : Nat := 118140960795 + 1024950 * 2 ^ 59
def prefixEnd_1024950 : Nat := 4983230072969 + 3 ^ 40 * 1024950 * 2
def baseEnd_1024950 : Nat := 350861331217246741407565

theorem tailTrace_1024950 : CollatzResearch.WordTrace tailWord_1024950 prefixEnd_1024950 350861331217246741407565 := by
  unfold tailWord_1024950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336437352299292023054019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24921998424525781579242869 2336437352299292023054019)
  ·
    refine ⟨3504656028448938034581029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336437352299292023054019 3504656028448938034581029)
    ·
      refine ⟨657123005334175881483943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3504656028448938034581029 657123005334175881483943)
      ·
        refine ⟨985684508001263822225915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657123005334175881483943 985684508001263822225915)
        ·
          refine ⟨1478526762001895733338873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985684508001263822225915 1478526762001895733338873)
          ·
            refine ⟨1108895071501421800004155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478526762001895733338873 1108895071501421800004155)
            ·
              refine ⟨1663342607252132700006233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108895071501421800004155 1663342607252132700006233)
              ·
                refine ⟨1247506955439099525004675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663342607252132700006233 1247506955439099525004675)
                ·
                  refine ⟨1871260433158649287507013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247506955439099525004675 1871260433158649287507013)
                  ·
                    refine ⟨350861331217246741407565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871260433158649287507013 350861331217246741407565)
                    ·
                      rfl

theorem cell22_1024950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1024950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024950 prefixEnd_1024950 := by exact prefixLift 1024950
  have htrace : WordTrace (prefixWord ++ tailWord_1024950) baseStart_1024950 baseEnd_1024950 := by
    simpa [prefixWord, tailWord_1024950, baseEnd_1024950] using wordTrace_append hprefix tailTrace_1024950
  have hstable : (prefixWord ++ tailWord_1024950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024950).length < 2 ^ (prefixWord ++ tailWord_1024950).sum := by decide
  have hdescent : baseEnd_1024950 < baseStart_1024950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024991 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 1, 3]
def baseStart_1024991 : Nat := 118140960795 + 1024991 * 2 ^ 59
def prefixEnd_1024991 : Nat := 4983230072969 + 3 ^ 40 * 1024991 * 2
def baseEnd_1024991 : Nat := 350875366355136301132439

theorem tailTrace_1024991 : CollatzResearch.WordTrace tailWord_1024991 prefixEnd_1024991 350875366355136301132439 := by
  unfold tailWord_1024991
  simp only [CollatzResearch.WordTrace]
  refine ⟨37384493029640136371106827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24922995353093424247404551 37384493029640136371106827)
  ·
    refine ⟨56076739544460204556660241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37384493029640136371106827 56076739544460204556660241)
    ·
      refine ⟨42057554658345153417495181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56076739544460204556660241 42057554658345153417495181)
      ·
        refine ⟨15771582996879432531560693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42057554658345153417495181 15771582996879432531560693)
        ·
          refine ⟨1478585905957446799833815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15771582996879432531560693 1478585905957446799833815)
          ·
            refine ⟨2217878858936170199750723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478585905957446799833815 2217878858936170199750723)
            ·
              refine ⟨3326818288404255299626085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217878858936170199750723 3326818288404255299626085)
              ·
                refine ⟨623778429075797868679891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3326818288404255299626085 623778429075797868679891)
                ·
                  refine ⟨935667643613696803019837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623778429075797868679891 935667643613696803019837)
                  ·
                    refine ⟨350875366355136301132439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935667643613696803019837 350875366355136301132439)
                    ·
                      rfl

theorem cell22_1024991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_1024991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1024991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1024991 prefixEnd_1024991 := by exact prefixLift 1024991
  have htrace : WordTrace (prefixWord ++ tailWord_1024991) baseStart_1024991 baseEnd_1024991 := by
    simpa [prefixWord, tailWord_1024991, baseEnd_1024991] using wordTrace_append hprefix tailTrace_1024991
  have hstable : (prefixWord ++ tailWord_1024991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024991).length < 2 ^ (prefixWord ++ tailWord_1024991).sum := by decide
  have hdescent : baseEnd_1024991 < baseStart_1024991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025002 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1025002 : Nat := 118140960795 + 1025002 * 2 ^ 59
def prefixEnd_1025002 : Nat := 4983230072969 + 3 ^ 40 * 1025002 * 2
def baseEnd_1025002 : Nat := 350879131879935939107405

theorem tailTrace_1025002 : CollatzResearch.WordTrace tailWord_1025002 prefixEnd_1025002 350879131879935939107405 := by
  unfold tailWord_1025002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346223558150071312439315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24923262821733523499838173 9346223558150071312439315)
  ·
    refine ⟨14019335337225106968658973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346223558150071312439315 14019335337225106968658973)
    ·
      refine ⟨5257250751459415113247115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14019335337225106968658973 5257250751459415113247115)
      ·
        refine ⟨7885876127189122669870673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5257250751459415113247115 7885876127189122669870673)
        ·
          refine ⟨5914407095391842002403005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7885876127189122669870673 5914407095391842002403005)
          ·
            refine ⟨2217902660771940750901127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5914407095391842002403005 2217902660771940750901127)
            ·
              refine ⟨3326853991157911126351691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217902660771940750901127 3326853991157911126351691)
              ·
                refine ⟨4990280986736866689527537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326853991157911126351691 4990280986736866689527537)
                ·
                  refine ⟨3742710740052650017145653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990280986736866689527537 3742710740052650017145653)
                  ·
                    refine ⟨350879131879935939107405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3742710740052650017145653 350879131879935939107405)
                    ·
                      rfl

theorem cell22_1025002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1025002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025002 prefixEnd_1025002 := by exact prefixLift 1025002
  have htrace : WordTrace (prefixWord ++ tailWord_1025002) baseStart_1025002 baseEnd_1025002 := by
    simpa [prefixWord, tailWord_1025002, baseEnd_1025002] using wordTrace_append hprefix tailTrace_1025002
  have hstable : (prefixWord ++ tailWord_1025002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025002).length < 2 ^ (prefixWord ++ tailWord_1025002).sum := by decide
  have hdescent : baseEnd_1025002 < baseStart_1025002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025012 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1025012 : Nat := 118140960795 + 1025012 * 2 ^ 59
def prefixEnd_1025012 : Nat := 4983230072969 + 3 ^ 40 * 1025012 * 2
def baseEnd_1025012 : Nat := 350882555084299246357375

theorem tailTrace_1025012 : CollatzResearch.WordTrace tailWord_1025012 prefixEnd_1025012 350882555084299246357375 := by
  unfold tailWord_1025012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18692629481282028478810645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24923505975042704638414193 18692629481282028478810645)
  ·
    refine ⟨876217006935095084944249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18692629481282028478810645 876217006935095084944249)
    ·
      refine ⟨657162755201321313708187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 876217006935095084944249 657162755201321313708187)
      ·
        refine ⟨985744132801981970562281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657162755201321313708187 985744132801981970562281)
        ·
          refine ⟨739308099601486477921711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985744132801981970562281 739308099601486477921711)
          ·
            refine ⟨1108962149402229716882567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739308099601486477921711 1108962149402229716882567)
            ·
              refine ⟨1663443224103344575323851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108962149402229716882567 1663443224103344575323851)
              ·
                refine ⟨2495164836155016862985777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663443224103344575323851 2495164836155016862985777)
                ·
                  refine ⟨1871373627116262647239333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495164836155016862985777 1871373627116262647239333)
                  ·
                    refine ⟨350882555084299246357375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871373627116262647239333 350882555084299246357375)
                    ·
                      rfl

theorem cell22_1025012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1025012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025012 prefixEnd_1025012 := by exact prefixLift 1025012
  have htrace : WordTrace (prefixWord ++ tailWord_1025012) baseStart_1025012 baseEnd_1025012 := by
    simpa [prefixWord, tailWord_1025012, baseEnd_1025012] using wordTrace_append hprefix tailTrace_1025012
  have hstable : (prefixWord ++ tailWord_1025012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025012).length < 2 ^ (prefixWord ++ tailWord_1025012).sum := by decide
  have hdescent : baseEnd_1025012 < baseStart_1025012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025017 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_1025017 : Nat := 118140960795 + 1025017 * 2 ^ 59
def prefixEnd_1025017 : Nat := 4983230072969 + 3 ^ 40 * 1025017 * 2
def baseEnd_1025017 : Nat := 350884266686480899982359

theorem tailTrace_1025017 : CollatzResearch.WordTrace tailWord_1025017 prefixEnd_1025017 350884266686480899982359 := by
  unfold tailWord_1025017
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385441327545942811553305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24923627551697295207702203 37385441327545942811553305)
  ·
    refine ⟨28039080995659457108664979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37385441327545942811553305 28039080995659457108664979)
    ·
      refine ⟨42058621493489185662997469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28039080995659457108664979 42058621493489185662997469)
      ·
        refine ⟨15771983060058444623624051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42058621493489185662997469 15771983060058444623624051)
        ·
          refine ⟨23657974590087666935436077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15771983060058444623624051 23657974590087666935436077)
          ·
            refine ⟨8871740471282875100788529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23657974590087666935436077 8871740471282875100788529)
            ·
              refine ⟨6653805353462156325591397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8871740471282875100788529 6653805353462156325591397)
              ·
                refine ⟨1247588503774154311048387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6653805353462156325591397 1247588503774154311048387)
                ·
                  refine ⟨1871382755661231466572581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247588503774154311048387 1871382755661231466572581)
                  ·
                    refine ⟨350884266686480899982359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871382755661231466572581 350884266686480899982359)
                    ·
                      rfl

theorem cell22_1025017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_1025017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025017 prefixEnd_1025017 := by exact prefixLift 1025017
  have htrace : WordTrace (prefixWord ++ tailWord_1025017) baseStart_1025017 baseEnd_1025017 := by
    simpa [prefixWord, tailWord_1025017, baseEnd_1025017] using wordTrace_append hprefix tailTrace_1025017
  have hstable : (prefixWord ++ tailWord_1025017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025017).length < 2 ^ (prefixWord ++ tailWord_1025017).sum := by decide
  have hdescent : baseEnd_1025017 < baseStart_1025017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025034 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1025034 : Nat := 118140960795 + 1025034 * 2 ^ 59
def prefixEnd_1025034 : Nat := 4983230072969 + 3 ^ 40 * 1025034 * 2
def baseEnd_1025034 : Nat := 350890086133898522307307

theorem tailTrace_1025034 : CollatzResearch.WordTrace tailWord_1025034 prefixEnd_1025034 350890086133898522307307 := by
  unfold tailWord_1025034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346515342121088678730539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24924040912322903143281437 9346515342121088678730539)
  ·
    refine ⟨14019773013181633018095809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346515342121088678730539 14019773013181633018095809)
    ·
      refine ⟨10514829759886224763571857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14019773013181633018095809 10514829759886224763571857)
      ·
        refine ⟨7886122319914668572678893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10514829759886224763571857 7886122319914668572678893)
        ·
          refine ⟨2957295869968000714754585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7886122319914668572678893 2957295869968000714754585)
          ·
            refine ⟨2217971902476000536065939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957295869968000714754585 2217971902476000536065939)
            ·
              refine ⟨3326957853714000804098909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217971902476000536065939 3326957853714000804098909)
              ·
                refine ⟨1247609195142750301537091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326957853714000804098909 1247609195142750301537091)
                ·
                  refine ⟨1871413792714125452305637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247609195142750301537091 1871413792714125452305637)
                  ·
                    refine ⟨350890086133898522307307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871413792714125452305637 350890086133898522307307)
                    ·
                      rfl

theorem cell22_1025034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1025034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025034 prefixEnd_1025034 := by exact prefixLift 1025034
  have htrace : WordTrace (prefixWord ++ tailWord_1025034) baseStart_1025034 baseEnd_1025034 := by
    simpa [prefixWord, tailWord_1025034, baseEnd_1025034] using wordTrace_append hprefix tailTrace_1025034
  have hstable : (prefixWord ++ tailWord_1025034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025034).length < 2 ^ (prefixWord ++ tailWord_1025034).sum := by decide
  have hdescent : baseEnd_1025034 < baseStart_1025034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025075 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_1025075 : Nat := 118140960795 + 1025075 * 2 ^ 59
def prefixEnd_1025075 : Nat := 4983230072969 + 3 ^ 40 * 1025075 * 2
def baseEnd_1025075 : Nat := 350904121271788082032181

theorem tailTrace_1025075 : CollatzResearch.WordTrace tailWord_1025075 prefixEnd_1025075 350904121271788082032181 := by
  unfold tailWord_1025075
  simp only [CollatzResearch.WordTrace]
  refine ⟨37387556761335818717164679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24925037840890545811443119 37387556761335818717164679)
  ·
    refine ⟨56081335142003728075747019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37387556761335818717164679 56081335142003728075747019)
    ·
      refine ⟨84122002713005592113620529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56081335142003728075747019 84122002713005592113620529)
      ·
        refine ⟨63091502034754194085215397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84122002713005592113620529 63091502034754194085215397)
        ·
          refine ⟨11829656631516411390977887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63091502034754194085215397 11829656631516411390977887)
          ·
            refine ⟨17744484947274617086466831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11829656631516411390977887 17744484947274617086466831)
            ·
              refine ⟨26616727420911925629700247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744484947274617086466831 26616727420911925629700247)
              ·
                refine ⟨39925091131367888444550371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616727420911925629700247 39925091131367888444550371)
                ·
                  refine ⟨59887636697051832666825557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39925091131367888444550371 59887636697051832666825557)
                  ·
                    refine ⟨350904121271788082032181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59887636697051832666825557 350904121271788082032181)
                    ·
                      rfl

theorem cell22_1025075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_1025075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025075 prefixEnd_1025075 := by exact prefixLift 1025075
  have htrace : WordTrace (prefixWord ++ tailWord_1025075) baseStart_1025075 baseEnd_1025075 := by
    simpa [prefixWord, tailWord_1025075, baseEnd_1025075] using wordTrace_append hprefix tailTrace_1025075
  have hstable : (prefixWord ++ tailWord_1025075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025075).length < 2 ^ (prefixWord ++ tailWord_1025075).sum := by decide
  have hdescent : baseEnd_1025075 < baseStart_1025075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025094 : List Nat := [6, 1, 1, 1, 1, 2, 10]
def baseStart_1025094 : Nat := 118140960795 + 1025094 * 2 ^ 59
def prefixEnd_1025094 : Nat := 4983230072969 + 3 ^ 40 * 1025094 * 2
def baseEnd_1025094 : Nat := 12996689828151050585449

theorem tailTrace_1025094 : CollatzResearch.WordTrace tailWord_1025094 prefixEnd_1025094 12996689828151050585449 := by
  unfold tailWord_1025094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168382804633343280065823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24925499832177989974737557 1168382804633343280065823)
  ·
    refine ⟨1752574206950014920098735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168382804633343280065823 1752574206950014920098735)
    ·
      refine ⟨2628861310425022380148103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752574206950014920098735 2628861310425022380148103)
      ·
        refine ⟨3943291965637533570222155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628861310425022380148103 3943291965637533570222155)
        ·
          refine ⟨5914937948456300355333233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943291965637533570222155 5914937948456300355333233)
          ·
            refine ⟨4436203461342225266499925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914937948456300355333233 4436203461342225266499925)
            ·
              refine ⟨12996689828151050585449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4436203461342225266499925 12996689828151050585449)
              ·
                rfl

theorem cell22_1025094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 10].length) (baseStart_1025094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025094 prefixEnd_1025094 := by exact prefixLift 1025094
  have htrace : WordTrace (prefixWord ++ tailWord_1025094) baseStart_1025094 baseEnd_1025094 := by
    simpa [prefixWord, tailWord_1025094, baseEnd_1025094] using wordTrace_append hprefix tailTrace_1025094
  have hstable : (prefixWord ++ tailWord_1025094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025094).length < 2 ^ (prefixWord ++ tailWord_1025094).sum := by decide
  have hdescent : baseEnd_1025094 < baseStart_1025094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025201 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 4]
def baseStart_1025201 : Nat := 118140960795 + 1025201 * 2 ^ 59
def prefixEnd_1025201 : Nat := 4983230072969 + 3 ^ 40 * 1025201 * 2
def baseEnd_1025201 : Nat := 116982417882255251127265

theorem tailTrace_1025201 : CollatzResearch.WordTrace tailWord_1025201 prefixEnd_1025201 116982417882255251127265 := by
  unfold tailWord_1025201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392152358879342236251457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24928101572586228157500971 37392152358879342236251457)
  ·
    refine ⟨28044114269159506677188593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37392152358879342236251457 28044114269159506677188593)
    ·
      refine ⟨21033085701869630007891445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28044114269159506677188593 21033085701869630007891445)
      ·
        refine ⟨1971851784550277813239823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21033085701869630007891445 1971851784550277813239823)
        ·
          refine ⟨2957777676825416719859735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971851784550277813239823 2957777676825416719859735)
          ·
            refine ⟨4436666515238125079789603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957777676825416719859735 4436666515238125079789603)
            ·
              refine ⟨6654999772857187619684405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436666515238125079789603 6654999772857187619684405)
              ·
                refine ⟨623906228705361339345413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6654999772857187619684405 623906228705361339345413)
                ·
                  refine ⟨116982417882255251127265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623906228705361339345413 116982417882255251127265)
                  ·
                    rfl

theorem cell22_1025201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_1025201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025201 prefixEnd_1025201 := by exact prefixLift 1025201
  have htrace : WordTrace (prefixWord ++ tailWord_1025201) baseStart_1025201 baseEnd_1025201 := by
    simpa [prefixWord, tailWord_1025201, baseEnd_1025201] using wordTrace_append hprefix tailTrace_1025201
  have hstable : (prefixWord ++ tailWord_1025201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025201).length < 2 ^ (prefixWord ++ tailWord_1025201).sum := by decide
  have hdescent : baseEnd_1025201 < baseStart_1025201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025216 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_1025216 : Nat := 118140960795 + 1025216 * 2 ^ 59
def prefixEnd_1025216 : Nat := 4983230072969 + 3 ^ 40 * 1025216 * 2
def baseEnd_1025216 : Nat := 350952388453310714256749

theorem tailTrace_1025216 : CollatzResearch.WordTrace tailWord_1025216 prefixEnd_1025216 350952388453310714256749 := by
  unfold tailWord_1025216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696349726912499899023751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24928466302549999865365001 18696349726912499899023751)
  ·
    refine ⟨28044524590368749848535627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18696349726912499899023751 28044524590368749848535627)
    ·
      refine ⟨42066786885553124772803441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044524590368749848535627 42066786885553124772803441)
      ·
        refine ⟨31550090164164843579602581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42066786885553124772803441 31550090164164843579602581)
        ·
          refine ⟨1478910476445227042793871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31550090164164843579602581 1478910476445227042793871)
          ·
            refine ⟨2218365714667840564190807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478910476445227042793871 2218365714667840564190807)
            ·
              refine ⟨3327548572001760846286211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218365714667840564190807 3327548572001760846286211)
              ·
                refine ⟨4991322858002641269429317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327548572001760846286211 4991322858002641269429317)
                ·
                  refine ⟨935873035875495238017997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4991322858002641269429317 935873035875495238017997)
                  ·
                    refine ⟨350952388453310714256749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935873035875495238017997 350952388453310714256749)
                    ·
                      rfl

theorem cell22_1025216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_1025216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025216 prefixEnd_1025216 := by exact prefixLift 1025216
  have htrace : WordTrace (prefixWord ++ tailWord_1025216) baseStart_1025216 baseEnd_1025216 := by
    simpa [prefixWord, tailWord_1025216, baseEnd_1025216] using wordTrace_append hprefix tailTrace_1025216
  have hstable : (prefixWord ++ tailWord_1025216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025216).length < 2 ^ (prefixWord ++ tailWord_1025216).sum := by decide
  have hdescent : baseEnd_1025216 < baseStart_1025216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025274 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_1025274 : Nat := 118140960795 + 1025274 * 2 ^ 59
def prefixEnd_1025274 : Nat := 4983230072969 + 3 ^ 40 * 1025274 * 2
def baseEnd_1025274 : Nat := 116990747679539298768857

theorem tailTrace_1025274 : CollatzResearch.WordTrace tailWord_1025274 prefixEnd_1025274 116990747679539298768857 := by
  unfold tailWord_1025274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348703721903718925914719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24929876591743250469105917 9348703721903718925914719)
  ·
    refine ⟨14023055582855578388872079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9348703721903718925914719 14023055582855578388872079)
    ·
      refine ⟨21034583374283367583308119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023055582855578388872079 21034583374283367583308119)
      ·
        refine ⟨31551875061425051374962179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21034583374283367583308119 31551875061425051374962179)
        ·
          refine ⟨47327812592137577062443269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31551875061425051374962179 47327812592137577062443269)
          ·
            refine ⟨8873964861025795699208113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47327812592137577062443269 8873964861025795699208113)
            ·
              refine ⟨6655473645769346774406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873964861025795699208113 6655473645769346774406085)
              ·
                refine ⟨1247901308581752520201141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6655473645769346774406085 1247901308581752520201141)
                ·
                  refine ⟨116990747679539298768857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247901308581752520201141 116990747679539298768857)
                  ·
                    rfl

theorem cell22_1025274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_1025274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025274 prefixEnd_1025274 := by exact prefixLift 1025274
  have htrace : WordTrace (prefixWord ++ tailWord_1025274) baseStart_1025274 baseEnd_1025274 := by
    simpa [prefixWord, tailWord_1025274, baseEnd_1025274] using wordTrace_append hprefix tailTrace_1025274
  have hstable : (prefixWord ++ tailWord_1025274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025274).length < 2 ^ (prefixWord ++ tailWord_1025274).sum := by decide
  have hdescent : baseEnd_1025274 < baseStart_1025274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025278 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1025278 : Nat := 118140960795 + 1025278 * 2 ^ 59
def prefixEnd_1025278 : Nat := 4983230072969 + 3 ^ 40 * 1025278 * 2
def baseEnd_1025278 : Nat := 350973612320363219206559

theorem tailTrace_1025278 : CollatzResearch.WordTrace tailWord_1025278 prefixEnd_1025278 350973612320363219206559 := by
  unfold tailWord_1025278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674370097450048048350561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24929973853066922924536325 4674370097450048048350561)
  ·
    refine ⟨3505777573087536036262921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4674370097450048048350561 3505777573087536036262921)
    ·
      refine ⟨2629333179815652027197191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505777573087536036262921 2629333179815652027197191)
      ·
        refine ⟨3943999769723478040795787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629333179815652027197191 3943999769723478040795787)
        ·
          refine ⟨5915999654585217061193681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943999769723478040795787 5915999654585217061193681)
          ·
            refine ⟨4436999740938912795895261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5915999654585217061193681 4436999740938912795895261)
            ·
              refine ⟨1663874902852092298460723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436999740938912795895261 1663874902852092298460723)
              ·
                refine ⟨2495812354278138447691085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663874902852092298460723 2495812354278138447691085)
                ·
                  refine ⟨935929632854301917884157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2495812354278138447691085 935929632854301917884157)
                  ·
                    refine ⟨350973612320363219206559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935929632854301917884157 350973612320363219206559)
                    ·
                      rfl

theorem cell22_1025278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1025278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025278 prefixEnd_1025278 := by exact prefixLift 1025278
  have htrace : WordTrace (prefixWord ++ tailWord_1025278) baseStart_1025278 baseEnd_1025278 := by
    simpa [prefixWord, tailWord_1025278, baseEnd_1025278] using wordTrace_append hprefix tailTrace_1025278
  have hstable : (prefixWord ++ tailWord_1025278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025278).length < 2 ^ (prefixWord ++ tailWord_1025278).sum := by decide
  have hdescent : baseEnd_1025278 < baseStart_1025278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025291 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 5]
def baseStart_1025291 : Nat := 118140960795 + 1025291 * 2 ^ 59
def prefixEnd_1025291 : Nat := 4983230072969 + 3 ^ 40 * 1025291 * 2
def baseEnd_1025291 : Nat := 116992687495345172877173

theorem tailTrace_1025291 : CollatzResearch.WordTrace tailWord_1025291 prefixEnd_1025291 116992687495345172877173 := by
  unfold tailWord_1025291
  simp only [CollatzResearch.WordTrace]
  refine ⟨37395434928553287607027727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24930289952368858404685151 37395434928553287607027727)
  ·
    refine ⟨56093152392829931410541591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37395434928553287607027727 56093152392829931410541591)
    ·
      refine ⟨84139728589244897115812387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56093152392829931410541591 84139728589244897115812387)
      ·
        refine ⟨126209592883867345673718581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84139728589244897115812387 126209592883867345673718581)
        ·
          refine ⟨11832149332862563656911117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126209592883867345673718581 11832149332862563656911117)
          ·
            refine ⟨4437055999823461371341669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11832149332862563656911117 4437055999823461371341669)
            ·
              refine ⟨831947999966899007126563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4437055999823461371341669 831947999966899007126563)
              ·
                refine ⟨1247921999950348510689845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831947999966899007126563 1247921999950348510689845)
                ·
                  refine ⟨116992687495345172877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247921999950348510689845 116992687495345172877173)
                  ·
                    rfl

theorem cell22_1025291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 5].length) (baseStart_1025291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025291 prefixEnd_1025291 := by exact prefixLift 1025291
  have htrace : WordTrace (prefixWord ++ tailWord_1025291) baseStart_1025291 baseEnd_1025291 := by
    simpa [prefixWord, tailWord_1025291, baseEnd_1025291] using wordTrace_append hprefix tailTrace_1025291
  have hstable : (prefixWord ++ tailWord_1025291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025291).length < 2 ^ (prefixWord ++ tailWord_1025291).sum := by decide
  have hdescent : baseEnd_1025291 < baseStart_1025291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025349 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1025349 : Nat := 118140960795 + 1025349 * 2 ^ 59
def prefixEnd_1025349 : Nat := 4983230072969 + 3 ^ 40 * 1025349 * 2
def baseEnd_1025349 : Nat := 350997917071342700681341

theorem tailTrace_1025349 : CollatzResearch.WordTrace tailWord_1025349 prefixEnd_1025349 350997917071342700681341 := by
  unfold tailWord_1025349
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397550362343163512639101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931700241562109008426067 37397550362343163512639101)
  ·
    refine ⟨14024081385878686317239663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37397550362343163512639101 14024081385878686317239663)
    ·
      refine ⟨21036122078818029475859495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024081385878686317239663 21036122078818029475859495)
      ·
        refine ⟨31554183118227044213789243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036122078818029475859495 31554183118227044213789243)
        ·
          refine ⟨47331274677340566320683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554183118227044213789243 47331274677340566320683865)
          ·
            refine ⟨35498456008005424740512899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47331274677340566320683865 35498456008005424740512899)
            ·
              refine ⟨53247684012008137110769349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35498456008005424740512899 53247684012008137110769349)
              ·
                refine ⟨9983940752251525708269253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53247684012008137110769349 9983940752251525708269253)
                ·
                  refine ⟨1871988891047161070300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9983940752251525708269253 1871988891047161070300485)
                  ·
                    refine ⟨350997917071342700681341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1871988891047161070300485 350997917071342700681341)
                    ·
                      rfl

theorem cell22_1025349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1025349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025349 prefixEnd_1025349 := by exact prefixLift 1025349
  have htrace : WordTrace (prefixWord ++ tailWord_1025349) baseStart_1025349 baseEnd_1025349 := by
    simpa [prefixWord, tailWord_1025349, baseEnd_1025349] using wordTrace_append hprefix tailTrace_1025349
  have hstable : (prefixWord ++ tailWord_1025349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025349).length < 2 ^ (prefixWord ++ tailWord_1025349).sum := by decide
  have hdescent : baseEnd_1025349 < baseStart_1025349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025351 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1025351 : Nat := 118140960795 + 1025351 * 2 ^ 59
def prefixEnd_1025351 : Nat := 4983230072969 + 3 ^ 40 * 1025351 * 2
def baseEnd_1025351 : Nat := 350998601712215362131335

theorem tailTrace_1025351 : CollatzResearch.WordTrace tailWord_1025351 prefixEnd_1025351 350998601712215362131335 := by
  unfold tailWord_1025351
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397623308335917854211907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931748872223945236141271 37397623308335917854211907)
  ·
    refine ⟨56096434962503876781317861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37397623308335917854211907 56096434962503876781317861)
    ·
      refine ⟨10518081555469476896497099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56096434962503876781317861 10518081555469476896497099)
      ·
        refine ⟨15777122333204215344745649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518081555469476896497099 15777122333204215344745649)
        ·
          refine ⟨11832841749903161508559237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15777122333204215344745649 11832841749903161508559237)
          ·
            refine ⟨2218657828106842782854857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11832841749903161508559237 2218657828106842782854857)
            ·
              refine ⟨1663993371080132087141143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218657828106842782854857 1663993371080132087141143)
              ·
                refine ⟨2495990056620198130711715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663993371080132087141143 2495990056620198130711715)
                ·
                  refine ⟨3743985084930297196067573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495990056620198130711715 3743985084930297196067573)
                  ·
                    refine ⟨350998601712215362131335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3743985084930297196067573 350998601712215362131335)
                    ·
                      rfl

theorem cell22_1025351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1025351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025351 prefixEnd_1025351 := by exact prefixLift 1025351
  have htrace : WordTrace (prefixWord ++ tailWord_1025351) baseStart_1025351 baseEnd_1025351 := by
    simpa [prefixWord, tailWord_1025351, baseEnd_1025351] using wordTrace_append hprefix tailTrace_1025351
  have hstable : (prefixWord ++ tailWord_1025351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025351).length < 2 ^ (prefixWord ++ tailWord_1025351).sum := by decide
  have hdescent : baseEnd_1025351 < baseStart_1025351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025447 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1025447 : Nat := 118140960795 + 1025447 * 2 ^ 59
def prefixEnd_1025447 : Nat := 4983230072969 + 3 ^ 40 * 1025447 * 2
def baseEnd_1025447 : Nat := 351031464474103111731041

theorem tailTrace_1025447 : CollatzResearch.WordTrace tailWord_1025447 prefixEnd_1025447 351031464474103111731041 := by
  unfold tailWord_1025447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37401124715988126249706595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24934083143992084166471063 37401124715988126249706595)
  ·
    refine ⟨56101687073982189374559893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37401124715988126249706595 56101687073982189374559893)
    ·
      refine ⟨2629766581592915126932495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56101687073982189374559893 2629766581592915126932495)
      ·
        refine ⟨3944649872389372690398743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629766581592915126932495 3944649872389372690398743)
        ·
          refine ⟨5916974808584059035598115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944649872389372690398743 5916974808584059035598115)
          ·
            refine ⟨8875462212876088553397173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916974808584059035598115 8875462212876088553397173)
            ·
              refine ⟨832074582457133301880985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8875462212876088553397173 832074582457133301880985)
              ·
                refine ⟨624055936842849976410739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832074582457133301880985 624055936842849976410739)
                ·
                  refine ⟨936083905264274964616109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624055936842849976410739 936083905264274964616109)
                  ·
                    refine ⟨351031464474103111731041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936083905264274964616109 351031464474103111731041)
                    ·
                      rfl

theorem cell22_1025447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1025447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025447 prefixEnd_1025447 := by exact prefixLift 1025447
  have htrace : WordTrace (prefixWord ++ tailWord_1025447) baseStart_1025447 baseEnd_1025447 := by
    simpa [prefixWord, tailWord_1025447, baseEnd_1025447] using wordTrace_append hprefix tailTrace_1025447
  have hstable : (prefixWord ++ tailWord_1025447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025447).length < 2 ^ (prefixWord ++ tailWord_1025447).sum := by decide
  have hdescent : baseEnd_1025447 < baseStart_1025447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025486 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1025486 : Nat := 118140960795 + 1025486 * 2 ^ 59
def prefixEnd_1025486 : Nat := 4983230072969 + 3 ^ 40 * 1025486 * 2
def baseEnd_1025486 : Nat := 351044814971120010005921

theorem tailTrace_1025486 : CollatzResearch.WordTrace tailWord_1025486 prefixEnd_1025486 351044814971120010005921 := by
  unfold tailWord_1025486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675318395355854488797039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24935031441897890606917541 4675318395355854488797039)
  ·
    refine ⟨7012977593033781733195559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4675318395355854488797039 7012977593033781733195559)
    ·
      refine ⟨10519466389550672599793339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012977593033781733195559 10519466389550672599793339)
      ·
        refine ⟨15779199584326008899690009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519466389550672599793339 15779199584326008899690009)
        ·
          refine ⟨11834399688244506674767507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779199584326008899690009 11834399688244506674767507)
          ·
            refine ⟨17751599532366760012151261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834399688244506674767507 17751599532366760012151261)
            ·
              refine ⟨6656849824637535004556723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17751599532366760012151261 6656849824637535004556723)
              ·
                refine ⟨9985274736956302506835085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656849824637535004556723 9985274736956302506835085)
                ·
                  refine ⟨3744478026358613440063157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9985274736956302506835085 3744478026358613440063157)
                  ·
                    refine ⟨351044814971120010005921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3744478026358613440063157 351044814971120010005921)
                    ·
                      rfl

theorem cell22_1025486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1025486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025486 prefixEnd_1025486 := by exact prefixLift 1025486
  have htrace : WordTrace (prefixWord ++ tailWord_1025486) baseStart_1025486 baseEnd_1025486 := by
    simpa [prefixWord, tailWord_1025486, baseEnd_1025486] using wordTrace_append hprefix tailTrace_1025486
  have hstable : (prefixWord ++ tailWord_1025486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025486).length < 2 ^ (prefixWord ++ tailWord_1025486).sum := by decide
  have hdescent : baseEnd_1025486 < baseStart_1025486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025505 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 4]
def baseStart_1025505 : Nat := 118140960795 + 1025505 * 2 ^ 59
def prefixEnd_1025505 : Nat := 4983230072969 + 3 ^ 40 * 1025505 * 2
def baseEnd_1025505 : Nat := 117017106353136764593621

theorem tailTrace_1025505 : CollatzResearch.WordTrace tailWord_1025505 prefixEnd_1025505 117017106353136764593621 := by
  unfold tailWord_1025505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403240149778002155317969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24935493433185334770211979 37403240149778002155317969)
  ·
    refine ⟨28052430112333501616488477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37403240149778002155317969 28052430112333501616488477)
    ·
      refine ⟨10519661292125063106183179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28052430112333501616488477 10519661292125063106183179)
      ·
        refine ⟨15779491938187594659274769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519661292125063106183179 15779491938187594659274769)
        ·
          refine ⟨11834618953640695994456077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779491938187594659274769 11834618953640695994456077)
          ·
            refine ⟨4437982107615260997921029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11834618953640695994456077 4437982107615260997921029)
            ·
              refine ⟨832121645177861437110193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4437982107615260997921029 832121645177861437110193)
              ·
                refine ⟨624091233883396077832645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832121645177861437110193 624091233883396077832645)
                ·
                  refine ⟨117017106353136764593621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624091233883396077832645 117017106353136764593621)
                  ·
                    rfl

theorem cell22_1025505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_1025505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025505 prefixEnd_1025505 := by exact prefixLift 1025505
  have htrace : WordTrace (prefixWord ++ tailWord_1025505) baseStart_1025505 baseEnd_1025505 := by
    simpa [prefixWord, tailWord_1025505, baseEnd_1025505] using wordTrace_append hprefix tailTrace_1025505
  have hstable : (prefixWord ++ tailWord_1025505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025505).length < 2 ^ (prefixWord ++ tailWord_1025505).sum := by decide
  have hdescent : baseEnd_1025505 < baseStart_1025505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025533 : List Nat := [1, 4, 1, 1, 1, 5, 3, 6]
def baseStart_1025533 : Nat := 118140960795 + 1025533 * 2 ^ 59
def prefixEnd_1025533 : Nat := 4983230072969 + 3 ^ 40 * 1025533 * 2
def baseEnd_1025533 : Nat := 39006767114625283786753

theorem tailTrace_1025533 : CollatzResearch.WordTrace tailWord_1025533 prefixEnd_1025533 39006767114625283786753 := by
  unfold tailWord_1025533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404261393676562937337253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24936174262451041958224835 37404261393676562937337253)
  ·
    refine ⟨7013299011314355550750735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37404261393676562937337253 7013299011314355550750735)
    ·
      refine ⟨10519948516971533326126103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013299011314355550750735 10519948516971533326126103)
      ·
        refine ⟨15779922775457299989189155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519948516971533326126103 15779922775457299989189155)
        ·
          refine ⟨23669884163185949983783733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15779922775457299989189155 23669884163185949983783733)
          ·
            refine ⟨2219051640298682810979725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23669884163185949983783733 2219051640298682810979725)
            ·
              refine ⟨832144365112006054117397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2219051640298682810979725 832144365112006054117397)
              ·
                refine ⟨39006767114625283786753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 832144365112006054117397 39006767114625283786753)
                ·
                  rfl

theorem cell22_1025533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 6].length) (baseStart_1025533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025533 prefixEnd_1025533 := by exact prefixLift 1025533
  have htrace : WordTrace (prefixWord ++ tailWord_1025533) baseStart_1025533 baseEnd_1025533 := by
    simpa [prefixWord, tailWord_1025533, baseEnd_1025533] using wordTrace_append hprefix tailTrace_1025533
  have hstable : (prefixWord ++ tailWord_1025533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025533).length < 2 ^ (prefixWord ++ tailWord_1025533).sum := by decide
  have hdescent : baseEnd_1025533 < baseStart_1025533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025565 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1025565 : Nat := 118140960795 + 1025565 * 2 ^ 59
def prefixEnd_1025565 : Nat := 4983230072969 + 3 ^ 40 * 1025565 * 2
def baseEnd_1025565 : Nat := 351071858285590137280679

theorem tailTrace_1025565 : CollatzResearch.WordTrace tailWord_1025565 prefixEnd_1025565 351071858285590137280679 := by
  unfold tailWord_1025565
  simp only [CollatzResearch.WordTrace]
  refine ⟨37405428529560632402502149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24936952353040421601668099 37405428529560632402502149)
  ·
    refine ⟨7013517849292618575469153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37405428529560632402502149 7013517849292618575469153)
    ·
      refine ⟨5260138386969463931601865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7013517849292618575469153 5260138386969463931601865)
      ·
        refine ⟨3945103790227097948701399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5260138386969463931601865 3945103790227097948701399)
        ·
          refine ⟨5917655685340646923052099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945103790227097948701399 5917655685340646923052099)
          ·
            refine ⟨8876483528010970384578149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917655685340646923052099 8876483528010970384578149)
            ·
              refine ⟨1664340661502056947108403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8876483528010970384578149 1664340661502056947108403)
              ·
                refine ⟨2496510992253085420662605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664340661502056947108403 2496510992253085420662605)
                ·
                  refine ⟨936191622094907032748477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2496510992253085420662605 936191622094907032748477)
                  ·
                    refine ⟨351071858285590137280679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936191622094907032748477 351071858285590137280679)
                    ·
                      rfl

theorem cell22_1025565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1025565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025565 prefixEnd_1025565 := by exact prefixLift 1025565
  have htrace : WordTrace (prefixWord ++ tailWord_1025565) baseStart_1025565 baseEnd_1025565 := by
    simpa [prefixWord, tailWord_1025565, baseEnd_1025565] using wordTrace_append hprefix tailTrace_1025565
  have hstable : (prefixWord ++ tailWord_1025565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025565).length < 2 ^ (prefixWord ++ tailWord_1025565).sum := by decide
  have hdescent : baseEnd_1025565 < baseStart_1025565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025623 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 6]
def baseStart_1025623 : Nat := 118140960795 + 1025623 * 2 ^ 59
def prefixEnd_1025623 : Nat := 4983230072969 + 3 ^ 40 * 1025623 * 2
def baseEnd_1025623 : Nat := 117030570956965773110167

theorem tailTrace_1025623 : CollatzResearch.WordTrace tailWord_1025623 prefixEnd_1025623 117030570956965773110167 := by
  unfold tailWord_1025623
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407543963350508308113523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24938362642233672205409015 37407543963350508308113523)
  ·
    refine ⟨56111315945025762462170285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37407543963350508308113523 56111315945025762462170285)
    ·
      refine ⟨21041743479384660923313857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56111315945025762462170285 21041743479384660923313857)
      ·
        refine ⟨15781307609538495692485393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21041743479384660923313857 15781307609538495692485393)
        ·
          refine ⟨11835980707153871769364045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15781307609538495692485393 11835980707153871769364045)
          ·
            refine ⟨4438492765182701913511517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11835980707153871769364045 4438492765182701913511517)
            ·
              refine ⟨1664434786943513217566819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4438492765182701913511517 1664434786943513217566819)
              ·
                refine ⟨2496652180415269826350229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664434786943513217566819 2496652180415269826350229)
                ·
                  refine ⟨117030570956965773110167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2496652180415269826350229 117030570956965773110167)
                  ·
                    rfl

theorem cell22_1025623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_1025623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025623 prefixEnd_1025623 := by exact prefixLift 1025623
  have htrace : WordTrace (prefixWord ++ tailWord_1025623) baseStart_1025623 baseEnd_1025623 := by
    simpa [prefixWord, tailWord_1025623, baseEnd_1025623] using wordTrace_append hprefix tailTrace_1025623
  have hstable : (prefixWord ++ tailWord_1025623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025623).length < 2 ^ (prefixWord ++ tailWord_1025623).sum := by decide
  have hdescent : baseEnd_1025623 < baseStart_1025623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025642 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1025642 : Nat := 118140960795 + 1025642 * 2 ^ 59
def prefixEnd_1025642 : Nat := 4983230072969 + 3 ^ 40 * 1025642 * 2
def baseEnd_1025642 : Nat := 351098216959187603105443

theorem tailTrace_1025642 : CollatzResearch.WordTrace tailWord_1025642 prefixEnd_1025642 351098216959187603105443 := by
  unfold tailWord_1025642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352059237570418638263795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24938824633521116368703453 9352059237570418638263795)
  ·
    refine ⟨14028088856355627957395693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9352059237570418638263795 14028088856355627957395693)
    ·
      refine ⟨5260533321133360484023385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14028088856355627957395693 5260533321133360484023385)
      ·
        refine ⟨3945399990850020363017539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5260533321133360484023385 3945399990850020363017539)
        ·
          refine ⟨5918099986275030544526309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945399990850020363017539 5918099986275030544526309)
          ·
            refine ⟨1109643747426568227098683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5918099986275030544526309 1109643747426568227098683)
            ·
              refine ⟨1664465621139852340648025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109643747426568227098683 1664465621139852340648025)
              ·
                refine ⟨1248349215854889255486019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664465621139852340648025 1248349215854889255486019)
                ·
                  refine ⟨1872523823782333883229029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248349215854889255486019 1872523823782333883229029)
                  ·
                    refine ⟨351098216959187603105443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872523823782333883229029 351098216959187603105443)
                    ·
                      rfl

theorem cell22_1025642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1025642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025642 prefixEnd_1025642 := by exact prefixLift 1025642
  have htrace : WordTrace (prefixWord ++ tailWord_1025642) baseStart_1025642 baseEnd_1025642 := by
    simpa [prefixWord, tailWord_1025642, baseEnd_1025642] using wordTrace_append hprefix tailTrace_1025642
  have hstable : (prefixWord ++ tailWord_1025642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025642).length < 2 ^ (prefixWord ++ tailWord_1025642).sum := by decide
  have hdescent : baseEnd_1025642 < baseStart_1025642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025668 : List Nat := [2, 3, 2, 1, 4, 10]
def baseStart_1025668 : Nat := 118140960795 + 1025668 * 2 ^ 59
def prefixEnd_1025668 : Nat := 4983230072969 + 3 ^ 40 * 1025668 * 2
def baseEnd_1025668 : Nat := 4334655769018916073523

theorem tailTrace_1025668 : CollatzResearch.WordTrace tailWord_1025668 prefixEnd_1025668 4334655769018916073523 := by
  unfold tailWord_1025668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704592624093740496750829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24939456832124987329001105 18704592624093740496750829)
  ·
    refine ⟨7014222234035152686281561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18704592624093740496750829 7014222234035152686281561)
    ·
      refine ⟨5260666675526364514711171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7014222234035152686281561 5260666675526364514711171)
      ·
        refine ⟨7891000013289546772066757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260666675526364514711171 7891000013289546772066757)
        ·
          refine ⟨1479562502491790019762517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7891000013289546772066757 1479562502491790019762517)
          ·
            refine ⟨4334655769018916073523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1479562502491790019762517 4334655769018916073523)
            ·
              rfl

theorem cell22_1025668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 10].length) (baseStart_1025668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025668 prefixEnd_1025668 := by exact prefixLift 1025668
  have htrace : WordTrace (prefixWord ++ tailWord_1025668) baseStart_1025668 baseEnd_1025668 := by
    simpa [prefixWord, tailWord_1025668, baseEnd_1025668] using wordTrace_append hprefix tailTrace_1025668
  have hstable : (prefixWord ++ tailWord_1025668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025668).length < 2 ^ (prefixWord ++ tailWord_1025668).sum := by decide
  have hdescent : baseEnd_1025668 < baseStart_1025668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025674 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_1025674 : Nat := 118140960795 + 1025674 * 2 ^ 59
def prefixEnd_1025674 : Nat := 4983230072969 + 3 ^ 40 * 1025674 * 2
def baseEnd_1025674 : Nat := 117036390404383395435115

theorem tailTrace_1025674 : CollatzResearch.WordTrace tailWord_1025674 prefixEnd_1025674 117036390404383395435115 := by
  unfold tailWord_1025674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352351021541436004555019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24939602724110496012146717 9352351021541436004555019)
  ·
    refine ⟨14028526532312154006832529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9352351021541436004555019 14028526532312154006832529)
    ·
      refine ⟨10521394899234115505124397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14028526532312154006832529 10521394899234115505124397)
      ·
        refine ⟨3945523087212793314421649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10521394899234115505124397 3945523087212793314421649)
        ·
          refine ⟨2959142315409594985816237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945523087212793314421649 2959142315409594985816237)
          ·
            refine ⟨1109678368278598119681089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2959142315409594985816237 1109678368278598119681089)
            ·
              refine ⟨832258776208948589760817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109678368278598119681089 832258776208948589760817)
              ·
                refine ⟨624194082156711442320613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832258776208948589760817 624194082156711442320613)
                ·
                  refine ⟨117036390404383395435115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624194082156711442320613 117036390404383395435115)
                  ·
                    rfl

theorem cell22_1025674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_1025674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025674 prefixEnd_1025674 := by exact prefixLift 1025674
  have htrace : WordTrace (prefixWord ++ tailWord_1025674) baseStart_1025674 baseEnd_1025674 := by
    simpa [prefixWord, tailWord_1025674, baseEnd_1025674] using wordTrace_append hprefix tailTrace_1025674
  have hstable : (prefixWord ++ tailWord_1025674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025674).length < 2 ^ (prefixWord ++ tailWord_1025674).sum := by decide
  have hdescent : baseEnd_1025674 < baseStart_1025674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025700 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1025700 : Nat := 118140960795 + 1025700 * 2 ^ 59
def prefixEnd_1025700 : Nat := 4983230072969 + 3 ^ 40 * 1025700 * 2
def baseEnd_1025700 : Nat := 351118071544494785155265

theorem tailTrace_1025700 : CollatzResearch.WordTrace tailWord_1025700 prefixEnd_1025700 351118071544494785155265 := by
  unfold tailWord_1025700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18705176192035775229333277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24940234922714366972444369 18705176192035775229333277)
  ·
    refine ⟨7014441072013415710999979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18705176192035775229333277 7014441072013415710999979)
    ·
      refine ⟨10521661608020123566499969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7014441072013415710999979 10521661608020123566499969)
      ·
        refine ⟨7891246206015092674874977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10521661608020123566499969 7891246206015092674874977)
        ·
          refine ⟨5918434654511319506156233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7891246206015092674874977 5918434654511319506156233)
          ·
            refine ⟨4438825990883489629617175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918434654511319506156233 4438825990883489629617175)
            ·
              refine ⟨6658238986325234444425763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438825990883489629617175 6658238986325234444425763)
              ·
                refine ⟨9987358479487851666638645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658238986325234444425763 9987358479487851666638645)
                ·
                  refine ⟨936314857451986093747373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9987358479487851666638645 936314857451986093747373)
                  ·
                    refine ⟨351118071544494785155265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936314857451986093747373 351118071544494785155265)
                    ·
                      rfl

theorem cell22_1025700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1025700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025700 prefixEnd_1025700 := by exact prefixLift 1025700
  have htrace : WordTrace (prefixWord ++ tailWord_1025700) baseStart_1025700 baseEnd_1025700 := by
    simpa [prefixWord, tailWord_1025700, baseEnd_1025700] using wordTrace_append hprefix tailTrace_1025700
  have hstable : (prefixWord ++ tailWord_1025700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025700).length < 2 ^ (prefixWord ++ tailWord_1025700).sum := by decide
  have hdescent : baseEnd_1025700 < baseStart_1025700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025704 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1025704 : Nat := 118140960795 + 1025704 * 2 ^ 59
def prefixEnd_1025704 : Nat := 4983230072969 + 3 ^ 40 * 1025704 * 2
def baseEnd_1025704 : Nat := 351119440826240108055253

theorem tailTrace_1025704 : CollatzResearch.WordTrace tailWord_1025704 prefixEnd_1025704 351119440826240108055253 := by
  unfold tailWord_1025704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18705249138028529570906083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24940332184038039427874777 18705249138028529570906083)
  ·
    refine ⟨28057873707042794356359125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18705249138028529570906083 28057873707042794356359125)
    ·
      refine ⟨657606415008815492727167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28057873707042794356359125 657606415008815492727167)
      ·
        refine ⟨986409622513223239090751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657606415008815492727167 986409622513223239090751)
        ·
          refine ⟨1479614433769834858636127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986409622513223239090751 1479614433769834858636127)
          ·
            refine ⟨2219421650654752287954191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479614433769834858636127 2219421650654752287954191)
            ·
              refine ⟨3329132475982128431931287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219421650654752287954191 3329132475982128431931287)
              ·
                refine ⟨4993698713973192647896931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329132475982128431931287 4993698713973192647896931)
                ·
                  refine ⟨7490548070959788971845397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993698713973192647896931 7490548070959788971845397)
                  ·
                    refine ⟨351119440826240108055253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7490548070959788971845397 351119440826240108055253)
                    ·
                      rfl

theorem cell22_1025704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1025704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025704 prefixEnd_1025704 := by exact prefixLift 1025704
  have htrace : WordTrace (prefixWord ++ tailWord_1025704) baseStart_1025704 baseEnd_1025704 := by
    simpa [prefixWord, tailWord_1025704, baseEnd_1025704] using wordTrace_append hprefix tailTrace_1025704
  have hstable : (prefixWord ++ tailWord_1025704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025704).length < 2 ^ (prefixWord ++ tailWord_1025704).sum := by decide
  have hdescent : baseEnd_1025704 < baseStart_1025704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025728 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_1025728 : Nat := 118140960795 + 1025728 * 2 ^ 59
def prefixEnd_1025728 : Nat := 4983230072969 + 3 ^ 40 * 1025728 * 2
def baseEnd_1025728 : Nat := 351127656516712045455179

theorem tailTrace_1025728 : CollatzResearch.WordTrace tailWord_1025728 prefixEnd_1025728 351127656516712045455179 := by
  unfold tailWord_1025728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18705686813985055620342919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24940915751980074160457225 18705686813985055620342919)
  ·
    refine ⟨28058530220977583430514379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18705686813985055620342919 28058530220977583430514379)
    ·
      refine ⟨42087795331466375145771569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28058530220977583430514379 42087795331466375145771569)
      ·
        refine ⟨31565846498599781359328677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42087795331466375145771569 31565846498599781359328677)
        ·
          refine ⟨5918596218487459004874127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31565846498599781359328677 5918596218487459004874127)
          ·
            refine ⟨8877894327731188507311191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918596218487459004874127 8877894327731188507311191)
            ·
              refine ⟨13316841491596782760966787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877894327731188507311191 13316841491596782760966787)
              ·
                refine ⟨19975262237395174141450181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13316841491596782760966787 19975262237395174141450181)
                ·
                  refine ⟨3745361669511595151521909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19975262237395174141450181 3745361669511595151521909)
                  ·
                    refine ⟨351127656516712045455179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3745361669511595151521909 351127656516712045455179)
                    ·
                      rfl

theorem cell22_1025728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_1025728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025728 prefixEnd_1025728 := by exact prefixLift 1025728
  have htrace : WordTrace (prefixWord ++ tailWord_1025728) baseStart_1025728 baseEnd_1025728 := by
    simpa [prefixWord, tailWord_1025728, baseEnd_1025728] using wordTrace_append hprefix tailTrace_1025728
  have hstable : (prefixWord ++ tailWord_1025728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025728).length < 2 ^ (prefixWord ++ tailWord_1025728).sum := by decide
  have hdescent : baseEnd_1025728 < baseStart_1025728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025743 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1025743 : Nat := 118140960795 + 1025743 * 2 ^ 59
def prefixEnd_1025743 : Nat := 4983230072969 + 3 ^ 40 * 1025743 * 2
def baseEnd_1025743 : Nat := 351132791323257006330133

theorem tailTrace_1025743 : CollatzResearch.WordTrace tailWord_1025743 prefixEnd_1025743 351132791323257006330133 := by
  unfold tailWord_1025743
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411920722915768802481883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24941280481943845868321255 37411920722915768802481883)
  ·
    refine ⟨56117881084373653203722825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37411920722915768802481883 56117881084373653203722825)
    ·
      refine ⟨42088410813280239902792119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56117881084373653203722825 42088410813280239902792119)
      ·
        refine ⟨63132616219920359854188179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42088410813280239902792119 63132616219920359854188179)
        ·
          refine ⟨94698924329880539781282269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63132616219920359854188179 94698924329880539781282269)
          ·
            refine ⟨35512096623705202417980851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94698924329880539781282269 35512096623705202417980851)
            ·
              refine ⟨53268144935557803626971277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35512096623705202417980851 53268144935557803626971277)
              ·
                refine ⟨19975554350834176360114229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53268144935557803626971277 19975554350834176360114229)
                ·
                  refine ⟨1872708220390704033760709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19975554350834176360114229 1872708220390704033760709)
                  ·
                    refine ⟨351132791323257006330133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872708220390704033760709 351132791323257006330133)
                    ·
                      rfl

theorem cell22_1025743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1025743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025743 prefixEnd_1025743 := by exact prefixLift 1025743
  have htrace : WordTrace (prefixWord ++ tailWord_1025743) baseStart_1025743 baseEnd_1025743 := by
    simpa [prefixWord, tailWord_1025743, baseEnd_1025743] using wordTrace_append hprefix tailTrace_1025743
  have hstable : (prefixWord ++ tailWord_1025743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025743).length < 2 ^ (prefixWord ++ tailWord_1025743).sum := by decide
  have hdescent : baseEnd_1025743 < baseStart_1025743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025760 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_1025760 : Nat := 118140960795 + 1025760 * 2 ^ 59
def prefixEnd_1025760 : Nat := 4983230072969 + 3 ^ 40 * 1025760 * 2
def baseEnd_1025760 : Nat := 351138610770674628655081

theorem tailTrace_1025760 : CollatzResearch.WordTrace tailWord_1025760 prefixEnd_1025760 351138610770674628655081 := by
  unfold tailWord_1025760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706270381927090352925367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24941693842569453803900489 18706270381927090352925367)
  ·
    refine ⟨28059405572890635529388051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18706270381927090352925367 28059405572890635529388051)
    ·
      refine ⟨42089108359335953294082077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28059405572890635529388051 42089108359335953294082077)
      ·
        refine ⟨15783415634750982485280779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42089108359335953294082077 15783415634750982485280779)
        ·
          refine ⟨23675123452126473727921169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783415634750982485280779 23675123452126473727921169)
          ·
            refine ⟨17756342589094855295940877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675123452126473727921169 17756342589094855295940877)
            ·
              refine ⟨6658628470910570735977829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17756342589094855295940877 6658628470910570735977829)
              ·
                refine ⟨1248492838295732012995843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6658628470910570735977829 1248492838295732012995843)
                ·
                  refine ⟨1872739257443598019493765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248492838295732012995843 1872739257443598019493765)
                  ·
                    refine ⟨351138610770674628655081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1872739257443598019493765 351138610770674628655081)
                    ·
                      rfl

theorem cell22_1025760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_1025760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025760 prefixEnd_1025760 := by exact prefixLift 1025760
  have htrace : WordTrace (prefixWord ++ tailWord_1025760) baseStart_1025760 baseEnd_1025760 := by
    simpa [prefixWord, tailWord_1025760, baseEnd_1025760] using wordTrace_append hprefix tailTrace_1025760
  have hstable : (prefixWord ++ tailWord_1025760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025760).length < 2 ^ (prefixWord ++ tailWord_1025760).sum := by decide
  have hdescent : baseEnd_1025760 < baseStart_1025760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025803 : List Nat := [1, 1, 1, 1, 5, 1, 3, 9]
def baseStart_1025803 : Nat := 118140960795 + 1025803 * 2 ^ 59
def prefixEnd_1025803 : Nat := 4983230072969 + 3 ^ 40 * 1025803 * 2
def baseEnd_1025803 : Nat := 39017036727715205536661

theorem tailTrace_1025803 : CollatzResearch.WordTrace tailWord_1025803 prefixEnd_1025803 39017036727715205536661 := by
  unfold tailWord_1025803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414109102698399049666063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24942739401798932699777375 37414109102698399049666063)
  ·
    refine ⟨56121163654047598574499095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37414109102698399049666063 56121163654047598574499095)
    ·
      refine ⟨84181745481071397861748643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56121163654047598574499095 84181745481071397861748643)
      ·
        refine ⟨126272618221607096792622965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84181745481071397861748643 126272618221607096792622965)
        ·
          refine ⟨11838057958275665324308403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126272618221607096792622965 11838057958275665324308403)
          ·
            refine ⟨17757086937413497986462605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838057958275665324308403 17757086937413497986462605)
            ·
              refine ⟨6658907601530061744923477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17757086937413497986462605 6658907601530061744923477)
              ·
                refine ⟨39017036727715205536661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6658907601530061744923477 39017036727715205536661)
                ·
                  rfl

theorem cell22_1025803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_1025803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025803 prefixEnd_1025803 := by exact prefixLift 1025803
  have htrace : WordTrace (prefixWord ++ tailWord_1025803) baseStart_1025803 baseEnd_1025803 := by
    simpa [prefixWord, tailWord_1025803, baseEnd_1025803] using wordTrace_append hprefix tailTrace_1025803
  have hstable : (prefixWord ++ tailWord_1025803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025803).length < 2 ^ (prefixWord ++ tailWord_1025803).sum := by decide
  have hdescent : baseEnd_1025803 < baseStart_1025803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1025833 : Nat := 118140960795 + 1025833 * 2 ^ 59
def prefixEnd_1025833 : Nat := 4983230072969 + 3 ^ 40 * 1025833 * 2
def baseEnd_1025833 : Nat := 351163600162526771579857

theorem tailTrace_1025833 : CollatzResearch.WordTrace tailWord_1025833 prefixEnd_1025833 351163600162526771579857 := by
  unfold tailWord_1025833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415203292589714173258153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24943468861726476115505435 37415203292589714173258153)
  ·
    refine ⟨28061402469442285629943615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37415203292589714173258153 28061402469442285629943615)
    ·
      refine ⟨42092103704163428444915423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28061402469442285629943615 42092103704163428444915423)
      ·
        refine ⟨63138155556245142667373135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42092103704163428444915423 63138155556245142667373135)
        ·
          refine ⟨94707233334367714001059703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63138155556245142667373135 94707233334367714001059703)
          ·
            refine ⟨142060850001551571001589555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94707233334367714001059703 142060850001551571001589555)
            ·
              refine ⟨213091275002327356502384333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142060850001551571001589555 213091275002327356502384333)
              ·
                refine ⟨79909228125872758688394125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213091275002327356502384333 79909228125872758688394125)
                ·
                  refine ⟨29965960547202284508147797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79909228125872758688394125 29965960547202284508147797)
                  ·
                    refine ⟨351163600162526771579857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29965960547202284508147797 351163600162526771579857)
                    ·
                      rfl

theorem cell22_1025833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1025833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025833 prefixEnd_1025833 := by exact prefixLift 1025833
  have htrace : WordTrace (prefixWord ++ tailWord_1025833) baseStart_1025833 baseEnd_1025833 := by
    simpa [prefixWord, tailWord_1025833, baseEnd_1025833] using wordTrace_append hprefix tailTrace_1025833
  have hstable : (prefixWord ++ tailWord_1025833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025833).length < 2 ^ (prefixWord ++ tailWord_1025833).sum := by decide
  have hdescent : baseEnd_1025833 < baseStart_1025833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025850 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1025850 : Nat := 118140960795 + 1025850 * 2 ^ 59
def prefixEnd_1025850 : Nat := 4983230072969 + 3 ^ 40 * 1025850 * 2
def baseEnd_1025850 : Nat := 351169419609944393904805

theorem tailTrace_1025850 : CollatzResearch.WordTrace tailWord_1025850 prefixEnd_1025850 351169419609944393904805 := by
  unfold tailWord_1025850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353955833382031519156751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24943882222352084051084669 9353955833382031519156751)
  ·
    refine ⟨14030933750073047278735127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353955833382031519156751 14030933750073047278735127)
    ·
      refine ⟨21046400625109570918102691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14030933750073047278735127 21046400625109570918102691)
      ·
        refine ⟨31569600937664356377154037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046400625109570918102691 31569600937664356377154037)
        ·
          refine ⟨2959650087906033410358191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31569600937664356377154037 2959650087906033410358191)
          ·
            refine ⟨4439475131859050115537287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959650087906033410358191 4439475131859050115537287)
            ·
              refine ⟨6659212697788575173305931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439475131859050115537287 6659212697788575173305931)
              ·
                refine ⟨9988819046682862759958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659212697788575173305931 9988819046682862759958897)
                ·
                  refine ⟨7491614285012147069969173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9988819046682862759958897 7491614285012147069969173)
                  ·
                    refine ⟨351169419609944393904805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7491614285012147069969173 351169419609944393904805)
                    ·
                      rfl

theorem cell22_1025850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1025850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025850 prefixEnd_1025850 := by exact prefixLift 1025850
  have htrace : WordTrace (prefixWord ++ tailWord_1025850) baseStart_1025850 baseEnd_1025850 := by
    simpa [prefixWord, tailWord_1025850, baseEnd_1025850] using wordTrace_append hprefix tailTrace_1025850
  have hstable : (prefixWord ++ tailWord_1025850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025850).length < 2 ^ (prefixWord ++ tailWord_1025850).sum := by decide
  have hdescent : baseEnd_1025850 < baseStart_1025850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025865 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 5]
def baseStart_1025865 : Nat := 118140960795 + 1025865 * 2 ^ 59
def prefixEnd_1025865 : Nat := 4983230072969 + 3 ^ 40 * 1025865 * 2
def baseEnd_1025865 : Nat := 117058184805496451593253

theorem tailTrace_1025865 : CollatzResearch.WordTrace tailWord_1025865 prefixEnd_1025865 117058184805496451593253 := by
  unfold tailWord_1025865
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416370428473783638423049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24944246952315855758948699 37416370428473783638423049)
  ·
    refine ⟨28062277821355337728817287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37416370428473783638423049 28062277821355337728817287)
    ·
      refine ⟨42093416732033006593225931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28062277821355337728817287 42093416732033006593225931)
      ·
        refine ⟨63140125098049509889838897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42093416732033006593225931 63140125098049509889838897)
        ·
          refine ⟨47355093823537132417379173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63140125098049509889838897 47355093823537132417379173)
          ·
            refine ⟨8879080091913212328258595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47355093823537132417379173 8879080091913212328258595)
            ·
              refine ⟨13318620137869818492387893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879080091913212328258595 13318620137869818492387893)
              ·
                refine ⟨1248620637925295483661365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13318620137869818492387893 1248620637925295483661365)
                ·
                  refine ⟨117058184805496451593253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1248620637925295483661365 117058184805496451593253)
                  ·
                    rfl

theorem cell22_1025865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_1025865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025865 prefixEnd_1025865 := by exact prefixLift 1025865
  have htrace : WordTrace (prefixWord ++ tailWord_1025865) baseStart_1025865 baseEnd_1025865 := by
    simpa [prefixWord, tailWord_1025865, baseEnd_1025865] using wordTrace_append hprefix tailTrace_1025865
  have hstable : (prefixWord ++ tailWord_1025865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025865).length < 2 ^ (prefixWord ++ tailWord_1025865).sum := by decide
  have hdescent : baseEnd_1025865 < baseStart_1025865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025869 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1025869 : Nat := 118140960795 + 1025869 * 2 ^ 59
def prefixEnd_1025869 : Nat := 4983230072969 + 3 ^ 40 * 1025869 * 2
def baseEnd_1025869 : Nat := 351175923698234677679747

theorem tailTrace_1025869 : CollatzResearch.WordTrace tailWord_1025869 prefixEnd_1025869 351175923698234677679747 := by
  unfold tailWord_1025869
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416516320459292321568661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24944344213639528214379107 37416516320459292321568661)
  ·
    refine ⟨1753899202521529327573531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37416516320459292321568661 1753899202521529327573531)
    ·
      refine ⟨2630848803782293991360297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753899202521529327573531 2630848803782293991360297)
      ·
        refine ⟨1973136602836720493520223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630848803782293991360297 1973136602836720493520223)
        ·
          refine ⟨2959704904255080740280335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973136602836720493520223 2959704904255080740280335)
          ·
            refine ⟨4439557356382621110420503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959704904255080740280335 4439557356382621110420503)
            ·
              refine ⟨6659336034573931665630755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439557356382621110420503 6659336034573931665630755)
              ·
                refine ⟨9989004051860897498446133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659336034573931665630755 9989004051860897498446133)
                ·
                  refine ⟨936469129861959140479325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9989004051860897498446133 936469129861959140479325)
                  ·
                    refine ⟨351175923698234677679747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936469129861959140479325 351175923698234677679747)
                    ·
                      rfl

theorem cell22_1025869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1025869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025869 prefixEnd_1025869 := by exact prefixLift 1025869
  have htrace : WordTrace (prefixWord ++ tailWord_1025869) baseStart_1025869 baseEnd_1025869 := by
    simpa [prefixWord, tailWord_1025869, baseEnd_1025869] using wordTrace_append hprefix tailTrace_1025869
  have hstable : (prefixWord ++ tailWord_1025869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025869).length < 2 ^ (prefixWord ++ tailWord_1025869).sum := by decide
  have hdescent : baseEnd_1025869 < baseStart_1025869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025959 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1025959 : Nat := 118140960795 + 1025959 * 2 ^ 59
def prefixEnd_1025959 : Nat := 4983230072969 + 3 ^ 40 * 1025959 * 2
def baseEnd_1025959 : Nat := 351206732537504442929471

theorem tailTrace_1025959 : CollatzResearch.WordTrace tailWord_1025959 prefixEnd_1025959 351206732537504442929471 := by
  unfold tailWord_1025959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37419798890133237692344931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24946532593422158461563287 37419798890133237692344931)
  ·
    refine ⟨56129698335199856538517397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37419798890133237692344931 56129698335199856538517397)
    ·
      refine ⟨2631079609462493275243003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56129698335199856538517397 2631079609462493275243003)
      ·
        refine ⟨3946619414193739912864505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631079609462493275243003 3946619414193739912864505)
        ·
          refine ⟨2959964560645304934648379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946619414193739912864505 2959964560645304934648379)
          ·
            refine ⟨4439946840967957401972569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959964560645304934648379 4439946840967957401972569)
            ·
              refine ⟨3329960130725968051479427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4439946840967957401972569 3329960130725968051479427)
              ·
                refine ⟨4994940196088952077219141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329960130725968051479427 4994940196088952077219141)
                ·
                  refine ⟨936551286766678514478589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4994940196088952077219141 936551286766678514478589)
                  ·
                    refine ⟨351206732537504442929471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936551286766678514478589 351206732537504442929471)
                    ·
                      rfl

theorem cell22_1025959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1025959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1025959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1025959 prefixEnd_1025959 := by exact prefixLift 1025959
  have htrace : WordTrace (prefixWord ++ tailWord_1025959) baseStart_1025959 baseEnd_1025959 := by
    simpa [prefixWord, tailWord_1025959, baseEnd_1025959] using wordTrace_append hprefix tailTrace_1025959
  have hstable : (prefixWord ++ tailWord_1025959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025959).length < 2 ^ (prefixWord ++ tailWord_1025959).sum := by decide
  have hdescent : baseEnd_1025959 < baseStart_1025959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026000 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_1026000 : Nat := 118140960795 + 1026000 * 2 ^ 59
def prefixEnd_1026000 : Nat := 4983230072969 + 3 ^ 40 * 1026000 * 2
def baseEnd_1026000 : Nat := 117073589225131334218115

theorem tailTrace_1026000 : CollatzResearch.WordTrace tailWord_1026000 prefixEnd_1026000 117073589225131334218115 := by
  unfold tailWord_1026000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710647141492350847293727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24947529521989801129724969 18710647141492350847293727)
  ·
    refine ⟨28065970712238526270940591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18710647141492350847293727 28065970712238526270940591)
    ·
      refine ⟨42098956068357789406410887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28065970712238526270940591 42098956068357789406410887)
      ·
        refine ⟨63148434102536684109616331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42098956068357789406410887 63148434102536684109616331)
        ·
          refine ⟨94722651153805026164424497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63148434102536684109616331 94722651153805026164424497)
          ·
            refine ⟨71041988365353769623318373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94722651153805026164424497 71041988365353769623318373)
            ·
              refine ⟨13320372818503831804372195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71041988365353769623318373 13320372818503831804372195)
              ·
                refine ⟨19980559227755747706558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320372818503831804372195 19980559227755747706558293)
                ·
                  refine ⟨117073589225131334218115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19980559227755747706558293 117073589225131334218115)
                  ·
                    rfl

theorem cell22_1026000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_1026000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026000 prefixEnd_1026000 := by exact prefixLift 1026000
  have htrace : WordTrace (prefixWord ++ tailWord_1026000) baseStart_1026000 baseEnd_1026000 := by
    simpa [prefixWord, tailWord_1026000, baseEnd_1026000] using wordTrace_append hprefix tailTrace_1026000
  have hstable : (prefixWord ++ tailWord_1026000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026000).length < 2 ^ (prefixWord ++ tailWord_1026000).sum := by decide
  have hdescent : baseEnd_1026000 < baseStart_1026000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026012 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_1026012 : Nat := 118140960795 + 1026012 * 2 ^ 59
def prefixEnd_1026012 : Nat := 4983230072969 + 3 ^ 40 * 1026012 * 2
def baseEnd_1026012 : Nat := 117074958506876657118103

theorem tailTrace_1026012 : CollatzResearch.WordTrace tailWord_1026012 prefixEnd_1026012 117074958506876657118103 := by
  unfold tailWord_1026012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710865979470613872012145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24947821305960818496016193 18710865979470613872012145)
  ·
    refine ⟨14033149484602960404009109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18710865979470613872012145 14033149484602960404009109)
    ·
      refine ⟨657803882090763768937927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14033149484602960404009109 657803882090763768937927)
      ·
        refine ⟨986705823136145653406891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657803882090763768937927 986705823136145653406891)
        ·
          refine ⟨1480058734704218480110337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986705823136145653406891 1480058734704218480110337)
          ·
            refine ⟨1110044051028163860082753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480058734704218480110337 1110044051028163860082753)
            ·
              refine ⟨832533038271122895062065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110044051028163860082753 832533038271122895062065)
              ·
                refine ⟨624399778703342171296549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832533038271122895062065 624399778703342171296549)
                ·
                  refine ⟨117074958506876657118103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624399778703342171296549 117074958506876657118103)
                  ·
                    rfl

theorem cell22_1026012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_1026012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026012 prefixEnd_1026012 := by exact prefixLift 1026012
  have htrace : WordTrace (prefixWord ++ tailWord_1026012) baseStart_1026012 baseEnd_1026012 := by
    simpa [prefixWord, tailWord_1026012, baseEnd_1026012] using wordTrace_append hprefix tailTrace_1026012
  have hstable : (prefixWord ++ tailWord_1026012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026012).length < 2 ^ (prefixWord ++ tailWord_1026012).sum := by decide
  have hdescent : baseEnd_1026012 < baseStart_1026012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026017 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 5]
def baseStart_1026017 : Nat := 118140960795 + 1026017 * 2 ^ 59
def prefixEnd_1026017 : Nat := 4983230072969 + 3 ^ 40 * 1026017 * 2
def baseEnd_1026017 : Nat := 117075529040937208326431

theorem tailTrace_1026017 : CollatzResearch.WordTrace tailWord_1026017 prefixEnd_1026017 117075529040937208326431 := by
  unfold tailWord_1026017
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421914323923113597956305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24947942882615409065304203 37421914323923113597956305)
  ·
    refine ⟨28066435742942335198467229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37421914323923113597956305 28066435742942335198467229)
    ·
      refine ⟨10524913403603375699425211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28066435742942335198467229 10524913403603375699425211)
      ·
        refine ⟨15787370105405063549137817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10524913403603375699425211 15787370105405063549137817)
        ·
          refine ⟨11840527579053797661853363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15787370105405063549137817 11840527579053797661853363)
          ·
            refine ⟨17760791368580696492780045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840527579053797661853363 17760791368580696492780045)
            ·
              refine ⟨6660296763217761184792517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17760791368580696492780045 6660296763217761184792517)
              ·
                refine ⟨1248805643103330222148597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6660296763217761184792517 1248805643103330222148597)
                ·
                  refine ⟨117075529040937208326431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1248805643103330222148597 117075529040937208326431)
                  ·
                    rfl

theorem cell22_1026017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_1026017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026017 prefixEnd_1026017 := by exact prefixLift 1026017
  have htrace : WordTrace (prefixWord ++ tailWord_1026017) baseStart_1026017 baseEnd_1026017 := by
    simpa [prefixWord, tailWord_1026017, baseEnd_1026017] using wordTrace_append hprefix tailTrace_1026017
  have hstable : (prefixWord ++ tailWord_1026017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026017).length < 2 ^ (prefixWord ++ tailWord_1026017).sum := by decide
  have hdescent : baseEnd_1026017 < baseStart_1026017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026062 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1026062 : Nat := 118140960795 + 1026062 * 2 ^ 59
def prefixEnd_1026062 : Nat := 4983230072969 + 3 ^ 40 * 1026062 * 2
def baseEnd_1026062 : Nat := 117080663847482169201385

theorem tailTrace_1026062 : CollatzResearch.WordTrace tailWord_1026062 prefixEnd_1026062 117080663847482169201385 := by
  unfold tailWord_1026062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677944451095010785418055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24949037072506724188896293 4677944451095010785418055)
  ·
    refine ⟨7016916676642516178127083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4677944451095010785418055 7016916676642516178127083)
    ·
      refine ⟨10525375014963774267190625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7016916676642516178127083 10525375014963774267190625)
      ·
        refine ⟨7894031261222830700392969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10525375014963774267190625 7894031261222830700392969)
        ·
          refine ⟨5920523445917123025294727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894031261222830700392969 5920523445917123025294727)
          ·
            refine ⟨8880785168875684537942091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920523445917123025294727 8880785168875684537942091)
            ·
              refine ⟨13321177753313526806913137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880785168875684537942091 13321177753313526806913137)
              ·
                refine ⟨9990883314985145105184853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13321177753313526806913137 9990883314985145105184853)
                ·
                  refine ⟨117080663847482169201385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9990883314985145105184853 117080663847482169201385)
                  ·
                    rfl

theorem cell22_1026062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1026062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026062 prefixEnd_1026062 := by exact prefixLift 1026062
  have htrace : WordTrace (prefixWord ++ tailWord_1026062) baseStart_1026062 baseEnd_1026062 := by
    simpa [prefixWord, tailWord_1026062, baseEnd_1026062] using wordTrace_append hprefix tailTrace_1026062
  have hstable : (prefixWord ++ tailWord_1026062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026062).length < 2 ^ (prefixWord ++ tailWord_1026062).sum := by decide
  have hdescent : baseEnd_1026062 < baseStart_1026062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026079 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 4]
def baseStart_1026079 : Nat := 118140960795 + 1026079 * 2 ^ 59
def prefixEnd_1026079 : Nat := 4983230072969 + 3 ^ 40 * 1026079 * 2
def baseEnd_1026079 : Nat := 117082603663288043309701

theorem tailTrace_1026079 : CollatzResearch.WordTrace tailWord_1026079 prefixEnd_1026079 117082603663288043309701 := by
  unfold tailWord_1026079
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424175649698498186713291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949450433132332124475527 37424175649698498186713291)
  ·
    refine ⟨56136263474547747280069937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424175649698498186713291 56136263474547747280069937)
    ·
      refine ⟨42102197605910810460052453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56136263474547747280069937 42102197605910810460052453)
      ·
        refine ⟨7894162051108276961259835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42102197605910810460052453 7894162051108276961259835)
        ·
          refine ⟨11841243076662415441889753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894162051108276961259835 11841243076662415441889753)
          ·
            refine ⟨8880932307496811581417315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11841243076662415441889753 8880932307496811581417315)
            ·
              refine ⟨13321398461245217372125973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880932307496811581417315 13321398461245217372125973)
              ·
                refine ⟨624440552870869564318405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13321398461245217372125973 624440552870869564318405)
                ·
                  refine ⟨117082603663288043309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624440552870869564318405 117082603663288043309701)
                  ·
                    rfl

theorem cell22_1026079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 4].length) (baseStart_1026079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026079 prefixEnd_1026079 := by exact prefixLift 1026079
  have htrace : WordTrace (prefixWord ++ tailWord_1026079) baseStart_1026079 baseEnd_1026079 := by
    simpa [prefixWord, tailWord_1026079, baseEnd_1026079] using wordTrace_append hprefix tailTrace_1026079
  have hstable : (prefixWord ++ tailWord_1026079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026079).length < 2 ^ (prefixWord ++ tailWord_1026079).sum := by decide
  have hdescent : baseEnd_1026079 < baseStart_1026079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026092 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_1026092 : Nat := 118140960795 + 1026092 * 2 ^ 59
def prefixEnd_1026092 : Nat := 4983230072969 + 3 ^ 40 * 1026092 * 2
def baseEnd_1026092 : Nat := 351252261155536429354063

theorem tailTrace_1026092 : CollatzResearch.WordTrace tailWord_1026092 prefixEnd_1026092 351252261155536429354063 := by
  unfold tailWord_1026092
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712324899325700703468265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24949766532434267604624353 18712324899325700703468265)
  ·
    refine ⟨14034243674494275527601199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18712324899325700703468265 14034243674494275527601199)
    ·
      refine ⟨21051365511741413291401799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14034243674494275527601199 21051365511741413291401799)
      ·
        refine ⟨31577048267612119937102699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21051365511741413291401799 31577048267612119937102699)
        ·
          refine ⟨47365572401418179905654049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31577048267612119937102699 47365572401418179905654049)
          ·
            refine ⟨35524179301063634929240537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47365572401418179905654049 35524179301063634929240537)
            ·
              refine ⟨26643134475797726196930403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35524179301063634929240537 26643134475797726196930403)
              ·
                refine ⟨39964701713696589295395605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26643134475797726196930403 39964701713696589295395605)
                ·
                  refine ⟨1873345392829527623221669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39964701713696589295395605 1873345392829527623221669)
                  ·
                    refine ⟨351252261155536429354063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873345392829527623221669 351252261155536429354063)
                    ·
                      rfl

theorem cell22_1026092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_1026092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026092 prefixEnd_1026092 := by exact prefixLift 1026092
  have htrace : WordTrace (prefixWord ++ tailWord_1026092) baseStart_1026092 baseEnd_1026092 := by
    simpa [prefixWord, tailWord_1026092, baseEnd_1026092] using wordTrace_append hprefix tailTrace_1026092
  have hstable : (prefixWord ++ tailWord_1026092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026092).length < 2 ^ (prefixWord ++ tailWord_1026092).sum := by decide
  have hdescent : baseEnd_1026092 < baseStart_1026092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026109 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1026109 : Nat := 118140960795 + 1026109 * 2 ^ 59
def prefixEnd_1026109 : Nat := 4983230072969 + 3 ^ 40 * 1026109 * 2
def baseEnd_1026109 : Nat := 351258080602954051679011

theorem tailTrace_1026109 : CollatzResearch.WordTrace tailWord_1026109 prefixEnd_1026109 351258080602954051679011 := by
  unfold tailWord_1026109
  simp only [CollatzResearch.WordTrace]
  refine ⟨37425269839589813310305381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24950179893059875540203587 37425269839589813310305381)
  ·
    refine ⟨7017238094923089995682259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37425269839589813310305381 7017238094923089995682259)
    ·
      refine ⟨10525857142384634993523389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017238094923089995682259 10525857142384634993523389)
      ·
        refine ⟨3947196428394238122571271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10525857142384634993523389 3947196428394238122571271)
        ·
          refine ⟨5920794642591357183856907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947196428394238122571271 5920794642591357183856907)
          ·
            refine ⟨8881191963887035775785361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920794642591357183856907 8881191963887035775785361)
            ·
              refine ⟨6660893972915276831839021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8881191963887035775785361 6660893972915276831839021)
              ·
                refine ⟨2497835239843228811939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6660893972915276831839021 2497835239843228811939633)
                ·
                  refine ⟨1873376429882421608954725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497835239843228811939633 1873376429882421608954725)
                  ·
                    refine ⟨351258080602954051679011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873376429882421608954725 351258080602954051679011)
                    ·
                      rfl

theorem cell22_1026109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1026109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026109 prefixEnd_1026109 := by exact prefixLift 1026109
  have htrace : WordTrace (prefixWord ++ tailWord_1026109) baseStart_1026109 baseEnd_1026109 := by
    simpa [prefixWord, tailWord_1026109, baseEnd_1026109] using wordTrace_append hprefix tailTrace_1026109
  have hstable : (prefixWord ++ tailWord_1026109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026109).length < 2 ^ (prefixWord ++ tailWord_1026109).sum := by decide
  have hdescent : baseEnd_1026109 < baseStart_1026109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026113 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 4]
def baseStart_1026113 : Nat := 118140960795 + 1026113 * 2 ^ 59
def prefixEnd_1026113 : Nat := 4983230072969 + 3 ^ 40 * 1026113 * 2
def baseEnd_1026113 : Nat := 117086483294899791526333

theorem tailTrace_1026113 : CollatzResearch.WordTrace tailWord_1026113 prefixEnd_1026113 117086483294899791526333 := by
  unfold tailWord_1026113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37425415731575321993450993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24950277154383547995633995 37425415731575321993450993)
  ·
    refine ⟨28069061798681491495088245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37425415731575321993450993 28069061798681491495088245)
    ·
      refine ⟨2631474543626389827664523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28069061798681491495088245 2631474543626389827664523)
      ·
        refine ⟨3947211815439584741496785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631474543626389827664523 3947211815439584741496785)
        ·
          refine ⟨2960408861579688556122589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947211815439584741496785 2960408861579688556122589)
          ·
            refine ⟨1110153323092383208545971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2960408861579688556122589 1110153323092383208545971)
            ·
              refine ⟨1665229984638574812818957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110153323092383208545971 1665229984638574812818957)
              ·
                refine ⟨624461244239465554807109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665229984638574812818957 624461244239465554807109)
                ·
                  refine ⟨117086483294899791526333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624461244239465554807109 117086483294899791526333)
                  ·
                    rfl

theorem cell22_1026113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_1026113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026113 prefixEnd_1026113 := by exact prefixLift 1026113
  have htrace : WordTrace (prefixWord ++ tailWord_1026113) baseStart_1026113 baseEnd_1026113 := by
    simpa [prefixWord, tailWord_1026113, baseEnd_1026113] using wordTrace_append hprefix tailTrace_1026113
  have hstable : (prefixWord ++ tailWord_1026113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026113).length < 2 ^ (prefixWord ++ tailWord_1026113).sum := by decide
  have hdescent : baseEnd_1026113 < baseStart_1026113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026137 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_1026137 : Nat := 118140960795 + 1026137 * 2 ^ 59
def prefixEnd_1026137 : Nat := 4983230072969 + 3 ^ 40 * 1026137 * 2
def baseEnd_1026137 : Nat := 351267665575171311978925

theorem tailTrace_1026137 : CollatzResearch.WordTrace tailWord_1026137 prefixEnd_1026137 351267665575171311978925 := by
  unfold tailWord_1026137
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426291083488374092324665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24950860722325582728216443 37426291083488374092324665)
  ·
    refine ⟨28069718312616280569243499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37426291083488374092324665 28069718312616280569243499)
    ·
      refine ⟨42104577468924420853865249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28069718312616280569243499 42104577468924420853865249)
      ·
        refine ⟨31578433101693315640398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42104577468924420853865249 31578433101693315640398937)
        ·
          refine ⟨23683824826269986730299203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31578433101693315640398937 23683824826269986730299203)
          ·
            refine ⟨35525737239404980095448805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23683824826269986730299203 35525737239404980095448805)
            ·
              refine ⟨6661075732388433767896651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35525737239404980095448805 6661075732388433767896651)
              ·
                refine ⟨9991613598582650651844977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661075732388433767896651 9991613598582650651844977)
                ·
                  refine ⟨7493710198936987988883733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991613598582650651844977 7493710198936987988883733)
                  ·
                    refine ⟨351267665575171311978925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7493710198936987988883733 351267665575171311978925)
                    ·
                      rfl

theorem cell22_1026137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_1026137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026137 prefixEnd_1026137 := by exact prefixLift 1026137
  have htrace : WordTrace (prefixWord ++ tailWord_1026137) baseStart_1026137 baseEnd_1026137 := by
    simpa [prefixWord, tailWord_1026137, baseEnd_1026137] using wordTrace_append hprefix tailTrace_1026137
  have hstable : (prefixWord ++ tailWord_1026137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026137).length < 2 ^ (prefixWord ++ tailWord_1026137).sum := by decide
  have hdescent : baseEnd_1026137 < baseStart_1026137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026141 : List Nat := [1, 4, 4, 1, 1, 2, 2, 7]
def baseStart_1026141 : Nat := 118140960795 + 1026141 * 2 ^ 59
def prefixEnd_1026141 : Nat := 4983230072969 + 3 ^ 40 * 1026141 * 2
def baseEnd_1026141 : Nat := 39029892761879626097657

theorem tailTrace_1026141 : CollatzResearch.WordTrace tailWord_1026141 prefixEnd_1026141 39029892761879626097657 := by
  unfold tailWord_1026141
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426436975473882775470277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24950957983649255183646851 37426436975473882775470277)
  ·
    refine ⟨7017456932901353020400677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37426436975473882775470277 7017456932901353020400677)
    ·
      refine ⟨1315773174919003691325127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7017456932901353020400677 1315773174919003691325127)
      ·
        refine ⟨1973659762378505536987691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315773174919003691325127 1973659762378505536987691)
        ·
          refine ⟨2960489643567758305481537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973659762378505536987691 2960489643567758305481537)
          ·
            refine ⟨2220367232675818729111153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960489643567758305481537 2220367232675818729111153)
            ·
              refine ⟨1665275424506864046833365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220367232675818729111153 1665275424506864046833365)
              ·
                refine ⟨39029892761879626097657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1665275424506864046833365 39029892761879626097657)
                ·
                  rfl

theorem cell22_1026141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 7].length) (baseStart_1026141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026141 prefixEnd_1026141 := by exact prefixLift 1026141
  have htrace : WordTrace (prefixWord ++ tailWord_1026141) baseStart_1026141 baseEnd_1026141 := by
    simpa [prefixWord, tailWord_1026141, baseEnd_1026141] using wordTrace_append hprefix tailTrace_1026141
  have hstable : (prefixWord ++ tailWord_1026141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026141).length < 2 ^ (prefixWord ++ tailWord_1026141).sum := by decide
  have hdescent : baseEnd_1026141 < baseStart_1026141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026186 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_1026186 : Nat := 118140960795 + 1026186 * 2 ^ 59
def prefixEnd_1026186 : Nat := 4983230072969 + 3 ^ 40 * 1026186 * 2
def baseEnd_1026186 : Nat := 117094813092183839167925

theorem tailTrace_1026186 : CollatzResearch.WordTrace tailWord_1026186 prefixEnd_1026186 117094813092183839167925 := by
  unfold tailWord_1026186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357019565077713865214603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24952052173540570307238941 9357019565077713865214603)
  ·
    refine ⟨14035529347616570797821905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357019565077713865214603 14035529347616570797821905)
    ·
      refine ⟨10526647010712428098366429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14035529347616570797821905 10526647010712428098366429)
      ·
        refine ⟨3947492629017160536887411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10526647010712428098366429 3947492629017160536887411)
        ·
          refine ⟨5921238943525740805331117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947492629017160536887411 5921238943525740805331117)
          ·
            refine ⟨2220464603822152801999169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5921238943525740805331117 2220464603822152801999169)
            ·
              refine ⟨1665348452866614601499377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220464603822152801999169 1665348452866614601499377)
              ·
                refine ⟨1249011339649960951124533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665348452866614601499377 1249011339649960951124533)
                ·
                  refine ⟨117094813092183839167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249011339649960951124533 117094813092183839167925)
                  ·
                    rfl

theorem cell22_1026186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_1026186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026186 prefixEnd_1026186 := by exact prefixLift 1026186
  have htrace : WordTrace (prefixWord ++ tailWord_1026186) baseStart_1026186 baseEnd_1026186 := by
    simpa [prefixWord, tailWord_1026186, baseEnd_1026186] using wordTrace_append hprefix tailTrace_1026186
  have hstable : (prefixWord ++ tailWord_1026186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026186).length < 2 ^ (prefixWord ++ tailWord_1026186).sum := by decide
  have hdescent : baseEnd_1026186 < baseStart_1026186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026190 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1026190 : Nat := 118140960795 + 1026190 * 2 ^ 59
def prefixEnd_1026190 : Nat := 4983230072969 + 3 ^ 40 * 1026190 * 2
def baseEnd_1026190 : Nat := 351285808558296840403763

theorem tailTrace_1026190 : CollatzResearch.WordTrace tailWord_1026190 prefixEnd_1026190 351285808558296840403763 := by
  unfold tailWord_1026190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678528019037045518000503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24952149434864242762669349 4678528019037045518000503)
  ·
    refine ⟨7017792028555568277000755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4678528019037045518000503 7017792028555568277000755)
    ·
      refine ⟨10526688042833352415501133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017792028555568277000755 10526688042833352415501133)
      ·
        refine ⟨3947508016062507155812925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10526688042833352415501133 3947508016062507155812925)
        ·
          refine ⟨1480315506023440183429847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3947508016062507155812925 1480315506023440183429847)
          ·
            refine ⟨2220473259035160275144771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480315506023440183429847 2220473259035160275144771)
            ·
              refine ⟨3330709888552740412717157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220473259035160275144771 3330709888552740412717157)
              ·
                refine ⟨624508104103638827384467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3330709888552740412717157 624508104103638827384467)
                ·
                  refine ⟨936762156155458241076701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624508104103638827384467 936762156155458241076701)
                  ·
                    refine ⟨351285808558296840403763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936762156155458241076701 351285808558296840403763)
                    ·
                      rfl

theorem cell22_1026190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1026190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026190 prefixEnd_1026190 := by exact prefixLift 1026190
  have htrace : WordTrace (prefixWord ++ tailWord_1026190) baseStart_1026190 baseEnd_1026190 := by
    simpa [prefixWord, tailWord_1026190, baseEnd_1026190] using wordTrace_append hprefix tailTrace_1026190
  have hstable : (prefixWord ++ tailWord_1026190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026190).length < 2 ^ (prefixWord ++ tailWord_1026190).sum := by decide
  have hdescent : baseEnd_1026190 < baseStart_1026190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026231 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 4]
def baseStart_1026231 : Nat := 118140960795 + 1026231 * 2 ^ 59
def prefixEnd_1026231 : Nat := 4983230072969 + 3 ^ 40 * 1026231 * 2
def baseEnd_1026231 : Nat := 117099947898728800042879

theorem tailTrace_1026231 : CollatzResearch.WordTrace tailWord_1026231 prefixEnd_1026231 117099947898728800042879 := by
  unfold tailWord_1026231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429719545147828146246547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24953146363431885430831031 37429719545147828146246547)
  ·
    refine ⟨56144579317721742219369821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37429719545147828146246547 56144579317721742219369821)
    ·
      refine ⟨21054217244145653332263683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56144579317721742219369821 21054217244145653332263683)
      ·
        refine ⟨31581325866218479998395525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21054217244145653332263683 31581325866218479998395525)
        ·
          refine ⟨5921498599915964999699161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31581325866218479998395525 5921498599915964999699161)
          ·
            refine ⟨4441123949936973749774371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5921498599915964999699161 4441123949936973749774371)
            ·
              refine ⟨6661685924905460624661557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441123949936973749774371 6661685924905460624661557)
              ·
                refine ⟨624533055459886933562021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6661685924905460624661557 624533055459886933562021)
                ·
                  refine ⟨117099947898728800042879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624533055459886933562021 117099947898728800042879)
                  ·
                    rfl

theorem cell22_1026231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 4].length) (baseStart_1026231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026231 prefixEnd_1026231 := by exact prefixLift 1026231
  have htrace : WordTrace (prefixWord ++ tailWord_1026231) baseStart_1026231 baseEnd_1026231 := by
    simpa [prefixWord, tailWord_1026231, baseEnd_1026231] using wordTrace_append hprefix tailTrace_1026231
  have hstable : (prefixWord ++ tailWord_1026231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026231).length < 2 ^ (prefixWord ++ tailWord_1026231).sum := by decide
  have hdescent : baseEnd_1026231 < baseStart_1026231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026304 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_1026304 : Nat := 118140960795 + 1026304 * 2 ^ 59
def prefixEnd_1026304 : Nat := 4983230072969 + 3 ^ 40 * 1026304 * 2
def baseEnd_1026304 : Nat := 117108277696012847684471

theorem tailTrace_1026304 : CollatzResearch.WordTrace tailWord_1026304 prefixEnd_1026304 117108277696012847684471 := by
  unfold tailWord_1026304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716191036941680806826983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24954921382588907742435977 18716191036941680806826983)
  ·
    refine ⟨28074286555412521210240475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18716191036941680806826983 28074286555412521210240475)
    ·
      refine ⟨42111429833118781815360713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28074286555412521210240475 42111429833118781815360713)
      ·
        refine ⟨31583572374839086361520535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42111429833118781815360713 31583572374839086361520535)
        ·
          refine ⟨47375358562258629542280803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31583572374839086361520535 47375358562258629542280803)
          ·
            refine ⟨71063037843387944313421205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47375358562258629542280803 71063037843387944313421205)
            ·
              refine ⟨3331079898908809889691619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71063037843387944313421205 3331079898908809889691619)
              ·
                refine ⟨4996619848363214834537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331079898908809889691619 4996619848363214834537429)
                ·
                  refine ⟨117108277696012847684471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4996619848363214834537429 117108277696012847684471)
                  ·
                    rfl

theorem cell22_1026304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_1026304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026304 prefixEnd_1026304 := by exact prefixLift 1026304
  have htrace : WordTrace (prefixWord ++ tailWord_1026304) baseStart_1026304 baseEnd_1026304 := by
    simpa [prefixWord, tailWord_1026304, baseEnd_1026304] using wordTrace_append hprefix tailTrace_1026304
  have hstable : (prefixWord ++ tailWord_1026304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026304).length < 2 ^ (prefixWord ++ tailWord_1026304).sum := by decide
  have hdescent : baseEnd_1026304 < baseStart_1026304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026319 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1026319 : Nat := 118140960795 + 1026319 * 2 ^ 59
def prefixEnd_1026319 : Nat := 4983230072969 + 3 ^ 40 * 1026319 * 2
def baseEnd_1026319 : Nat := 351329967894583503928367

theorem tailTrace_1026319 : CollatzResearch.WordTrace tailWord_1026319 prefixEnd_1026319 351329967894583503928367 := by
  unfold tailWord_1026319
  simp only [CollatzResearch.WordTrace]
  refine ⟨37432929168829019175450011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24955286112552679450300007 37432929168829019175450011)
  ·
    refine ⟨56149393753243528763175017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37432929168829019175450011 56149393753243528763175017)
    ·
      refine ⟨42112045314932646572381263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56149393753243528763175017 42112045314932646572381263)
      ·
        refine ⟨63168067972398969858571895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42112045314932646572381263 63168067972398969858571895)
        ·
          refine ⟨94752101958598454787857843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63168067972398969858571895 94752101958598454787857843)
          ·
            refine ⟨142128152937897682181786765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94752101958598454787857843 142128152937897682181786765)
            ·
              refine ⟨53298057351711630818170037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142128152937897682181786765 53298057351711630818170037)
              ·
                refine ⟨4996692876722965389203441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53298057351711630818170037 4996692876722965389203441)
                ·
                  refine ⟨3747519657542224041902581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996692876722965389203441 3747519657542224041902581)
                  ·
                    refine ⟨351329967894583503928367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3747519657542224041902581 351329967894583503928367)
                    ·
                      rfl

theorem cell22_1026319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1026319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026319 prefixEnd_1026319 := by exact prefixLift 1026319
  have htrace : WordTrace (prefixWord ++ tailWord_1026319) baseStart_1026319 baseEnd_1026319 := by
    simpa [prefixWord, tailWord_1026319, baseEnd_1026319] using wordTrace_append hprefix tailTrace_1026319
  have hstable : (prefixWord ++ tailWord_1026319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026319).length < 2 ^ (prefixWord ++ tailWord_1026319).sum := by decide
  have hdescent : baseEnd_1026319 < baseStart_1026319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026321 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 5]
def baseStart_1026321 : Nat := 118140960795 + 1026321 * 2 ^ 59
def prefixEnd_1026321 : Nat := 4983230072969 + 3 ^ 40 * 1026321 * 2
def baseEnd_1026321 : Nat := 117110217511818721792787

theorem tailTrace_1026321 : CollatzResearch.WordTrace tailWord_1026321 prefixEnd_1026321 117110217511818721792787 := by
  unfold tailWord_1026321
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433002114821773517022817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24955334743214515678015211 37433002114821773517022817)
  ·
    refine ⟨28074751586116330137767113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37433002114821773517022817 28074751586116330137767113)
    ·
      refine ⟨21056063689587247603325335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28074751586116330137767113 21056063689587247603325335)
      ·
        refine ⟨31584095534380871404988003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056063689587247603325335 31584095534380871404988003)
        ·
          refine ⟨47376143301571307107482005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31584095534380871404988003 47376143301571307107482005)
          ·
            refine ⟨2220756717261155020663219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47376143301571307107482005 2220756717261155020663219)
            ·
              refine ⟨3331135075891732530994829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220756717261155020663219 3331135075891732530994829)
              ·
                refine ⟨1249175653459399699123061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331135075891732530994829 1249175653459399699123061)
                ·
                  refine ⟨117110217511818721792787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249175653459399699123061 117110217511818721792787)
                  ·
                    rfl

theorem cell22_1026321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_1026321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026321 prefixEnd_1026321 := by exact prefixLift 1026321
  have htrace : WordTrace (prefixWord ++ tailWord_1026321) baseStart_1026321 baseEnd_1026321 := by
    simpa [prefixWord, tailWord_1026321, baseEnd_1026321] using wordTrace_append hprefix tailTrace_1026321
  have hstable : (prefixWord ++ tailWord_1026321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026321).length < 2 ^ (prefixWord ++ tailWord_1026321).sum := by decide
  have hdescent : baseEnd_1026321 < baseStart_1026321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026351 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 1, 4]
def baseStart_1026351 : Nat := 118140960795 + 1026351 * 2 ^ 59
def prefixEnd_1026351 : Nat := 4983230072969 + 3 ^ 40 * 1026351 * 2
def baseEnd_1026351 : Nat := 351340922148546087128269

theorem tailTrace_1026351 : CollatzResearch.WordTrace tailWord_1026351 prefixEnd_1026351 351340922148546087128269 := by
  unfold tailWord_1026351
  simp only [CollatzResearch.WordTrace]
  refine ⟨37434096304713088640614907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24956064203142059093743271 37434096304713088640614907)
  ·
    refine ⟨56151144457069632960922361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37434096304713088640614907 56151144457069632960922361)
    ·
      refine ⟨42113358342802224720691771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56151144457069632960922361 42113358342802224720691771)
      ·
        refine ⟨63170037514203337081037657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42113358342802224720691771 63170037514203337081037657)
        ·
          refine ⟨47377528135652502810778243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63170037514203337081037657 47377528135652502810778243)
          ·
            refine ⟨71066292203478754216167365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47377528135652502810778243 71066292203478754216167365)
            ·
              refine ⟨13324929788152266415531381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71066292203478754216167365 13324929788152266415531381)
              ·
                refine ⟨1249212167639274976456067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13324929788152266415531381 1249212167639274976456067)
                ·
                  refine ⟨1873818251458912464684101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249212167639274976456067 1873818251458912464684101)
                  ·
                    refine ⟨351340922148546087128269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873818251458912464684101 351340922148546087128269)
                    ·
                      rfl

theorem cell22_1026351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_1026351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026351 prefixEnd_1026351 := by exact prefixLift 1026351
  have htrace : WordTrace (prefixWord ++ tailWord_1026351) baseStart_1026351 baseEnd_1026351 := by
    simpa [prefixWord, tailWord_1026351, baseEnd_1026351] using wordTrace_append hprefix tailTrace_1026351
  have hstable : (prefixWord ++ tailWord_1026351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026351).length < 2 ^ (prefixWord ++ tailWord_1026351).sum := by decide
  have hdescent : baseEnd_1026351 < baseStart_1026351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026400 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_1026400 : Nat := 118140960795 + 1026400 * 2 ^ 59
def prefixEnd_1026400 : Nat := 4983230072969 + 3 ^ 40 * 1026400 * 2
def baseEnd_1026400 : Nat := 117119231949975430884373

theorem tailTrace_1026400 : CollatzResearch.WordTrace tailWord_1026400 prefixEnd_1026400 117119231949975430884373 := by
  unfold tailWord_1026400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717941740767785004574327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24957255654357046672765769 18717941740767785004574327)
  ·
    refine ⟨28076912611151677506861491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18717941740767785004574327 28076912611151677506861491)
    ·
      refine ⟨42115368916727516260292237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28076912611151677506861491 42115368916727516260292237)
      ·
        refine ⟨15793263343772818597609589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42115368916727516260292237 15793263343772818597609589)
        ·
          refine ⟨1480618438478701743525899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15793263343772818597609589 1480618438478701743525899)
          ·
            refine ⟨2220927657718052615288849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480618438478701743525899 2220927657718052615288849)
            ·
              refine ⟨1665695743288539461466637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220927657718052615288849 1665695743288539461466637)
              ·
                refine ⟨624635903733202298049989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665695743288539461466637 624635903733202298049989)
                ·
                  refine ⟨117119231949975430884373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624635903733202298049989 117119231949975430884373)
                  ·
                    rfl

theorem cell22_1026400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_1026400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026400 prefixEnd_1026400 := by exact prefixLift 1026400
  have htrace : WordTrace (prefixWord ++ tailWord_1026400) baseStart_1026400 baseEnd_1026400 := by
    simpa [prefixWord, tailWord_1026400, baseEnd_1026400] using wordTrace_append hprefix tailTrace_1026400
  have hstable : (prefixWord ++ tailWord_1026400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026400).length < 2 ^ (prefixWord ++ tailWord_1026400).sum := by decide
  have hdescent : baseEnd_1026400 < baseStart_1026400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026402 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1026402 : Nat := 118140960795 + 1026402 * 2 ^ 59
def prefixEnd_1026402 : Nat := 4983230072969 + 3 ^ 40 * 1026402 * 2
def baseEnd_1026402 : Nat := 351358380490798954103113

theorem tailTrace_1026402 : CollatzResearch.WordTrace tailWord_1026402 prefixEnd_1026402 351358380490798954103113 := by
  unfold tailWord_1026402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358989106882081087680365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24957304285018882900480973 9358989106882081087680365)
  ·
    refine ⟨3509620915080780407880137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9358989106882081087680365 3509620915080780407880137)
    ·
      refine ⟨2632215686310585305910103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3509620915080780407880137 2632215686310585305910103)
      ·
        refine ⟨3948323529465877958865155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632215686310585305910103 3948323529465877958865155)
        ·
          refine ⟨5922485294198816938297733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948323529465877958865155 5922485294198816938297733)
          ·
            refine ⟨1110465992662278175930825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5922485294198816938297733 1110465992662278175930825)
            ·
              refine ⟨832849494496708631948119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110465992662278175930825 832849494496708631948119)
              ·
                refine ⟨1249274241745062947922179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832849494496708631948119 1249274241745062947922179)
                ·
                  refine ⟨1873911362617594421883269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249274241745062947922179 1873911362617594421883269)
                  ·
                    refine ⟨351358380490798954103113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873911362617594421883269 351358380490798954103113)
                    ·
                      rfl

theorem cell22_1026402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1026402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026402 prefixEnd_1026402 := by exact prefixLift 1026402
  have htrace : WordTrace (prefixWord ++ tailWord_1026402) baseStart_1026402 baseEnd_1026402 := by
    simpa [prefixWord, tailWord_1026402, baseEnd_1026402] using wordTrace_append hprefix tailTrace_1026402
  have hstable : (prefixWord ++ tailWord_1026402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026402).length < 2 ^ (prefixWord ++ tailWord_1026402).sum := by decide
  have hdescent : baseEnd_1026402 < baseStart_1026402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026443 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 3, 3]
def baseStart_1026443 : Nat := 118140960795 + 1026443 * 2 ^ 59
def prefixEnd_1026443 : Nat := 4983230072969 + 3 ^ 40 * 1026443 * 2
def baseEnd_1026443 : Nat := 351372415628688513827987

theorem tailTrace_1026443 : CollatzResearch.WordTrace tailWord_1026443 prefixEnd_1026443 351372415628688513827987 := by
  unfold tailWord_1026443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37437451820379788352963983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24958301213586525568642655 37437451820379788352963983)
  ·
    refine ⟨56156177730569682529445975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37437451820379788352963983 56156177730569682529445975)
    ·
      refine ⟨84234266595854523794168963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56156177730569682529445975 84234266595854523794168963)
      ·
        refine ⟨126351399893781785691253445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84234266595854523794168963 126351399893781785691253445)
        ·
          refine ⟨23690887480084084817110021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126351399893781785691253445 23690887480084084817110021)
          ·
            refine ⟨4442041402515765903208129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23690887480084084817110021 4442041402515765903208129)
            ·
              refine ⟨3331531051886824427406097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4442041402515765903208129 3331531051886824427406097)
              ·
                refine ⟨2498648288915118320554573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331531051886824427406097 2498648288915118320554573)
                ·
                  refine ⟨936993108343169370207965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2498648288915118320554573 936993108343169370207965)
                  ·
                    refine ⟨351372415628688513827987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936993108343169370207965 351372415628688513827987)
                    ·
                      rfl

theorem cell22_1026443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].length) (baseStart_1026443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026443 prefixEnd_1026443 := by exact prefixLift 1026443
  have htrace : WordTrace (prefixWord ++ tailWord_1026443) baseStart_1026443 baseEnd_1026443 := by
    simpa [prefixWord, tailWord_1026443, baseEnd_1026443] using wordTrace_append hprefix tailTrace_1026443
  have hstable : (prefixWord ++ tailWord_1026443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026443).length < 2 ^ (prefixWord ++ tailWord_1026443).sum := by decide
  have hdescent : baseEnd_1026443 < baseStart_1026443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026503 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1026503 : Nat := 118140960795 + 1026503 * 2 ^ 59
def prefixEnd_1026503 : Nat := 4983230072969 + 3 ^ 40 * 1026503 * 2
def baseEnd_1026503 : Nat := 351392954854868357327803

theorem tailTrace_1026503 : CollatzResearch.WordTrace tailWord_1026503 prefixEnd_1026503 351392954854868357327803 := by
  unfold tailWord_1026503
  simp only [CollatzResearch.WordTrace]
  refine ⟨37439640200162418600148163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24959760133441612400098775 37439640200162418600148163)
  ·
    refine ⟨56159460300243627900222245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37439640200162418600148163 56159460300243627900222245)
    ·
      refine ⟨10529898806295680231291671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56159460300243627900222245 10529898806295680231291671)
      ·
        refine ⟨15794848209443520346937507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529898806295680231291671 15794848209443520346937507)
        ·
          refine ⟨23692272314165280520406261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794848209443520346937507 23692272314165280520406261)
          ·
            refine ⟨2221150529452995048788087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23692272314165280520406261 2221150529452995048788087)
            ·
              refine ⟨3331725794179492573182131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221150529452995048788087 3331725794179492573182131)
              ·
                refine ⟨4997588691269238859773197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331725794179492573182131 4997588691269238859773197)
                ·
                  refine ⟨1874095759225964572414949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4997588691269238859773197 1874095759225964572414949)
                  ·
                    refine ⟨351392954854868357327803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874095759225964572414949 351392954854868357327803)
                    ·
                      rfl

theorem cell22_1026503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1026503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026503 prefixEnd_1026503 := by exact prefixLift 1026503
  have htrace : WordTrace (prefixWord ++ tailWord_1026503) baseStart_1026503 baseEnd_1026503 := by
    simpa [prefixWord, tailWord_1026503, baseEnd_1026503] using wordTrace_append hprefix tailTrace_1026503
  have hstable : (prefixWord ++ tailWord_1026503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026503).length < 2 ^ (prefixWord ++ tailWord_1026503).sum := by decide
  have hdescent : baseEnd_1026503 < baseStart_1026503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026535 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 4]
def baseStart_1026535 : Nat := 118140960795 + 1026535 * 2 ^ 59
def prefixEnd_1026535 : Nat := 4983230072969 + 3 ^ 40 * 1026535 * 2
def baseEnd_1026535 : Nat := 117134636369610313509235

theorem tailTrace_1026535 : CollatzResearch.WordTrace tailWord_1026535 prefixEnd_1026535 117134636369610313509235 := by
  unfold tailWord_1026535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440807336046488065313059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960538224030992043542039 37440807336046488065313059)
  ·
    refine ⟨56161211004069732097969589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440807336046488065313059 56161211004069732097969589)
    ·
      refine ⟨5265113531631537384184649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56161211004069732097969589 5265113531631537384184649)
      ·
        refine ⟨3948835148723653038138487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265113531631537384184649 3948835148723653038138487)
        ·
          refine ⟨5923252723085479557207731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948835148723653038138487 5923252723085479557207731)
          ·
            refine ⟨8884879084628219335811597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923252723085479557207731 8884879084628219335811597)
            ·
              refine ⟨3331829656735582250929349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8884879084628219335811597 3331829656735582250929349)
              ·
                refine ⟨624718060637921672049253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3331829656735582250929349 624718060637921672049253)
                ·
                  refine ⟨117134636369610313509235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624718060637921672049253 117134636369610313509235)
                  ·
                    rfl

theorem cell22_1026535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 4].length) (baseStart_1026535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026535 prefixEnd_1026535 := by exact prefixLift 1026535
  have htrace : WordTrace (prefixWord ++ tailWord_1026535) baseStart_1026535 baseEnd_1026535 := by
    simpa [prefixWord, tailWord_1026535, baseEnd_1026535] using wordTrace_append hprefix tailTrace_1026535
  have hstable : (prefixWord ++ tailWord_1026535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026535).length < 2 ^ (prefixWord ++ tailWord_1026535).sum := by decide
  have hdescent : baseEnd_1026535 < baseStart_1026535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026550 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1026550 : Nat := 118140960795 + 1026550 * 2 ^ 59
def prefixEnd_1026550 : Nat := 4983230072969 + 3 ^ 40 * 1026550 * 2
def baseEnd_1026550 : Nat := 351409043915375901402659

theorem tailTrace_1026550 : CollatzResearch.WordTrace tailWord_1026550 prefixEnd_1026550 351409043915375901402659 := by
  unfold tailWord_1026550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340084651937009101694319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24960902953994763751406069 2340084651937009101694319)
  ·
    refine ⟨3510126977905513652541479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340084651937009101694319 3510126977905513652541479)
    ·
      refine ⟨5265190466858270478812219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510126977905513652541479 5265190466858270478812219)
      ·
        refine ⟨7897785700287405718218329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265190466858270478812219 7897785700287405718218329)
        ·
          refine ⟨5923339275215554288663747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897785700287405718218329 5923339275215554288663747)
          ·
            refine ⟨8885008912823331432995621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923339275215554288663747 8885008912823331432995621)
            ·
              refine ⟨1665939171154374643686679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8885008912823331432995621 1665939171154374643686679)
              ·
                refine ⟨2498908756731561965530019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665939171154374643686679 2498908756731561965530019)
                ·
                  refine ⟨3748363135097342948295029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498908756731561965530019 3748363135097342948295029)
                  ·
                    refine ⟨351409043915375901402659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3748363135097342948295029 351409043915375901402659)
                    ·
                      rfl

theorem cell22_1026550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1026550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026550 prefixEnd_1026550 := by exact prefixLift 1026550
  have htrace : WordTrace (prefixWord ++ tailWord_1026550) baseStart_1026550 baseEnd_1026550 := by
    simpa [prefixWord, tailWord_1026550, baseEnd_1026550] using wordTrace_append hprefix tailTrace_1026550
  have hstable : (prefixWord ++ tailWord_1026550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026550).length < 2 ^ (prefixWord ++ tailWord_1026550).sum := by decide
  have hdescent : baseEnd_1026550 < baseStart_1026550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026563 : List Nat := [1, 1, 1, 3, 2, 1, 7, 6]
def baseStart_1026563 : Nat := 118140960795 + 1026563 * 2 ^ 59
def prefixEnd_1026563 : Nat := 4983230072969 + 3 ^ 40 * 1026563 * 2
def baseEnd_1026563 : Nat := 39045943786783133425291

theorem tailTrace_1026563 : CollatzResearch.WordTrace tailWord_1026563 prefixEnd_1026563 39045943786783133425291 := by
  unfold tailWord_1026563
  simp only [CollatzResearch.WordTrace]
  refine ⟨37441828579945048847332343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961219053296699231554895 37441828579945048847332343)
  ·
    refine ⟨56162742869917573270998515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37441828579945048847332343 56162742869917573270998515)
    ·
      refine ⟨84244114304876359906497773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56162742869917573270998515 84244114304876359906497773)
      ·
        refine ⟨31591542864328634964936665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84244114304876359906497773 31591542864328634964936665)
        ·
          refine ⟨23693657148246476223702499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31591542864328634964936665 23693657148246476223702499)
          ·
            refine ⟨35540485722369714335553749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693657148246476223702499 35540485722369714335553749)
            ·
              refine ⟨832980134118040179739541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35540485722369714335553749 832980134118040179739541)
              ·
                refine ⟨39045943786783133425291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 832980134118040179739541 39045943786783133425291)
                ·
                  rfl

theorem cell22_1026563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 6].length) (baseStart_1026563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026563 prefixEnd_1026563 := by exact prefixLift 1026563
  have htrace : WordTrace (prefixWord ++ tailWord_1026563) baseStart_1026563 baseEnd_1026563 := by
    simpa [prefixWord, tailWord_1026563, baseEnd_1026563] using wordTrace_append hprefix tailTrace_1026563
  have hstable : (prefixWord ++ tailWord_1026563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026563).length < 2 ^ (prefixWord ++ tailWord_1026563).sum := by decide
  have hdescent : baseEnd_1026563 < baseStart_1026563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026580 : List Nat := [2, 4, 3, 1, 1, 2, 9]
def baseStart_1026580 : Nat := 118140960795 + 1026580 * 2 ^ 59
def prefixEnd_1026580 : Nat := 4983230072969 + 3 ^ 40 * 1026580 * 2
def baseEnd_1026580 : Nat := 13015530130683919376021

theorem tailTrace_1026580 : CollatzResearch.WordTrace tailWord_1026580 prefixEnd_1026580 13015530130683919376021 := by
  unfold tailWord_1026580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721224310441730375350597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24961632413922307167134129 18721224310441730375350597)
  ·
    refine ⟨3510229558207824445378237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18721224310441730375350597 3510229558207824445378237)
    ·
      refine ⟨1316336084327934167016839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3510229558207824445378237 1316336084327934167016839)
      ·
        refine ⟨1974504126491901250525259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316336084327934167016839 1974504126491901250525259)
        ·
          refine ⟨2961756189737851875787889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974504126491901250525259 2961756189737851875787889)
          ·
            refine ⟨2221317142303388906840917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961756189737851875787889 2221317142303388906840917)
            ·
              refine ⟨13015530130683919376021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2221317142303388906840917 13015530130683919376021)
              ·
                rfl

theorem cell22_1026580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 9].length) (baseStart_1026580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026580 prefixEnd_1026580 := by exact prefixLift 1026580
  have htrace : WordTrace (prefixWord ++ tailWord_1026580) baseStart_1026580 baseEnd_1026580 := by
    simpa [prefixWord, tailWord_1026580, baseEnd_1026580] using wordTrace_append hprefix tailTrace_1026580
  have hstable : (prefixWord ++ tailWord_1026580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026580).length < 2 ^ (prefixWord ++ tailWord_1026580).sum := by decide
  have hdescent : baseEnd_1026580 < baseStart_1026580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026595 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 3, 3]
def baseStart_1026595 : Nat := 118140960795 + 1026595 * 2 ^ 59
def prefixEnd_1026595 : Nat := 4983230072969 + 3 ^ 40 * 1026595 * 2
def baseEnd_1026595 : Nat := 351424448335010784027521

theorem tailTrace_1026595 : CollatzResearch.WordTrace tailWord_1026595 prefixEnd_1026595 351424448335010784027521 := by
  unfold tailWord_1026595
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442995715829118312497239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961997143886078874998159 37442995715829118312497239)
  ·
    refine ⟨56164493573743677468745859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442995715829118312497239 56164493573743677468745859)
    ·
      refine ⟨84246740360615516203118789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56164493573743677468745859 84246740360615516203118789)
      ·
        refine ⟨15796263817615409288084773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84246740360615516203118789 15796263817615409288084773)
        ·
          refine ⟨2961799465802889241515895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15796263817615409288084773 2961799465802889241515895)
          ·
            refine ⟨4442699198704333862273843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961799465802889241515895 4442699198704333862273843)
            ·
              refine ⟨6664048798056500793410765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442699198704333862273843 6664048798056500793410765)
              ·
                refine ⟨2499018299271187797529037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6664048798056500793410765 2499018299271187797529037)
                ·
                  refine ⟨937131862226695424073389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2499018299271187797529037 937131862226695424073389)
                  ·
                    refine ⟨351424448335010784027521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937131862226695424073389 351424448335010784027521)
                    ·
                      rfl

theorem cell22_1026595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].length) (baseStart_1026595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026595 prefixEnd_1026595 := by exact prefixLift 1026595
  have htrace : WordTrace (prefixWord ++ tailWord_1026595) baseStart_1026595 baseEnd_1026595 := by
    simpa [prefixWord, tailWord_1026595, baseEnd_1026595] using wordTrace_append hprefix tailTrace_1026595
  have hstable : (prefixWord ++ tailWord_1026595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026595).length < 2 ^ (prefixWord ++ tailWord_1026595).sum := by decide
  have hdescent : baseEnd_1026595 < baseStart_1026595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026608 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_1026608 : Nat := 118140960795 + 1026608 * 2 ^ 59
def prefixEnd_1026608 : Nat := 4983230072969 + 3 ^ 40 * 1026608 * 2
def baseEnd_1026608 : Nat := 117142966166894361150827

theorem tailTrace_1026608 : CollatzResearch.WordTrace tailWord_1026608 prefixEnd_1026608 117142966166894361150827 := by
  unfold tailWord_1026608
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721734932391010766360239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24962313243188014355146985 18721734932391010766360239)
  ·
    refine ⟨28082602398586516149540359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18721734932391010766360239 28082602398586516149540359)
    ·
      refine ⟨42123903597879774224310539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28082602398586516149540359 42123903597879774224310539)
      ·
        refine ⟨63185855396819661336465809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42123903597879774224310539 63185855396819661336465809)
        ·
          refine ⟨47389391547614746002349357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63185855396819661336465809 47389391547614746002349357)
          ·
            refine ⟨17771021830355529750881009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47389391547614746002349357 17771021830355529750881009)
            ·
              refine ⟨13328266372766647313160757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771021830355529750881009 13328266372766647313160757)
              ·
                refine ⟨1249524972446873185608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13328266372766647313160757 1249524972446873185608821)
                ·
                  refine ⟨117142966166894361150827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249524972446873185608821 117142966166894361150827)
                  ·
                    rfl

theorem cell22_1026608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_1026608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026608 prefixEnd_1026608 := by exact prefixLift 1026608
  have htrace : WordTrace (prefixWord ++ tailWord_1026608) baseStart_1026608 baseEnd_1026608 := by
    simpa [prefixWord, tailWord_1026608, baseEnd_1026608] using wordTrace_append hprefix tailTrace_1026608
  have hstable : (prefixWord ++ tailWord_1026608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026608).length < 2 ^ (prefixWord ++ tailWord_1026608).sum := by decide
  have hdescent : baseEnd_1026608 < baseStart_1026608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026629 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_1026629 : Nat := 118140960795 + 1026629 * 2 ^ 59
def prefixEnd_1026629 : Nat := 4983230072969 + 3 ^ 40 * 1026629 * 2
def baseEnd_1026629 : Nat := 351436087229846028677417

theorem tailTrace_1026629 : CollatzResearch.WordTrace tailWord_1026629 prefixEnd_1026629 351436087229846028677417 := by
  unfold tailWord_1026629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444235797705942119234941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24962823865137294746156627 37444235797705942119234941)
  ·
    refine ⟨14041588424139728294713103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37444235797705942119234941 14041588424139728294713103)
    ·
      refine ⟨21062382636209592442069655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041588424139728294713103 21062382636209592442069655)
      ·
        refine ⟨31593573954314388663104483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062382636209592442069655 31593573954314388663104483)
        ·
          refine ⟨47390360931471582994656725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31593573954314388663104483 47390360931471582994656725)
          ·
            refine ⟨1110711584331365226437267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47390360931471582994656725 1110711584331365226437267)
            ·
              refine ⟨1666067376497047839655901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110711584331365226437267 1666067376497047839655901)
              ·
                refine ⟨624775266186392939870963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1666067376497047839655901 624775266186392939870963)
                ·
                  refine ⟨937162899279589409806445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624775266186392939870963 937162899279589409806445)
                  ·
                    refine ⟨351436087229846028677417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937162899279589409806445 351436087229846028677417)
                    ·
                      rfl

theorem cell22_1026629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_1026629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026629 prefixEnd_1026629 := by exact prefixLift 1026629
  have htrace : WordTrace (prefixWord ++ tailWord_1026629) baseStart_1026629 baseEnd_1026629 := by
    simpa [prefixWord, tailWord_1026629, baseEnd_1026629] using wordTrace_append hprefix tailTrace_1026629
  have hstable : (prefixWord ++ tailWord_1026629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026629).length < 2 ^ (prefixWord ++ tailWord_1026629).sum := by decide
  have hdescent : baseEnd_1026629 < baseStart_1026629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026698 : List Nat := [3, 1, 2, 3, 13]
def baseStart_1026698 : Nat := 118140960795 + 1026698 * 2 ^ 59
def prefixEnd_1026698 : Nat := 4983230072969 + 3 ^ 40 * 1026698 * 2
def baseEnd_1026698 : Nat := 1446336244197336825935

theorem tailTrace_1026698 : CollatzResearch.WordTrace tailWord_1026698 prefixEnd_1026698 1446336244197336825935 := by
  unfold tailWord_1026698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361688108613991725874187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24964501622970644602331165 9361688108613991725874187)
  ·
    refine ⟨14042532162920987588811281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361688108613991725874187 14042532162920987588811281)
    ·
      refine ⟨10531899122190740691608461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14042532162920987588811281 10531899122190740691608461)
      ·
        refine ⟨3949462170821527759353173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10531899122190740691608461 3949462170821527759353173)
        ·
          refine ⟨1446336244197336825935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3949462170821527759353173 1446336244197336825935)
          ·
            rfl

theorem cell22_1026698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 13].length) (baseStart_1026698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026698 prefixEnd_1026698 := by exact prefixLift 1026698
  have htrace : WordTrace (prefixWord ++ tailWord_1026698) baseStart_1026698 baseEnd_1026698 := by
    simpa [prefixWord, tailWord_1026698, baseEnd_1026698] using wordTrace_append hprefix tailTrace_1026698
  have hstable : (prefixWord ++ tailWord_1026698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026698).length < 2 ^ (prefixWord ++ tailWord_1026698).sum := by decide
  have hdescent : baseEnd_1026698 < baseStart_1026698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026734 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1026734 : Nat := 118140960795 + 1026734 * 2 ^ 59
def prefixEnd_1026734 : Nat := 4983230072969 + 3 ^ 40 * 1026734 * 2
def baseEnd_1026734 : Nat := 351472030875660754802095

theorem tailTrace_1026734 : CollatzResearch.WordTrace tailWord_1026734 prefixEnd_1026734 351472030875660754802095 := by
  unfold tailWord_1026734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681008182790693131475907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24965376974883696701204837 4681008182790693131475907)
  ·
    refine ⟨7021512274186039697213861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681008182790693131475907 7021512274186039697213861)
    ·
      refine ⟨1316533551409882443227599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7021512274186039697213861 1316533551409882443227599)
      ·
        refine ⟨1974800327114823664841399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316533551409882443227599 1974800327114823664841399)
        ·
          refine ⟨2962200490672235497262099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974800327114823664841399 2962200490672235497262099)
          ·
            refine ⟨4443300736008353245893149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962200490672235497262099 4443300736008353245893149)
            ·
              refine ⟨1666237776003132467209931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443300736008353245893149 1666237776003132467209931)
              ·
                refine ⟨2499356664004698700814897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666237776003132467209931 2499356664004698700814897)
                ·
                  refine ⟨1874517498003524025611173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499356664004698700814897 1874517498003524025611173)
                  ·
                    refine ⟨351472030875660754802095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874517498003524025611173 351472030875660754802095)
                    ·
                      rfl

theorem cell22_1026734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1026734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026734 prefixEnd_1026734 := by exact prefixLift 1026734
  have htrace : WordTrace (prefixWord ++ tailWord_1026734) baseStart_1026734 baseEnd_1026734 := by
    simpa [prefixWord, tailWord_1026734, baseEnd_1026734] using wordTrace_append hprefix tailTrace_1026734
  have hstable : (prefixWord ++ tailWord_1026734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026734).length < 2 ^ (prefixWord ++ tailWord_1026734).sum := by decide
  have hdescent : baseEnd_1026734 < baseStart_1026734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026753 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1026753 : Nat := 118140960795 + 1026753 * 2 ^ 59
def prefixEnd_1026753 : Nat := 4983230072969 + 3 ^ 40 * 1026753 * 2
def baseEnd_1026753 : Nat := 351478534963951038577037

theorem tailTrace_1026753 : CollatzResearch.WordTrace tailWord_1026753 prefixEnd_1026753 351478534963951038577037 := by
  unfold tailWord_1026753
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448758449256711296748913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24965838966171140864499275 37448758449256711296748913)
  ·
    refine ⟨28086568836942533472561685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37448758449256711296748913 28086568836942533472561685)
    ·
      refine ⟨1316557914231681256526329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28086568836942533472561685 1316557914231681256526329)
      ·
        refine ⟨987418435673760942394747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316557914231681256526329 987418435673760942394747)
        ·
          refine ⟨1481127653510641413592121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987418435673760942394747 1481127653510641413592121)
          ·
            refine ⟨1110845740132981060194091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481127653510641413592121 1110845740132981060194091)
            ·
              refine ⟨1666268610199471590291137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110845740132981060194091 1666268610199471590291137)
              ·
                refine ⟨1249701457649603692718353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666268610199471590291137 1249701457649603692718353)
                ·
                  refine ⟨937276093237202769538765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249701457649603692718353 937276093237202769538765)
                  ·
                    refine ⟨351478534963951038577037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937276093237202769538765 351478534963951038577037)
                    ·
                      rfl

theorem cell22_1026753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1026753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026753 prefixEnd_1026753 := by exact prefixLift 1026753
  have htrace : WordTrace (prefixWord ++ tailWord_1026753) baseStart_1026753 baseEnd_1026753 := by
    simpa [prefixWord, tailWord_1026753, baseEnd_1026753] using wordTrace_append hprefix tailTrace_1026753
  have hstable : (prefixWord ++ tailWord_1026753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026753).length < 2 ^ (prefixWord ++ tailWord_1026753).sum := by decide
  have hdescent : baseEnd_1026753 < baseStart_1026753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026760 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_1026760 : Nat := 118140960795 + 1026760 * 2 ^ 59
def prefixEnd_1026760 : Nat := 4983230072969 + 3 ^ 40 * 1026760 * 2
def baseEnd_1026760 : Nat := 117160310402335117884005

theorem tailTrace_1026760 : CollatzResearch.WordTrace tailWord_1026760 prefixEnd_1026760 117160310402335117884005 := by
  unfold tailWord_1026760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724506880115675746126867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24966009173487567661502489 18724506880115675746126867)
  ·
    refine ⟨28086760320173513619190301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18724506880115675746126867 28086760320173513619190301)
    ·
      refine ⟨10532535120065067607196363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28086760320173513619190301 10532535120065067607196363)
      ·
        refine ⟨15798802680097601410794545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532535120065067607196363 15798802680097601410794545)
        ·
          refine ⟨11849102010073201058095909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15798802680097601410794545 11849102010073201058095909)
          ·
            refine ⟨2221706626888725198392983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11849102010073201058095909 2221706626888725198392983)
            ·
              refine ⟨3332559940333087797589475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221706626888725198392983 3332559940333087797589475)
              ·
                refine ⟨4998839910499631696384213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332559940333087797589475 4998839910499631696384213)
                ·
                  refine ⟨117160310402335117884005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4998839910499631696384213 117160310402335117884005)
                  ·
                    rfl

theorem cell22_1026760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_1026760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026760 prefixEnd_1026760 := by exact prefixLift 1026760
  have htrace : WordTrace (prefixWord ++ tailWord_1026760) baseStart_1026760 baseEnd_1026760 := by
    simpa [prefixWord, tailWord_1026760, baseEnd_1026760] using wordTrace_append hprefix tailTrace_1026760
  have hstable : (prefixWord ++ tailWord_1026760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026760).length < 2 ^ (prefixWord ++ tailWord_1026760).sum := by decide
  have hdescent : baseEnd_1026760 < baseStart_1026760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026764 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_1026764 : Nat := 118140960795 + 1026764 * 2 ^ 59
def prefixEnd_1026764 : Nat := 4983230072969 + 3 ^ 40 * 1026764 * 2
def baseEnd_1026764 : Nat := 351482300488750676552003

theorem tailTrace_1026764 : CollatzResearch.WordTrace tailWord_1026764 prefixEnd_1026764 351482300488750676552003 := by
  unfold tailWord_1026764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724579826108430087699673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24966106434811240116932897 18724579826108430087699673)
  ·
    refine ⟨14043434869581322565774755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18724579826108430087699673 14043434869581322565774755)
    ·
      refine ⟨21065152304371983848662133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043434869581322565774755 21065152304371983848662133)
      ·
        refine ⟨1974858028534873485812075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21065152304371983848662133 1974858028534873485812075)
        ·
          refine ⟨2962287042802310228718113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974858028534873485812075 2962287042802310228718113)
          ·
            refine ⟨2221715282101732671538585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962287042802310228718113 2221715282101732671538585)
            ·
              refine ⟨1666286461576299503653939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221715282101732671538585 1666286461576299503653939)
              ·
                refine ⟨2499429692364449255480909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666286461576299503653939 2499429692364449255480909)
                ·
                  refine ⟨937286134636668470805341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2499429692364449255480909 937286134636668470805341)
                  ·
                    refine ⟨351482300488750676552003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937286134636668470805341 351482300488750676552003)
                    ·
                      rfl

theorem cell22_1026764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_1026764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026764 prefixEnd_1026764 := by exact prefixLift 1026764
  have htrace : WordTrace (prefixWord ++ tailWord_1026764) baseStart_1026764 baseEnd_1026764 := by
    simpa [prefixWord, tailWord_1026764, baseEnd_1026764] using wordTrace_append hprefix tailTrace_1026764
  have hstable : (prefixWord ++ tailWord_1026764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026764).length < 2 ^ (prefixWord ++ tailWord_1026764).sum := by decide
  have hdescent : baseEnd_1026764 < baseStart_1026764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026775 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1026775 : Nat := 118140960795 + 1026775 * 2 ^ 59
def prefixEnd_1026775 : Nat := 4983230072969 + 3 ^ 40 * 1026775 * 2
def baseEnd_1026775 : Nat := 351486066013550314526969

theorem tailTrace_1026775 : CollatzResearch.WordTrace tailWord_1026775 prefixEnd_1026775 351486066013550314526969 := by
  unfold tailWord_1026775
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449560855177009054049779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24966373903451339369366519 37449560855177009054049779)
  ·
    refine ⟨56174341282765513581074669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37449560855177009054049779 56174341282765513581074669)
    ·
      refine ⟨21065377981037067592903001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56174341282765513581074669 21065377981037067592903001)
      ·
        refine ⟨15799033485777800694677251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21065377981037067592903001 15799033485777800694677251)
        ·
          refine ⟨23698550228666701042015877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15799033485777800694677251 23698550228666701042015877)
          ·
            refine ⟨4443478167875006445377977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23698550228666701042015877 4443478167875006445377977)
            ·
              refine ⟨3332608625906254834033483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443478167875006445377977 3332608625906254834033483)
              ·
                refine ⟨4998912938859382251050225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332608625906254834033483 4998912938859382251050225)
                ·
                  refine ⟨3749184704144536688287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998912938859382251050225 3749184704144536688287669)
                  ·
                    refine ⟨351486066013550314526969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3749184704144536688287669 351486066013550314526969)
                    ·
                      rfl

theorem cell22_1026775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1026775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026775 prefixEnd_1026775 := by exact prefixLift 1026775
  have htrace : WordTrace (prefixWord ++ tailWord_1026775) baseStart_1026775 baseEnd_1026775 := by
    simpa [prefixWord, tailWord_1026775, baseEnd_1026775] using wordTrace_append hprefix tailTrace_1026775
  have hstable : (prefixWord ++ tailWord_1026775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026775).length < 2 ^ (prefixWord ++ tailWord_1026775).sum := by decide
  have hdescent : baseEnd_1026775 < baseStart_1026775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026777 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 5]
def baseStart_1026777 : Nat := 118140960795 + 1026777 * 2 ^ 59
def prefixEnd_1026777 : Nat := 4983230072969 + 3 ^ 40 * 1026777 * 2
def baseEnd_1026777 : Nat := 117162250218140991992321

theorem tailTrace_1026777 : CollatzResearch.WordTrace tailWord_1026777 prefixEnd_1026777 117162250218140991992321 := by
  unfold tailWord_1026777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449633801169763395622585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24966422534113175597081723 37449633801169763395622585)
  ·
    refine ⟨28087225350877322546716939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37449633801169763395622585 28087225350877322546716939)
    ·
      refine ⟨42130838026315983820075409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28087225350877322546716939 42130838026315983820075409)
      ·
        refine ⟨31598128519736987865056557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42130838026315983820075409 31598128519736987865056557)
        ·
          refine ⟨11849298194901370449396209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31598128519736987865056557 11849298194901370449396209)
          ·
            refine ⟨8886973646176027837047157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849298194901370449396209 8886973646176027837047157)
            ·
              refine ⟨833153779329002609723171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8886973646176027837047157 833153779329002609723171)
              ·
                refine ⟨1249730668993503914584757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833153779329002609723171 1249730668993503914584757)
                ·
                  refine ⟨117162250218140991992321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249730668993503914584757 117162250218140991992321)
                  ·
                    rfl

theorem cell22_1026777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_1026777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026777 prefixEnd_1026777 := by exact prefixLift 1026777
  have htrace : WordTrace (prefixWord ++ tailWord_1026777) baseStart_1026777 baseEnd_1026777 := by
    simpa [prefixWord, tailWord_1026777, baseEnd_1026777] using wordTrace_append hprefix tailTrace_1026777
  have hstable : (prefixWord ++ tailWord_1026777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026777).length < 2 ^ (prefixWord ++ tailWord_1026777).sum := by decide
  have hdescent : baseEnd_1026777 < baseStart_1026777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026835 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_1026835 : Nat := 118140960795 + 1026835 * 2 ^ 59
def prefixEnd_1026835 : Nat := 4983230072969 + 3 ^ 40 * 1026835 * 2
def baseEnd_1026835 : Nat := 351506605239730158026785

theorem tailTrace_1026835 : CollatzResearch.WordTrace tailWord_1026835 prefixEnd_1026835 351506605239730158026785 := by
  unfold tailWord_1026835
  simp only [CollatzResearch.WordTrace]
  refine ⟨37451749234959639301233959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24967832823306426200822639 37451749234959639301233959)
  ·
    refine ⟨56177623852439458951850939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37451749234959639301233959 56177623852439458951850939)
    ·
      refine ⟨84266435778659188427776409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56177623852439458951850939 84266435778659188427776409)
      ·
        refine ⟨63199826833994391320832307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84266435778659188427776409 63199826833994391320832307)
        ·
          refine ⟨94799740250991586981248461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63199826833994391320832307 94799740250991586981248461)
          ·
            refine ⟨35549902594121845117968173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94799740250991586981248461 35549902594121845117968173)
            ·
              refine ⟨13331213472795691919238065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35549902594121845117968173 13331213472795691919238065)
              ·
                refine ⟨9998410104596768939428549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331213472795691919238065 9998410104596768939428549)
                ·
                  refine ⟨1874701894611894176142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9998410104596768939428549 1874701894611894176142853)
                  ·
                    refine ⟨351506605239730158026785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874701894611894176142853 351506605239730158026785)
                    ·
                      rfl

theorem cell22_1026835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_1026835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026835 prefixEnd_1026835 := by exact prefixLift 1026835
  have htrace : WordTrace (prefixWord ++ tailWord_1026835) baseStart_1026835 baseEnd_1026835 := by
    simpa [prefixWord, tailWord_1026835, baseEnd_1026835] using wordTrace_append hprefix tailTrace_1026835
  have hstable : (prefixWord ++ tailWord_1026835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026835).length < 2 ^ (prefixWord ++ tailWord_1026835).sum := by decide
  have hdescent : baseEnd_1026835 < baseStart_1026835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026858 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1026858 : Nat := 118140960795 + 1026858 * 2 ^ 59
def prefixEnd_1026858 : Nat := 4983230072969 + 3 ^ 40 * 1026858 * 2
def baseEnd_1026858 : Nat := 351514478609765764701715

theorem tailTrace_1026858 : CollatzResearch.WordTrace tailWord_1026858 prefixEnd_1026858 351514478609765764701715 := by
  unfold tailWord_1026858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363147028469078557330307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24968392075917542819547485 9363147028469078557330307)
  ·
    refine ⟨14044720542703617835995461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363147028469078557330307 14044720542703617835995461)
    ·
      refine ⟨2633385101756928344249149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14044720542703617835995461 2633385101756928344249149)
      ·
        refine ⟨987519413158848129093431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2633385101756928344249149 987519413158848129093431)
        ·
          refine ⟨1481279119738272193640147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987519413158848129093431 1481279119738272193640147)
          ·
            refine ⟨2221918679607408290460221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481279119738272193640147 2221918679607408290460221)
            ·
              refine ⟨833219504852778108922583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2221918679607408290460221 833219504852778108922583)
              ·
                refine ⟨1249829257279167163383875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833219504852778108922583 1249829257279167163383875)
                ·
                  refine ⟨1874743885918750745075813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249829257279167163383875 1874743885918750745075813)
                  ·
                    refine ⟨351514478609765764701715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874743885918750745075813 351514478609765764701715)
                    ·
                      rfl

theorem cell22_1026858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1026858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026858 prefixEnd_1026858 := by exact prefixLift 1026858
  have htrace : WordTrace (prefixWord ++ tailWord_1026858) baseStart_1026858 baseEnd_1026858 := by
    simpa [prefixWord, tailWord_1026858, baseEnd_1026858] using wordTrace_append hprefix tailTrace_1026858
  have hstable : (prefixWord ++ tailWord_1026858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026858).length < 2 ^ (prefixWord ++ tailWord_1026858).sum := by decide
  have hdescent : baseEnd_1026858 < baseStart_1026858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026916 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_1026916 : Nat := 118140960795 + 1026916 * 2 ^ 59
def prefixEnd_1026916 : Nat := 4983230072969 + 3 ^ 40 * 1026916 * 2
def baseEnd_1026916 : Nat := 351534333195072946751537

theorem tailTrace_1026916 : CollatzResearch.WordTrace tailWord_1026916 prefixEnd_1026916 351534333195072946751537 := by
  unfold tailWord_1026916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18727351773833095067466301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24969802365110793423288401 18727351773833095067466301)
  ·
    refine ⟨7022756915187410650299863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18727351773833095067466301 7022756915187410650299863)
    ·
      refine ⟨10534135372781115975449795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022756915187410650299863 10534135372781115975449795)
      ·
        refine ⟨15801203059171673963174693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10534135372781115975449795 15801203059171673963174693)
        ·
          refine ⟨2962725573594688868095255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15801203059171673963174693 2962725573594688868095255)
          ·
            refine ⟨4444088360392033302142883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962725573594688868095255 4444088360392033302142883)
            ·
              refine ⟨6666132540588049953214325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444088360392033302142883 6666132540588049953214325)
              ·
                refine ⟨624949925680129683113843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6666132540588049953214325 624949925680129683113843)
                ·
                  refine ⟨937424888520194524670765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624949925680129683113843 937424888520194524670765)
                  ·
                    refine ⟨351534333195072946751537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937424888520194524670765 351534333195072946751537)
                    ·
                      rfl

theorem cell22_1026916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_1026916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026916 prefixEnd_1026916 := by exact prefixLift 1026916
  have htrace : WordTrace (prefixWord ++ tailWord_1026916) baseStart_1026916 baseEnd_1026916 := by
    simpa [prefixWord, tailWord_1026916, baseEnd_1026916] using wordTrace_append hprefix tailTrace_1026916
  have hstable : (prefixWord ++ tailWord_1026916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026916).length < 2 ^ (prefixWord ++ tailWord_1026916).sum := by decide
  have hdescent : baseEnd_1026916 < baseStart_1026916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026929 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 5]
def baseStart_1026929 : Nat := 118140960795 + 1026929 * 2 ^ 59
def prefixEnd_1026929 : Nat := 4983230072969 + 3 ^ 40 * 1026929 * 2
def baseEnd_1026929 : Nat := 117179594453581748725499

theorem tailTrace_1026929 : CollatzResearch.WordTrace tailWord_1026929 prefixEnd_1026929 117179594453581748725499 := by
  unfold tailWord_1026929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37455177696619093355155841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24970118464412728903437227 37455177696619093355155841)
  ·
    refine ⟨28091383272464320016366881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37455177696619093355155841 28091383272464320016366881)
    ·
      refine ⟨21068537454348240012275161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28091383272464320016366881 21068537454348240012275161)
      ·
        refine ⟨15801403090761180009206371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21068537454348240012275161 15801403090761180009206371)
        ·
          refine ⟨23702104636141770013809557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801403090761180009206371 23702104636141770013809557)
          ·
            refine ⟨1111036154819145469397323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23702104636141770013809557 1111036154819145469397323)
            ·
              refine ⟨1666554232228718204095985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111036154819145469397323 1666554232228718204095985)
              ·
                refine ⟨1249915674171538653071989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666554232228718204095985 1249915674171538653071989)
                ·
                  refine ⟨117179594453581748725499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249915674171538653071989 117179594453581748725499)
                  ·
                    rfl

theorem cell22_1026929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_1026929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026929 prefixEnd_1026929 := by exact prefixLift 1026929
  have htrace : WordTrace (prefixWord ++ tailWord_1026929) baseStart_1026929 baseEnd_1026929 := by
    simpa [prefixWord, tailWord_1026929, baseEnd_1026929] using wordTrace_append hprefix tailTrace_1026929
  have hstable : (prefixWord ++ tailWord_1026929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026929).length < 2 ^ (prefixWord ++ tailWord_1026929).sum := by decide
  have hdescent : baseEnd_1026929 < baseStart_1026929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026987 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_1026987 : Nat := 118140960795 + 1026987 * 2 ^ 59
def prefixEnd_1026987 : Nat := 4983230072969 + 3 ^ 40 * 1026987 * 2
def baseEnd_1026987 : Nat := 351558637946052428226319

theorem tailTrace_1026987 : CollatzResearch.WordTrace tailWord_1026987 prefixEnd_1026987 351558637946052428226319 := by
  unfold tailWord_1026987
  simp only [CollatzResearch.WordTrace]
  refine ⟨37457293130408969260767215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24971528753605979507178143 37457293130408969260767215)
  ·
    refine ⟨56185939695613453891150823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37457293130408969260767215 56185939695613453891150823)
    ·
      refine ⟨84278909543420180836726235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56185939695613453891150823 84278909543420180836726235)
      ·
        refine ⟨126418364315130271255089353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84278909543420180836726235 126418364315130271255089353)
        ·
          refine ⟨94813773236347703441317015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126418364315130271255089353 94813773236347703441317015)
          ·
            refine ⟨142220659854521555161975523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94813773236347703441317015 142220659854521555161975523)
            ·
              refine ⟨213330989781782332742963285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142220659854521555161975523 213330989781782332742963285)
              ·
                refine ⟨2499972536505261711831601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 213330989781782332742963285 2499972536505261711831601)
                ·
                  refine ⟨1874979402378946283873701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499972536505261711831601 1874979402378946283873701)
                  ·
                    refine ⟨351558637946052428226319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874979402378946283873701 351558637946052428226319)
                    ·
                      rfl

theorem cell22_1026987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_1026987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1026987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1026987 prefixEnd_1026987 := by exact prefixLift 1026987
  have htrace : WordTrace (prefixWord ++ tailWord_1026987) baseStart_1026987 baseEnd_1026987 := by
    simpa [prefixWord, tailWord_1026987, baseEnd_1026987] using wordTrace_append hprefix tailTrace_1026987
  have hstable : (prefixWord ++ tailWord_1026987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026987).length < 2 ^ (prefixWord ++ tailWord_1026987).sum := by decide
  have hdescent : baseEnd_1026987 < baseStart_1026987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027002 : List Nat := [3, 1, 1, 1, 2, 1, 6, 7]
def baseStart_1027002 : Nat := 118140960795 + 1027002 * 2 ^ 59
def prefixEnd_1027002 : Nat := 4983230072969 + 3 ^ 40 * 1027002 * 2
def baseEnd_1027002 : Nat := 39062641416955265455697

theorem tailTrace_1027002 : CollatzResearch.WordTrace tailWord_1027002 prefixEnd_1027002 39062641416955265455697 := by
  unfold tailWord_1027002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364460056338656705640815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24971893483569751215042173 9364460056338656705640815)
  ·
    refine ⟨14046690084507985058461223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364460056338656705640815 14046690084507985058461223)
    ·
      refine ⟨21070035126761977587691835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046690084507985058461223 21070035126761977587691835)
      ·
        refine ⟨31605052690142966381537753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21070035126761977587691835 31605052690142966381537753)
        ·
          refine ⟨23703789517607224786153315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31605052690142966381537753 23703789517607224786153315)
          ·
            refine ⟨35555684276410837179229973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23703789517607224786153315 35555684276410837179229973)
            ·
              refine ⟨1666672700456757992776405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35555684276410837179229973 1666672700456757992776405)
              ·
                refine ⟨39062641416955265455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1666672700456757992776405 39062641416955265455697)
                ·
                  rfl

theorem cell22_1027002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_1027002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027002 prefixEnd_1027002 := by exact prefixLift 1027002
  have htrace : WordTrace (prefixWord ++ tailWord_1027002) baseStart_1027002 baseEnd_1027002 := by
    simpa [prefixWord, tailWord_1027002, baseEnd_1027002] using wordTrace_append hprefix tailTrace_1027002
  have hstable : (prefixWord ++ tailWord_1027002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027002).length < 2 ^ (prefixWord ++ tailWord_1027002).sum := by decide
  have hdescent : baseEnd_1027002 < baseStart_1027002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027006 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1027006 : Nat := 118140960795 + 1027006 * 2 ^ 59
def prefixEnd_1027006 : Nat := 4983230072969 + 3 ^ 40 * 1027006 * 2
def baseEnd_1027006 : Nat := 351565142034342712001261

theorem tailTrace_1027006 : CollatzResearch.WordTrace tailWord_1027006 prefixEnd_1027006 351565142034342712001261 := by
  unfold tailWord_1027006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682248264667516938213609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24971990744893423670472581 4682248264667516938213609)
  ·
    refine ⟨3511686198500637703660207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4682248264667516938213609 3511686198500637703660207)
    ·
      refine ⟨5267529297750956555490311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511686198500637703660207 5267529297750956555490311)
      ·
        refine ⟨7901293946626434833235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267529297750956555490311 7901293946626434833235467)
        ·
          refine ⟨11851940919939652249853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901293946626434833235467 11851940919939652249853201)
          ·
            refine ⟨8888955689954739187389901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11851940919939652249853201 8888955689954739187389901)
            ·
              refine ⟨3333358383733027195271213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8888955689954739187389901 3333358383733027195271213)
              ·
                refine ⟨1250009393899885198226705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333358383733027195271213 1250009393899885198226705)
                ·
                  refine ⟨937507045424913898670029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250009393899885198226705 937507045424913898670029)
                  ·
                    refine ⟨351565142034342712001261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937507045424913898670029 351565142034342712001261)
                    ·
                      rfl

theorem cell22_1027006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1027006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027006 prefixEnd_1027006 := by exact prefixLift 1027006
  have htrace : WordTrace (prefixWord ++ tailWord_1027006) baseStart_1027006 baseEnd_1027006 := by
    simpa [prefixWord, tailWord_1027006, baseEnd_1027006] using wordTrace_append hprefix tailTrace_1027006
  have hstable : (prefixWord ++ tailWord_1027006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027006).length < 2 ^ (prefixWord ++ tailWord_1027006).sum := by decide
  have hdescent : baseEnd_1027006 < baseStart_1027006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027109 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 6]
def baseStart_1027109 : Nat := 118140960795 + 1027109 * 2 ^ 59
def prefixEnd_1027109 : Nat := 4983230072969 + 3 ^ 40 * 1027109 * 2
def baseEnd_1027109 : Nat := 117200133679761592225315

theorem tailTrace_1027109 : CollatzResearch.WordTrace tailWord_1027109 prefixEnd_1027109 117200133679761592225315 := by
  unfold tailWord_1027109
  simp only [CollatzResearch.WordTrace]
  refine ⟨37461742835966984096708381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24974495223977989397805587 37461742835966984096708381)
  ·
    refine ⟨14048153563487619036265643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37461742835966984096708381 14048153563487619036265643)
    ·
      refine ⟨21072230345231428554398465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14048153563487619036265643 21072230345231428554398465)
      ·
        refine ⟨15804172758923571415798849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21072230345231428554398465 15804172758923571415798849)
        ·
          refine ⟨11853129569192678561849137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804172758923571415798849 11853129569192678561849137)
          ·
            refine ⟨8889847176894508921386853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11853129569192678561849137 8889847176894508921386853)
            ·
              refine ⟨1666846345667720422760035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8889847176894508921386853 1666846345667720422760035)
              ·
                refine ⟨2500269518501580634140053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666846345667720422760035 2500269518501580634140053)
                ·
                  refine ⟨117200133679761592225315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500269518501580634140053 117200133679761592225315)
                  ·
                    rfl

theorem cell22_1027109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_1027109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027109 prefixEnd_1027109 := by exact prefixLift 1027109
  have htrace : WordTrace (prefixWord ++ tailWord_1027109) baseStart_1027109 baseEnd_1027109 := by
    simpa [prefixWord, tailWord_1027109, baseEnd_1027109] using wordTrace_append hprefix tailTrace_1027109
  have hstable : (prefixWord ++ tailWord_1027109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027109).length < 2 ^ (prefixWord ++ tailWord_1027109).sum := by decide
  have hdescent : baseEnd_1027109 < baseStart_1027109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027126 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1027126 : Nat := 118140960795 + 1027126 * 2 ^ 59
def prefixEnd_1027126 : Nat := 4983230072969 + 3 ^ 40 * 1027126 * 2
def baseEnd_1027126 : Nat := 117202073495567466333631

theorem tailTrace_1027126 : CollatzResearch.WordTrace tailWord_1027126 prefixEnd_1027126 117202073495567466333631 := by
  unfold tailWord_1027126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341397679806587250004827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24974908584603597333384821 2341397679806587250004827)
  ·
    refine ⟨3512096519709880875007241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341397679806587250004827 3512096519709880875007241)
    ·
      refine ⟨2634072389782410656255431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512096519709880875007241 2634072389782410656255431)
      ·
        refine ⟨3951108584673615984383147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634072389782410656255431 3951108584673615984383147)
        ·
          refine ⟨5926662877010423976574721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951108584673615984383147 5926662877010423976574721)
          ·
            refine ⟨4444997157757817982431041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926662877010423976574721 4444997157757817982431041)
            ·
              refine ⟨3333747868318363486823281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444997157757817982431041 3333747868318363486823281)
              ·
                refine ⟨2500310901238772615117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333747868318363486823281 2500310901238772615117461)
                ·
                  refine ⟨117202073495567466333631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500310901238772615117461 117202073495567466333631)
                  ·
                    rfl

theorem cell22_1027126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1027126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027126 prefixEnd_1027126 := by exact prefixLift 1027126
  have htrace : WordTrace (prefixWord ++ tailWord_1027126) baseStart_1027126 baseEnd_1027126 := by
    simpa [prefixWord, tailWord_1027126, baseEnd_1027126] using wordTrace_append hprefix tailTrace_1027126
  have hstable : (prefixWord ++ tailWord_1027126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027126).length < 2 ^ (prefixWord ++ tailWord_1027126).sum := by decide
  have hdescent : baseEnd_1027126 < baseStart_1027126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027139 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_1027139 : Nat := 118140960795 + 1027139 * 2 ^ 59
def prefixEnd_1027139 : Nat := 4983230072969 + 3 ^ 40 * 1027139 * 2
def baseEnd_1027139 : Nat := 351610670652374698425853

theorem tailTrace_1027139 : CollatzResearch.WordTrace tailWord_1027139 prefixEnd_1027139 351610670652374698425853 := by
  unfold tailWord_1027139
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462837025858299220300471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24975224683905532813533647 37462837025858299220300471)
  ·
    refine ⟨56194255538787448830450707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37462837025858299220300471 56194255538787448830450707)
    ·
      refine ⟨84291383308181173245676061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56194255538787448830450707 84291383308181173245676061)
      ·
        refine ⟨31609268740567939967128523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84291383308181173245676061 31609268740567939967128523)
        ·
          refine ⟨47413903110851909950692785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31609268740567939967128523 47413903110851909950692785)
          ·
            refine ⟨35560427333138932463019589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47413903110851909950692785 35560427333138932463019589)
            ·
              refine ⟨6667580124963549836816173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35560427333138932463019589 6667580124963549836816173)
              ·
                refine ⟨2500342546861331188806065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6667580124963549836816173 2500342546861331188806065)
                ·
                  refine ⟨1875256910145998391604549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500342546861331188806065 1875256910145998391604549)
                  ·
                    refine ⟨351610670652374698425853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875256910145998391604549 351610670652374698425853)
                    ·
                      rfl

theorem cell22_1027139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_1027139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027139 prefixEnd_1027139 := by exact prefixLift 1027139
  have htrace : WordTrace (prefixWord ++ tailWord_1027139) baseStart_1027139 baseEnd_1027139 := by
    simpa [prefixWord, tailWord_1027139, baseEnd_1027139] using wordTrace_append hprefix tailTrace_1027139
  have hstable : (prefixWord ++ tailWord_1027139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027139).length < 2 ^ (prefixWord ++ tailWord_1027139).sum := by decide
  have hdescent : baseEnd_1027139 < baseStart_1027139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027143 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 4]
def baseStart_1027143 : Nat := 118140960795 + 1027143 * 2 ^ 59
def prefixEnd_1027143 : Nat := 4983230072969 + 3 ^ 40 * 1027143 * 2
def baseEnd_1027143 : Nat := 117204013311373340441947

theorem tailTrace_1027143 : CollatzResearch.WordTrace tailWord_1027143 prefixEnd_1027143 117204013311373340441947 := by
  unfold tailWord_1027143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462982917843807903446083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24975321945229205268964055 37462982917843807903446083)
  ·
    refine ⟨56194474376765711855169125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37462982917843807903446083 56194474376765711855169125)
    ·
      refine ⟨10536463945643570972844211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56194474376765711855169125 10536463945643570972844211)
      ·
        refine ⟨15804695918465356459266317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536463945643570972844211 15804695918465356459266317)
        ·
          refine ⟨5926760969424508672224869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15804695918465356459266317 5926760969424508672224869)
          ·
            refine ⟨1111267681767095376042163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5926760969424508672224869 1111267681767095376042163)
            ·
              refine ⟨1666901522650643064063245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111267681767095376042163 1666901522650643064063245)
              ·
                refine ⟨625088070993991149023717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1666901522650643064063245 625088070993991149023717)
                ·
                  refine ⟨117204013311373340441947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625088070993991149023717 117204013311373340441947)
                  ·
                    rfl

theorem cell22_1027143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 4].length) (baseStart_1027143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027143 prefixEnd_1027143 := by exact prefixLift 1027143
  have htrace : WordTrace (prefixWord ++ tailWord_1027143) baseStart_1027143 baseEnd_1027143 := by
    simpa [prefixWord, tailWord_1027143, baseEnd_1027143] using wordTrace_append hprefix tailTrace_1027143
  have hstable : (prefixWord ++ tailWord_1027143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027143).length < 2 ^ (prefixWord ++ tailWord_1027143).sum := by decide
  have hdescent : baseEnd_1027143 < baseStart_1027143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027154 : List Nat := [3, 2, 2, 1, 3, 1, 10]
def baseStart_1027154 : Nat := 118140960795 + 1027154 * 2 ^ 59
def prefixEnd_1027154 : Nat := 4983230072969 + 3 ^ 40 * 1027154 * 2
def baseEnd_1027154 : Nat := 13022807609589617011141

theorem tailTrace_1027154 : CollatzResearch.WordTrace tailWord_1027154 prefixEnd_1027154 13022807609589617011141 := by
  unfold tailWord_1027154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365846030200989195524129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24975589413869304521397677 9365846030200989195524129)
  ·
    refine ⟨7024384522650741896643097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9365846030200989195524129 7024384522650741896643097)
    ·
      refine ⟨5268288391988056422482323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7024384522650741896643097 5268288391988056422482323)
      ·
        refine ⟨7902432587982084633723485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268288391988056422482323 7902432587982084633723485)
        ·
          refine ⟨2963412220493281737646307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7902432587982084633723485 2963412220493281737646307)
          ·
            refine ⟨4445118330739922606469461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963412220493281737646307 4445118330739922606469461)
            ·
              refine ⟨13022807609589617011141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4445118330739922606469461 13022807609589617011141)
              ·
                rfl

theorem cell22_1027154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 10].length) (baseStart_1027154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027154 prefixEnd_1027154 := by exact prefixLift 1027154
  have htrace : WordTrace (prefixWord ++ tailWord_1027154) baseStart_1027154 baseEnd_1027154 := by
    simpa [prefixWord, tailWord_1027154, baseEnd_1027154] using wordTrace_append hprefix tailTrace_1027154
  have hstable : (prefixWord ++ tailWord_1027154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027154).length < 2 ^ (prefixWord ++ tailWord_1027154).sum := by decide
  have hdescent : baseEnd_1027154 < baseStart_1027154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027175 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1027175 : Nat := 118140960795 + 1027175 * 2 ^ 59
def prefixEnd_1027175 : Nat := 4983230072969 + 3 ^ 40 * 1027175 * 2
def baseEnd_1027175 : Nat := 351622994188082604525743

theorem tailTrace_1027175 : CollatzResearch.WordTrace tailWord_1027175 prefixEnd_1027175 351622994188082604525743 := by
  unfold tailWord_1027175
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464150053727877368610979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24976100035818584912407319 37464150053727877368610979)
  ·
    refine ⟨56196225080591816052916469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37464150053727877368610979 56196225080591816052916469)
    ·
      refine ⟨5268396101305482754960919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56196225080591816052916469 5268396101305482754960919)
      ·
        refine ⟨7902594151958224132441379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268396101305482754960919 7902594151958224132441379)
        ·
          refine ⟨11853891227937336198662069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902594151958224132441379 11853891227937336198662069)
          ·
            refine ⟨1111302302619125268624569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11853891227937336198662069 1111302302619125268624569)
            ·
              refine ⟨833476726964343951468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111302302619125268624569 833476726964343951468427)
              ·
                refine ⟨1250215090446515927202641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833476726964343951468427 1250215090446515927202641)
                ·
                  refine ⟨937661317834886945401981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250215090446515927202641 937661317834886945401981)
                  ·
                    refine ⟨351622994188082604525743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937661317834886945401981 351622994188082604525743)
                    ·
                      rfl

theorem cell22_1027175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1027175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027175 prefixEnd_1027175 := by exact prefixLift 1027175
  have htrace : WordTrace (prefixWord ++ tailWord_1027175) baseStart_1027175 baseEnd_1027175 := by
    simpa [prefixWord, tailWord_1027175, baseEnd_1027175] using wordTrace_append hprefix tailTrace_1027175
  have hstable : (prefixWord ++ tailWord_1027175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027175).length < 2 ^ (prefixWord ++ tailWord_1027175).sum := by decide
  have hdescent : baseEnd_1027175 < baseStart_1027175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027186 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1027186 : Nat := 118140960795 + 1027186 * 2 ^ 59
def prefixEnd_1027186 : Nat := 4983230072969 + 3 ^ 40 * 1027186 * 2
def baseEnd_1027186 : Nat := 351626759712882242500709

theorem tailTrace_1027186 : CollatzResearch.WordTrace tailWord_1027186 prefixEnd_1027186 351626759712882242500709 := by
  unfold tailWord_1027186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366137814172006561815353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24976367504458684164840941 9366137814172006561815353)
  ·
    refine ⟨7024603360629004921361515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9366137814172006561815353 7024603360629004921361515)
    ·
      refine ⟨10536905040943507382042273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024603360629004921361515 10536905040943507382042273)
      ·
        refine ⟨7902678780707630536531705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10536905040943507382042273 7902678780707630536531705)
        ·
          refine ⟨5927009085530722902398779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902678780707630536531705 5927009085530722902398779)
          ·
            refine ⟨8890513628296084353598169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927009085530722902398779 8890513628296084353598169)
            ·
              refine ⟨6667885221222063265198627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890513628296084353598169 6667885221222063265198627)
              ·
                refine ⟨10001827831833094897797941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667885221222063265198627 10001827831833094897797941)
                ·
                  refine ⟨937671359234352646668557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10001827831833094897797941 937671359234352646668557)
                  ·
                    refine ⟨351626759712882242500709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937671359234352646668557 351626759712882242500709)
                    ·
                      rfl

theorem cell22_1027186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1027186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027186 prefixEnd_1027186 := by exact prefixLift 1027186
  have htrace : WordTrace (prefixWord ++ tailWord_1027186) baseStart_1027186 baseEnd_1027186 := by
    simpa [prefixWord, tailWord_1027186, baseEnd_1027186] using wordTrace_append hprefix tailTrace_1027186
  have hstable : (prefixWord ++ tailWord_1027186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027186).length < 2 ^ (prefixWord ++ tailWord_1027186).sum := by decide
  have hdescent : baseEnd_1027186 < baseStart_1027186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027203 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 1, 3]
def baseStart_1027203 : Nat := 118140960795 + 1027203 * 2 ^ 59
def prefixEnd_1027203 : Nat := 4983230072969 + 3 ^ 40 * 1027203 * 2
def baseEnd_1027203 : Nat := 351632579160299864825657

theorem tailTrace_1027203 : CollatzResearch.WordTrace tailWord_1027203 prefixEnd_1027203 351632579160299864825657 := by
  unfold tailWord_1027203
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465171297626438150630263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24976780865084292100420175 37465171297626438150630263)
  ·
    refine ⟨56197756946439657225945395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37465171297626438150630263 56197756946439657225945395)
    ·
      refine ⟨84296635419659485838918093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56197756946439657225945395 84296635419659485838918093)
      ·
        refine ⟨31611238282372307189594285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84296635419659485838918093 31611238282372307189594285)
        ·
          refine ⟨11854214355889615196097857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31611238282372307189594285 11854214355889615196097857)
          ·
            refine ⟨8890660766917211397073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11854214355889615196097857 8890660766917211397073393)
            ·
              refine ⟨6667995575187908547805045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890660766917211397073393 6667995575187908547805045)
              ·
                refine ⟨625124585173866426356723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6667995575187908547805045 625124585173866426356723)
                ·
                  refine ⟨937686877760799639535085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625124585173866426356723 937686877760799639535085)
                  ·
                    refine ⟨351632579160299864825657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937686877760799639535085 351632579160299864825657)
                    ·
                      rfl

theorem cell22_1027203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 3].length) (baseStart_1027203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027203 prefixEnd_1027203 := by exact prefixLift 1027203
  have htrace : WordTrace (prefixWord ++ tailWord_1027203) baseStart_1027203 baseEnd_1027203 := by
    simpa [prefixWord, tailWord_1027203, baseEnd_1027203] using wordTrace_append hprefix tailTrace_1027203
  have hstable : (prefixWord ++ tailWord_1027203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027203).length < 2 ^ (prefixWord ++ tailWord_1027203).sum := by decide
  have hdescent : baseEnd_1027203 < baseStart_1027203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027259 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_1027259 : Nat := 118140960795 + 1027259 * 2 ^ 59
def prefixEnd_1027259 : Nat := 4983230072969 + 3 ^ 40 * 1027259 * 2
def baseEnd_1027259 : Nat := 351651749104734385425485

theorem tailTrace_1027259 : CollatzResearch.WordTrace tailWord_1027259 prefixEnd_1027259 351651749104734385425485 := by
  unfold tailWord_1027259
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467213785423559714668831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24978142523615706476445887 37467213785423559714668831)
  ·
    refine ⟨56200820678135339572003247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467213785423559714668831 56200820678135339572003247)
    ·
      refine ⟨84301231017203009358004871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56200820678135339572003247 84301231017203009358004871)
      ·
        refine ⟨126451846525804514037007307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84301231017203009358004871 126451846525804514037007307)
        ·
          refine ⟨189677769788706771055510961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126451846525804514037007307 189677769788706771055510961)
          ·
            refine ⟨142258327341530078291633221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189677769788706771055510961 142258327341530078291633221)
            ·
              refine ⟨26673436376536889679681229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142258327341530078291633221 26673436376536889679681229)
              ·
                refine ⟨10002538641201333629880461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26673436376536889679681229 10002538641201333629880461)
                ·
                  refine ⟨3750951990450500111205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10002538641201333629880461 3750951990450500111205173)
                  ·
                    refine ⟨351651749104734385425485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3750951990450500111205173 351651749104734385425485)
                    ·
                      rfl

theorem cell22_1027259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_1027259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027259 prefixEnd_1027259 := by exact prefixLift 1027259
  have htrace : WordTrace (prefixWord ++ tailWord_1027259) baseStart_1027259 baseEnd_1027259 := by
    simpa [prefixWord, tailWord_1027259, baseEnd_1027259] using wordTrace_append hprefix tailTrace_1027259
  have hstable : (prefixWord ++ tailWord_1027259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027259).length < 2 ^ (prefixWord ++ tailWord_1027259).sum := by decide
  have hdescent : baseEnd_1027259 < baseStart_1027259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027263 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 1, 4]
def baseStart_1027263 : Nat := 118140960795 + 1027263 * 2 ^ 59
def prefixEnd_1027263 : Nat := 4983230072969 + 3 ^ 40 * 1027263 * 2
def baseEnd_1027263 : Nat := 351653118386479708325473

theorem tailTrace_1027263 : CollatzResearch.WordTrace tailWord_1027263 prefixEnd_1027263 351653118386479708325473 := by
  unfold tailWord_1027263
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467359677409068397814443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24978239784939378931876295 37467359677409068397814443)
  ·
    refine ⟨56201039516113602596721665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467359677409068397814443 56201039516113602596721665)
    ·
      refine ⟨42150779637085201947541249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56201039516113602596721665 42150779637085201947541249)
      ·
        refine ⟨31613084727813901460655937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42150779637085201947541249 31613084727813901460655937)
        ·
          refine ⟨23709813545860426095491953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31613084727813901460655937 23709813545860426095491953)
          ·
            refine ⟨17782360159395319571618965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23709813545860426095491953 17782360159395319571618965)
            ·
              refine ⟨833548132471655604919639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17782360159395319571618965 833548132471655604919639)
              ·
                refine ⟨1250322198707483407379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833548132471655604919639 1250322198707483407379459)
                ·
                  refine ⟨1875483298061225111069189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250322198707483407379459 1875483298061225111069189)
                  ·
                    refine ⟨351653118386479708325473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875483298061225111069189 351653118386479708325473)
                    ·
                      rfl

theorem cell22_1027263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_1027263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027263 prefixEnd_1027263 := by exact prefixLift 1027263
  have htrace : WordTrace (prefixWord ++ tailWord_1027263) baseStart_1027263 baseEnd_1027263 := by
    simpa [prefixWord, tailWord_1027263, baseEnd_1027263] using wordTrace_append hprefix tailTrace_1027263
  have hstable : (prefixWord ++ tailWord_1027263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027263).length < 2 ^ (prefixWord ++ tailWord_1027263).sum := by decide
  have hdescent : baseEnd_1027263 < baseStart_1027263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027278 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_1027278 : Nat := 118140960795 + 1027278 * 2 ^ 59
def prefixEnd_1027278 : Nat := 4983230072969 + 3 ^ 40 * 1027278 * 2
def baseEnd_1027278 : Nat := 117219417731008223066809

theorem tailTrace_1027278 : CollatzResearch.WordTrace tailWord_1027278 prefixEnd_1027278 117219417731008223066809 := by
  unfold tailWord_1027278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683488346544340744951311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24978604514903150639740325 4683488346544340744951311)
  ·
    refine ⟨7025232519816511117426967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4683488346544340744951311 7025232519816511117426967)
    ·
      refine ⟨10537848779724766676140451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025232519816511117426967 10537848779724766676140451)
      ·
        refine ⟨15806773169587150014210677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537848779724766676140451 15806773169587150014210677)
        ·
          refine ⟨1481884984648795313832251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15806773169587150014210677 1481884984648795313832251)
          ·
            refine ⟨2222827476973192970748377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481884984648795313832251 2222827476973192970748377)
            ·
              refine ⟨1667120607729894728061283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222827476973192970748377 1667120607729894728061283)
              ·
                refine ⟨2500680911594842092091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667120607729894728061283 2500680911594842092091925)
                ·
                  refine ⟨117219417731008223066809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500680911594842092091925 117219417731008223066809)
                  ·
                    rfl

theorem cell22_1027278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_1027278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027278 prefixEnd_1027278 := by exact prefixLift 1027278
  have htrace : WordTrace (prefixWord ++ tailWord_1027278) baseStart_1027278 baseEnd_1027278 := by
    simpa [prefixWord, tailWord_1027278, baseEnd_1027278] using wordTrace_append hprefix tailTrace_1027278
  have hstable : (prefixWord ++ tailWord_1027278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027278).length < 2 ^ (prefixWord ++ tailWord_1027278).sum := by decide
  have hdescent : baseEnd_1027278 < baseStart_1027278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027289 : List Nat := [1, 2, 1, 2, 3, 1, 1, 11]
def baseStart_1027289 : Nat := 118140960795 + 1027289 * 2 ^ 59
def prefixEnd_1027289 : Nat := 4983230072969 + 3 ^ 40 * 1027289 * 2
def baseEnd_1027289 : Nat := 39073557635313811908377

theorem tailTrace_1027289 : CollatzResearch.WordTrace tailWord_1027289 prefixEnd_1027289 39073557635313811908377 := by
  unfold tailWord_1027289
  simp only [CollatzResearch.WordTrace]
  refine ⟨37468307975314874838260921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24978871983543249892173947 37468307975314874838260921)
  ·
    refine ⟨28101230981486156128695691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37468307975314874838260921 28101230981486156128695691)
    ·
      refine ⟨42151846472229234193043537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28101230981486156128695691 42151846472229234193043537)
      ·
        refine ⟨31613884854171925644782653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42151846472229234193043537 31613884854171925644782653)
        ·
          refine ⟨11855206820314472116793495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31613884854171925644782653 11855206820314472116793495)
          ·
            refine ⟨17782810230471708175190243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855206820314472116793495 17782810230471708175190243)
            ·
              refine ⟨26674215345707562262785365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782810230471708175190243 26674215345707562262785365)
              ·
                refine ⟨39073557635313811908377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26674215345707562262785365 39073557635313811908377)
                ·
                  rfl

theorem cell22_1027289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 11].length) (baseStart_1027289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027289 prefixEnd_1027289 := by exact prefixLift 1027289
  have htrace : WordTrace (prefixWord ++ tailWord_1027289) baseStart_1027289 baseEnd_1027289 := by
    simpa [prefixWord, tailWord_1027289, baseEnd_1027289] using wordTrace_append hprefix tailTrace_1027289
  have hstable : (prefixWord ++ tailWord_1027289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027289).length < 2 ^ (prefixWord ++ tailWord_1027289).sum := by decide
  have hdescent : baseEnd_1027289 < baseStart_1027289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027306 : List Nat := [3, 1, 3, 1, 1, 4, 1, 8]
def baseStart_1027306 : Nat := 118140960795 + 1027306 * 2 ^ 59
def prefixEnd_1027306 : Nat := 4983230072969 + 3 ^ 40 * 1027306 * 2
def baseEnd_1027306 : Nat := 39074204240582436611149

theorem tailTrace_1027306 : CollatzResearch.WordTrace tailWord_1027306 prefixEnd_1027306 39074204240582436611149 := by
  unfold tailWord_1027306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9367232004063321685407443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24979285344168857827753181 9367232004063321685407443)
  ·
    refine ⟨14050848006094982528111165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9367232004063321685407443 14050848006094982528111165)
    ·
      refine ⟨5269068002285618448041687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14050848006094982528111165 5269068002285618448041687)
      ·
        refine ⟨7903602003428427672062531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269068002285618448041687 7903602003428427672062531)
        ·
          refine ⟨11855403005142641508093797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903602003428427672062531 11855403005142641508093797)
          ·
            refine ⟨2222888063464245282767587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11855403005142641508093797 2222888063464245282767587)
            ·
              refine ⟨3334332095196367924151381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222888063464245282767587 3334332095196367924151381)
              ·
                refine ⟨39074204240582436611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3334332095196367924151381 39074204240582436611149)
                ·
                  rfl

theorem cell22_1027306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_1027306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027306 prefixEnd_1027306 := by exact prefixLift 1027306
  have htrace : WordTrace (prefixWord ++ tailWord_1027306) baseStart_1027306 baseEnd_1027306 := by
    simpa [prefixWord, tailWord_1027306, baseEnd_1027306] using wordTrace_append hprefix tailTrace_1027306
  have hstable : (prefixWord ++ tailWord_1027306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027306).length < 2 ^ (prefixWord ++ tailWord_1027306).sum := by decide
  have hdescent : baseEnd_1027306 < baseStart_1027306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027385 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 5]
def baseStart_1027385 : Nat := 118140960795 + 1027385 * 2 ^ 59
def prefixEnd_1027385 : Nat := 4983230072969 + 3 ^ 40 * 1027385 * 2
def baseEnd_1027385 : Nat := 117231627159904018925033

theorem tailTrace_1027385 : CollatzResearch.WordTrace tailWord_1027385 prefixEnd_1027385 117231627159904018925033 := by
  unfold tailWord_1027385
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471809382967083233755609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981206255311388822503739 37471809382967083233755609)
  ·
    refine ⟨28103857037225312425316707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37471809382967083233755609 28103857037225312425316707)
    ·
      refine ⟨42155785555837968637975061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28103857037225312425316707 42155785555837968637975061)
      ·
        refine ⟨1976052447929904779905081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42155785555837968637975061 1976052447929904779905081)
        ·
          refine ⟨1482039335947428584928811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976052447929904779905081 1482039335947428584928811)
          ·
            refine ⟨2223059003921142877393217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482039335947428584928811 2223059003921142877393217)
            ·
              refine ⟨1667294252940857158044913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223059003921142877393217 1667294252940857158044913)
              ·
                refine ⟨1250470689705642868533685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667294252940857158044913 1250470689705642868533685)
                ·
                  refine ⟨117231627159904018925033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250470689705642868533685 117231627159904018925033)
                  ·
                    rfl

theorem cell22_1027385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_1027385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027385 prefixEnd_1027385 := by exact prefixLift 1027385
  have htrace : WordTrace (prefixWord ++ tailWord_1027385) baseStart_1027385 baseEnd_1027385 := by
    simpa [prefixWord, tailWord_1027385, baseEnd_1027385] using wordTrace_append hprefix tailTrace_1027385
  have hstable : (prefixWord ++ tailWord_1027385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027385).length < 2 ^ (prefixWord ++ tailWord_1027385).sum := by decide
  have hdescent : baseEnd_1027385 < baseStart_1027385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027389 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1027389 : Nat := 118140960795 + 1027389 * 2 ^ 59
def prefixEnd_1027389 : Nat := 4983230072969 + 3 ^ 40 * 1027389 * 2
def baseEnd_1027389 : Nat := 351696250761457379675087

theorem tailTrace_1027389 : CollatzResearch.WordTrace tailWord_1027389 prefixEnd_1027389 351696250761457379675087 := by
  unfold tailWord_1027389
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471955274952591916901221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981303516635061277934147 37471955274952591916901221)
  ·
    refine ⟨7025991614053610984418979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37471955274952591916901221 7025991614053610984418979)
    ·
      refine ⟨10538987421080416476628469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025991614053610984418979 10538987421080416476628469)
      ·
        refine ⟨988030070726289044683919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10538987421080416476628469 988030070726289044683919)
        ·
          refine ⟨1482045106089433567025879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988030070726289044683919 1482045106089433567025879)
          ·
            refine ⟨2223067659134150350538819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482045106089433567025879 2223067659134150350538819)
            ·
              refine ⟨3334601488701225525808229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223067659134150350538819 3334601488701225525808229)
              ·
                refine ⟨625237779131479786089043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3334601488701225525808229 625237779131479786089043)
                ·
                  refine ⟨937856668697219679133565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625237779131479786089043 937856668697219679133565)
                  ·
                    refine ⟨351696250761457379675087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937856668697219679133565 351696250761457379675087)
                    ·
                      rfl

theorem cell22_1027389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1027389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027389 prefixEnd_1027389 := by exact prefixLift 1027389
  have htrace : WordTrace (prefixWord ++ tailWord_1027389) baseStart_1027389 baseEnd_1027389 := by
    simpa [prefixWord, tailWord_1027389, baseEnd_1027389] using wordTrace_append hprefix tailTrace_1027389
  have hstable : (prefixWord ++ tailWord_1027389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027389).length < 2 ^ (prefixWord ++ tailWord_1027389).sum := by decide
  have hdescent : baseEnd_1027389 < baseStart_1027389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027413 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1027413 : Nat := 118140960795 + 1027413 * 2 ^ 59
def prefixEnd_1027413 : Nat := 4983230072969 + 3 ^ 40 * 1027413 * 2
def baseEnd_1027413 : Nat := 117234822150643105691671

theorem tailTrace_1027413 : CollatzResearch.WordTrace tailWord_1027413 prefixEnd_1027413 117234822150643105691671 := by
  unfold tailWord_1027413
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472830626865644015774893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981887084577096010516595 37472830626865644015774893)
  ·
    refine ⟨14052311485074616505915585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37472830626865644015774893 14052311485074616505915585)
    ·
      refine ⟨10539233613805962379436689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14052311485074616505915585 10539233613805962379436689)
      ·
        refine ⟨7904425210354471784577517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539233613805962379436689 7904425210354471784577517)
        ·
          refine ⟨2964159453882926919216569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7904425210354471784577517 2964159453882926919216569)
          ·
            refine ⟨2223119590412195189412427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964159453882926919216569 2223119590412195189412427)
            ·
              refine ⟨3334679385618292784118641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223119590412195189412427 3334679385618292784118641)
              ·
                refine ⟨2501009539213719588088981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334679385618292784118641 2501009539213719588088981)
                ·
                  refine ⟨117234822150643105691671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2501009539213719588088981 117234822150643105691671)
                  ·
                    rfl

theorem cell22_1027413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1027413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027413 prefixEnd_1027413 := by exact prefixLift 1027413
  have htrace : WordTrace (prefixWord ++ tailWord_1027413) baseStart_1027413 baseEnd_1027413 := by
    simpa [prefixWord, tailWord_1027413, baseEnd_1027413] using wordTrace_append hprefix tailTrace_1027413
  have hstable : (prefixWord ++ tailWord_1027413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027413).length < 2 ^ (prefixWord ++ tailWord_1027413).sum := by decide
  have hdescent : baseEnd_1027413 < baseStart_1027413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027428 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1027428 : Nat := 118140960795 + 1027428 * 2 ^ 59
def prefixEnd_1027428 : Nat := 4983230072969 + 3 ^ 40 * 1027428 * 2
def baseEnd_1027428 : Nat := 351709601258474277949967

theorem tailTrace_1027428 : CollatzResearch.WordTrace tailWord_1027428 prefixEnd_1027428 351709601258474277949967 := by
  unfold tailWord_1027428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736688860905650788785469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24982251814540867718380625 18736688860905650788785469)
  ·
    refine ⟨7026258322839619045794551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18736688860905650788785469 7026258322839619045794551)
    ·
      refine ⟨10539387484259428568691827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026258322839619045794551 10539387484259428568691827)
      ·
        refine ⟨15809081226389142853037741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10539387484259428568691827 15809081226389142853037741)
        ·
          refine ⟨5928405459895928569889153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15809081226389142853037741 5928405459895928569889153)
          ·
            refine ⟨4446304094921946427416865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928405459895928569889153 4446304094921946427416865)
            ·
              refine ⟨3334728071191459820562649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4446304094921946427416865 3334728071191459820562649)
              ·
                refine ⟨2501046053393594865421987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334728071191459820562649 2501046053393594865421987)
                ·
                  refine ⟨3751569080090392298132981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501046053393594865421987 3751569080090392298132981)
                  ·
                    refine ⟨351709601258474277949967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3751569080090392298132981 351709601258474277949967)
                    ·
                      rfl

theorem cell22_1027428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1027428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027428 prefixEnd_1027428 := by exact prefixLift 1027428
  have htrace : WordTrace (prefixWord ++ tailWord_1027428) baseStart_1027428 baseEnd_1027428 := by
    simpa [prefixWord, tailWord_1027428, baseEnd_1027428] using wordTrace_append hprefix tailTrace_1027428
  have hstable : (prefixWord ++ tailWord_1027428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027428).length < 2 ^ (prefixWord ++ tailWord_1027428).sum := by decide
  have hdescent : baseEnd_1027428 < baseStart_1027428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027518 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1027518 : Nat := 118140960795 + 1027518 * 2 ^ 59
def prefixEnd_1027518 : Nat := 4983230072969 + 3 ^ 40 * 1027518 * 2
def baseEnd_1027518 : Nat := 351740410097744043199691

theorem tailTrace_1027518 : CollatzResearch.WordTrace tailWord_1027518 prefixEnd_1027518 351740410097744043199691 := by
  unfold tailWord_1027518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4684582536435655868543401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24984440194323497965564805 4684582536435655868543401)
  ·
    refine ⟨3513436902326741901407551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4684582536435655868543401 3513436902326741901407551)
    ·
      refine ⟨5270155353490112852111327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513436902326741901407551 5270155353490112852111327)
      ·
        refine ⟨7905233030235169278166991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270155353490112852111327 7905233030235169278166991)
        ·
          refine ⟨11857849545352753917250487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905233030235169278166991 11857849545352753917250487)
          ·
            refine ⟨17786774318029130875875731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857849545352753917250487 17786774318029130875875731)
            ·
              refine ⟨26680161477043696313813597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17786774318029130875875731 26680161477043696313813597)
              ·
                refine ⟨10005060553891386117680099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26680161477043696313813597 10005060553891386117680099)
                ·
                  refine ⟨15007590830837079176520149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005060553891386117680099 15007590830837079176520149)
                  ·
                    refine ⟨351740410097744043199691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15007590830837079176520149 351740410097744043199691)
                    ·
                      rfl

theorem cell22_1027518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1027518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027518 prefixEnd_1027518 := by exact prefixLift 1027518
  have htrace : WordTrace (prefixWord ++ tailWord_1027518) baseStart_1027518 baseEnd_1027518 := by
    simpa [prefixWord, tailWord_1027518, baseEnd_1027518] using wordTrace_append hprefix tailTrace_1027518
  have hstable : (prefixWord ++ tailWord_1027518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027518).length < 2 ^ (prefixWord ++ tailWord_1027518).sum := by decide
  have hdescent : baseEnd_1027518 < baseStart_1027518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027520 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_1027520 : Nat := 118140960795 + 1027520 * 2 ^ 59
def prefixEnd_1027520 : Nat := 4983230072969 + 3 ^ 40 * 1027520 * 2
def baseEnd_1027520 : Nat := 117247031579538901549895

theorem tailTrace_1027520 : CollatzResearch.WordTrace tailWord_1027520 prefixEnd_1027520 117247031579538901549895 := by
  unfold tailWord_1027520
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738366618739000644960007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24984488824985334193280009 18738366618739000644960007)
  ·
    refine ⟨28107549928108500967440011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18738366618739000644960007 28107549928108500967440011)
    ·
      refine ⟨42161324892162751451160017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28107549928108500967440011 42161324892162751451160017)
      ·
        refine ⟨31620993669122063588370013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42161324892162751451160017 31620993669122063588370013)
        ·
          refine ⟨11857872625920773845638755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31620993669122063588370013 11857872625920773845638755)
          ·
            refine ⟨17786808938881160768458133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857872625920773845638755 17786808938881160768458133)
            ·
              refine ⟨833756669010054411021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17786808938881160768458133 833756669010054411021475)
              ·
                refine ⟨1250635003515081616532213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833756669010054411021475 1250635003515081616532213)
                ·
                  refine ⟨117247031579538901549895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250635003515081616532213 117247031579538901549895)
                  ·
                    rfl

theorem cell22_1027520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_1027520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027520 prefixEnd_1027520 := by exact prefixLift 1027520
  have htrace : WordTrace (prefixWord ++ tailWord_1027520) baseStart_1027520 baseEnd_1027520 := by
    simpa [prefixWord, tailWord_1027520, baseEnd_1027520] using wordTrace_append hprefix tailTrace_1027520
  have hstable : (prefixWord ++ tailWord_1027520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027520).length < 2 ^ (prefixWord ++ tailWord_1027520).sum := by decide
  have hdescent : baseEnd_1027520 < baseStart_1027520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027578 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1027578 : Nat := 118140960795 + 1027578 * 2 ^ 59
def prefixEnd_1027578 : Nat := 4983230072969 + 3 ^ 40 * 1027578 * 2
def baseEnd_1027578 : Nat := 351760949323923886699507

theorem tailTrace_1027578 : CollatzResearch.WordTrace tailWord_1027578 prefixEnd_1027578 351760949323923886699507 := by
  unfold tailWord_1027578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369712167816969298882847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24985899114178584797020925 9369712167816969298882847)
  ·
    refine ⟨14054568251725453948324271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9369712167816969298882847 14054568251725453948324271)
    ·
      refine ⟨21081852377588180922486407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14054568251725453948324271 21081852377588180922486407)
      ·
        refine ⟨31622778566382271383729611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21081852377588180922486407 31622778566382271383729611)
        ·
          refine ⟨47434167849573407075594417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622778566382271383729611 47434167849573407075594417)
          ·
            refine ⟨35575625887180055306695813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47434167849573407075594417 35575625887180055306695813)
            ·
              refine ⟨6670429853846260370005465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35575625887180055306695813 6670429853846260370005465)
              ·
                refine ⟨5002822390384695277504099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6670429853846260370005465 5002822390384695277504099)
                ·
                  refine ⟨7504233585577042916256149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002822390384695277504099 7504233585577042916256149)
                  ·
                    refine ⟨351760949323923886699507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7504233585577042916256149 351760949323923886699507)
                    ·
                      rfl

theorem cell22_1027578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1027578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027578 prefixEnd_1027578 := by exact prefixLift 1027578
  have htrace : WordTrace (prefixWord ++ tailWord_1027578) baseStart_1027578 baseEnd_1027578 := by
    simpa [prefixWord, tailWord_1027578, baseEnd_1027578] using wordTrace_append hprefix tailTrace_1027578
  have hstable : (prefixWord ++ tailWord_1027578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027578).length < 2 ^ (prefixWord ++ tailWord_1027578).sum := by decide
  have hdescent : baseEnd_1027578 < baseStart_1027578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027595 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_1027595 : Nat := 118140960795 + 1027595 * 2 ^ 59
def prefixEnd_1027595 : Nat := 4983230072969 + 3 ^ 40 * 1027595 * 2
def baseEnd_1027595 : Nat := 351766768771341509024455

theorem tailTrace_1027595 : CollatzResearch.WordTrace tailWord_1027595 prefixEnd_1027595 351766768771341509024455 := by
  unfold tailWord_1027595
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479468712206289098900239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24986312474804192732600159 37479468712206289098900239)
  ·
    refine ⟨56219203068309433648350359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37479468712206289098900239 56219203068309433648350359)
    ·
      refine ⟨84328804602464150472525539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56219203068309433648350359 84328804602464150472525539)
      ·
        refine ⟨126493206903696225708788309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84328804602464150472525539 126493206903696225708788309)
        ·
          refine ⟨1482342268402690145024863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 126493206903696225708788309 1482342268402690145024863)
          ·
            refine ⟨2223513402604035217537295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482342268402690145024863 2223513402604035217537295)
            ·
              refine ⟨3335270103906052826305943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223513402604035217537295 3335270103906052826305943)
              ·
                refine ⟨5002905155859079239458915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335270103906052826305943 5002905155859079239458915)
                ·
                  refine ⟨7504357733788618859188373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002905155859079239458915 7504357733788618859188373)
                  ·
                    refine ⟨351766768771341509024455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7504357733788618859188373 351766768771341509024455)
                    ·
                      rfl

theorem cell22_1027595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_1027595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027595 prefixEnd_1027595 := by exact prefixLift 1027595
  have htrace : WordTrace (prefixWord ++ tailWord_1027595) baseStart_1027595 baseEnd_1027595 := by
    simpa [prefixWord, tailWord_1027595, baseEnd_1027595] using wordTrace_append hprefix tailTrace_1027595
  have hstable : (prefixWord ++ tailWord_1027595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027595).length < 2 ^ (prefixWord ++ tailWord_1027595).sum := by decide
  have hdescent : baseEnd_1027595 < baseStart_1027595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027644 : List Nat := [2, 2, 2, 2, 5, 1, 2, 6]
def baseStart_1027644 : Nat := 118140960795 + 1027644 * 2 ^ 59
def prefixEnd_1027644 : Nat := 4983230072969 + 3 ^ 40 * 1027644 * 2
def baseEnd_1027644 : Nat := 39087060274746857172145

theorem tailTrace_1027644 : CollatzResearch.WordTrace tailWord_1027644 prefixEnd_1027644 39087060274746857172145 := by
  unfold tailWord_1027644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740627944514385233716993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24987503926019180311622657 18740627944514385233716993)
  ·
    refine ⟨14055470958385788925287745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18740627944514385233716993 14055470958385788925287745)
    ·
      refine ⟨10541603218789341693965809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14055470958385788925287745 10541603218789341693965809)
      ·
        refine ⟨7906202414092006270474357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10541603218789341693965809 7906202414092006270474357)
        ·
          refine ⟨741206476321125587856971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7906202414092006270474357 741206476321125587856971)
          ·
            refine ⟨1111809714481688381785457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741206476321125587856971 1111809714481688381785457)
            ·
              refine ⟨833857285861266286339093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111809714481688381785457 833857285861266286339093)
              ·
                refine ⟨39087060274746857172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 833857285861266286339093 39087060274746857172145)
                ·
                  rfl

theorem cell22_1027644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_1027644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027644 prefixEnd_1027644 := by exact prefixLift 1027644
  have htrace : WordTrace (prefixWord ++ tailWord_1027644) baseStart_1027644 baseEnd_1027644 := by
    simpa [prefixWord, tailWord_1027644, baseEnd_1027644] using wordTrace_append hprefix tailTrace_1027644
  have hstable : (prefixWord ++ tailWord_1027644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027644).length < 2 ^ (prefixWord ++ tailWord_1027644).sum := by decide
  have hdescent : baseEnd_1027644 < baseStart_1027644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027717 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1027717 : Nat := 118140960795 + 1027717 * 2 ^ 59
def prefixEnd_1027717 : Nat := 4983230072969 + 3 ^ 40 * 1027717 * 2
def baseEnd_1027717 : Nat := 117269510621524619158027

theorem tailTrace_1027717 : CollatzResearch.WordTrace tailWord_1027717 prefixEnd_1027717 117269510621524619158027 := by
  unfold tailWord_1027717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483918417764303934841405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24989278945176202623227603 37483918417764303934841405)
  ·
    refine ⟨14056469406661613975565527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37483918417764303934841405 14056469406661613975565527)
    ·
      refine ⟨21084704109992420963348291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056469406661613975565527 21084704109992420963348291)
      ·
        refine ⟨31627056164988631445022437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21084704109992420963348291 31627056164988631445022437)
        ·
          refine ⟨5930073030935368395941707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31627056164988631445022437 5930073030935368395941707)
          ·
            refine ⟨8895109546403052593912561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930073030935368395941707 8895109546403052593912561)
            ·
              refine ⟨6671332159802289445434421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895109546403052593912561 6671332159802289445434421)
              ·
                refine ⟨625437389981464635509477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6671332159802289445434421 625437389981464635509477)
                ·
                  refine ⟨117269510621524619158027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625437389981464635509477 117269510621524619158027)
                  ·
                    rfl

theorem cell22_1027717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1027717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027717 prefixEnd_1027717 := by exact prefixLift 1027717
  have htrace : WordTrace (prefixWord ++ tailWord_1027717) baseStart_1027717 baseEnd_1027717 := by
    simpa [prefixWord, tailWord_1027717, baseEnd_1027717] using wordTrace_append hprefix tailTrace_1027717
  have hstable : (prefixWord ++ tailWord_1027717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027717).length < 2 ^ (prefixWord ++ tailWord_1027717).sum := by decide
  have hdescent : baseEnd_1027717 < baseStart_1027717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027719 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 1, 4]
def baseStart_1027719 : Nat := 118140960795 + 1027719 * 2 ^ 59
def prefixEnd_1027719 : Nat := 4983230072969 + 3 ^ 40 * 1027719 * 2
def baseEnd_1027719 : Nat := 351809216505446518924075

theorem tailTrace_1027719 : CollatzResearch.WordTrace tailWord_1027719 prefixEnd_1027719 351809216505446518924075 := by
  unfold tailWord_1027719
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483991363757058276414211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24989327575838038850942807 37483991363757058276414211)
  ·
    refine ⟨56225987045635587414621317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37483991363757058276414211 56225987045635587414621317)
    ·
      refine ⟨10542372571056672640241497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56225987045635587414621317 10542372571056672640241497)
      ·
        refine ⟨7906779428292504480181123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10542372571056672640241497 7906779428292504480181123)
        ·
          refine ⟨11860169142438756720271685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906779428292504480181123 11860169142438756720271685)
          ·
            refine ⟨2223781714207266885050941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11860169142438756720271685 2223781714207266885050941)
            ·
              refine ⟨833918142827725081894103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223781714207266885050941 833918142827725081894103)
              ·
                refine ⟨1250877214241587622841155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833918142827725081894103 1250877214241587622841155)
                ·
                  refine ⟨1876315821362381434261733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250877214241587622841155 1876315821362381434261733)
                  ·
                    refine ⟨351809216505446518924075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876315821362381434261733 351809216505446518924075)
                    ·
                      rfl

theorem cell22_1027719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_1027719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027719 prefixEnd_1027719 := by exact prefixLift 1027719
  have htrace : WordTrace (prefixWord ++ tailWord_1027719) baseStart_1027719 baseEnd_1027719 := by
    simpa [prefixWord, tailWord_1027719, baseEnd_1027719] using wordTrace_append hprefix tailTrace_1027719
  have hstable : (prefixWord ++ tailWord_1027719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027719).length < 2 ^ (prefixWord ++ tailWord_1027719).sum := by decide
  have hdescent : baseEnd_1027719 < baseStart_1027719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027794 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1027794 : Nat := 118140960795 + 1027794 * 2 ^ 59
def prefixEnd_1027794 : Nat := 4983230072969 + 3 ^ 40 * 1027794 * 2
def baseEnd_1027794 : Nat := 351834890538171323298845

theorem tailTrace_1027794 : CollatzResearch.WordTrace tailWord_1027794 prefixEnd_1027794 351834890538171323298845 := by
  unfold tailWord_1027794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371681709621336521348609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24991151225656897390262957 9371681709621336521348609)
  ·
    refine ⟨7028761282216002391011457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9371681709621336521348609 7028761282216002391011457)
    ·
      refine ⟨5271570961662001793258593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028761282216002391011457 5271570961662001793258593)
      ·
        refine ⟨3953678221246501344943945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5271570961662001793258593 3953678221246501344943945)
        ·
          refine ⟨2965258665934876008707959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953678221246501344943945 2965258665934876008707959)
          ·
            refine ⟨4447887998902314013061939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965258665934876008707959 4447887998902314013061939)
            ·
              refine ⟨6671831998353471019592909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447887998902314013061939 6671831998353471019592909)
              ·
                refine ⟨2501936999382551632347341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6671831998353471019592909 2501936999382551632347341)
                ·
                  refine ⟨938226374768456862130253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2501936999382551632347341 938226374768456862130253)
                  ·
                    refine ⟨351834890538171323298845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938226374768456862130253 351834890538171323298845)
                    ·
                      rfl

theorem cell22_1027794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1027794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027794 prefixEnd_1027794 := by exact prefixLift 1027794
  have htrace : WordTrace (prefixWord ++ tailWord_1027794) baseStart_1027794 baseEnd_1027794 := by
    simpa [prefixWord, tailWord_1027794, baseEnd_1027794] using wordTrace_append hprefix tailTrace_1027794
  have hstable : (prefixWord ++ tailWord_1027794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027794).length < 2 ^ (prefixWord ++ tailWord_1027794).sum := by decide
  have hdescent : baseEnd_1027794 < baseStart_1027794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027852 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1027852 : Nat := 118140960795 + 1027852 * 2 ^ 59
def prefixEnd_1027852 : Nat := 4983230072969 + 3 ^ 40 * 1027852 * 2
def baseEnd_1027852 : Nat := 117284915041159501782889

theorem tailTrace_1027852 : CollatzResearch.WordTrace tailWord_1027852 prefixEnd_1027852 117284915041159501782889 := by
  unfold tailWord_1027852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744421136137610995502905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24992561514850147994003873 18744421136137610995502905)
  ·
    refine ⟨14058315852103208246627179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18744421136137610995502905 14058315852103208246627179)
    ·
      refine ⟨21087473778154812369940769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058315852103208246627179 21087473778154812369940769)
      ·
        refine ⟨15815605333616109277455577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21087473778154812369940769 15815605333616109277455577)
        ·
          refine ⟨11861704000212081958091683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15815605333616109277455577 11861704000212081958091683)
          ·
            refine ⟨17792556000318122937137525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861704000212081958091683 17792556000318122937137525)
            ·
              refine ⟨1668052125029824025356643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17792556000318122937137525 1668052125029824025356643)
              ·
                refine ⟨2502078187544736038034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668052125029824025356643 2502078187544736038034965)
                ·
                  refine ⟨117284915041159501782889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2502078187544736038034965 117284915041159501782889)
                  ·
                    rfl

theorem cell22_1027852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1027852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027852 prefixEnd_1027852 := by exact prefixLift 1027852
  have htrace : WordTrace (prefixWord ++ tailWord_1027852) baseStart_1027852 baseEnd_1027852 := by
    simpa [prefixWord, tailWord_1027852, baseEnd_1027852] using wordTrace_append hprefix tailTrace_1027852
  have hstable : (prefixWord ++ tailWord_1027852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027852).length < 2 ^ (prefixWord ++ tailWord_1027852).sum := by decide
  have hdescent : baseEnd_1027852 < baseStart_1027852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027858 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1027858 : Nat := 118140960795 + 1027858 * 2 ^ 59
def prefixEnd_1027858 : Nat := 4983230072969 + 3 ^ 40 * 1027858 * 2
def baseEnd_1027858 : Nat := 117285599682032163232883

theorem tailTrace_1027858 : CollatzResearch.WordTrace tailWord_1027858 prefixEnd_1027858 117285599682032163232883 := by
  unfold tailWord_1027858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372265277563371253931057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24992707406835656677149485 9372265277563371253931057)
  ·
    refine ⟨7029198958172528440448293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9372265277563371253931057 7029198958172528440448293)
    ·
      refine ⟨1317974804657349082584055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7029198958172528440448293 1317974804657349082584055)
      ·
        refine ⟨1976962206986023623876083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317974804657349082584055 1976962206986023623876083)
        ·
          refine ⟨2965443310479035435814125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976962206986023623876083 2965443310479035435814125)
          ·
            refine ⟨1112041241429638288430297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2965443310479035435814125 1112041241429638288430297)
            ·
              refine ⟨834030931072228716322723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112041241429638288430297 834030931072228716322723)
              ·
                refine ⟨1251046396608343074484085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834030931072228716322723 1251046396608343074484085)
                ·
                  refine ⟨117285599682032163232883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251046396608343074484085 117285599682032163232883)
                  ·
                    rfl

theorem cell22_1027858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1027858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027858 prefixEnd_1027858 := by exact prefixLift 1027858
  have htrace : WordTrace (prefixWord ++ tailWord_1027858) baseStart_1027858 baseEnd_1027858 := by
    simpa [prefixWord, tailWord_1027858, baseEnd_1027858] using wordTrace_append hprefix tailTrace_1027858
  have hstable : (prefixWord ++ tailWord_1027858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027858).length < 2 ^ (prefixWord ++ tailWord_1027858).sum := by decide
  have hdescent : baseEnd_1027858 < baseStart_1027858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027897 : List Nat := [1, 2, 1, 7, 11]
def baseStart_1027897 : Nat := 118140960795 + 1027897 * 2 ^ 59
def prefixEnd_1027897 : Nat := 4983230072969 + 3 ^ 40 * 1027897 * 2
def baseEnd_1027897 : Nat := 1448025306761783489603

theorem tailTrace_1027897 : CollatzResearch.WordTrace tailWord_1027897 prefixEnd_1027897 1448025306761783489603 := by
  unfold tailWord_1027897
  simp only [CollatzResearch.WordTrace]
  refine ⟨37490483557112194676393945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24993655704741463117595963 37490483557112194676393945)
  ·
    refine ⟨28117862667834146007295459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37490483557112194676393945 28117862667834146007295459)
    ·
      refine ⟨42176794001751219010943189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28117862667834146007295459 42176794001751219010943189)
      ·
        refine ⟨988518609416044195568981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42176794001751219010943189 988518609416044195568981)
        ·
          refine ⟨1448025306761783489603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 988518609416044195568981 1448025306761783489603)
          ·
            rfl

theorem cell22_1027897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 11].length) (baseStart_1027897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027897 prefixEnd_1027897 := by exact prefixLift 1027897
  have htrace : WordTrace (prefixWord ++ tailWord_1027897) baseStart_1027897 baseEnd_1027897 := by
    simpa [prefixWord, tailWord_1027897, baseEnd_1027897] using wordTrace_append hprefix tailTrace_1027897
  have hstable : (prefixWord ++ tailWord_1027897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027897).length < 2 ^ (prefixWord ++ tailWord_1027897).sum := by decide
  have hdescent : baseEnd_1027897 < baseStart_1027897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027901 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1027901 : Nat := 118140960795 + 1027901 * 2 ^ 59
def prefixEnd_1027901 : Nat := 4983230072969 + 3 ^ 40 * 1027901 * 2
def baseEnd_1027901 : Nat := 351871518824858710873517

theorem tailTrace_1027901 : CollatzResearch.WordTrace tailWord_1027901 prefixEnd_1027901 351871518824858710873517 := by
  unfold tailWord_1027901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37490629449097703359539557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24993752966065135573026371 37490629449097703359539557)
  ·
    refine ⟨7029493021705819379913667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37490629449097703359539557 7029493021705819379913667)
    ·
      refine ⟨10544239532558729069870501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7029493021705819379913667 10544239532558729069870501)
      ·
        refine ⟨1977044912354761700600719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10544239532558729069870501 1977044912354761700600719)
        ·
          refine ⟨2965567368532142550901079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977044912354761700600719 2965567368532142550901079)
          ·
            refine ⟨4448351052798213826351619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965567368532142550901079 4448351052798213826351619)
            ·
              refine ⟨6672526579197320739527429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448351052798213826351619 6672526579197320739527429)
              ·
                refine ⟨1251098733599497638661393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6672526579197320739527429 1251098733599497638661393)
                ·
                  refine ⟨938324050199623228996045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1251098733599497638661393 938324050199623228996045)
                  ·
                    refine ⟨351871518824858710873517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938324050199623228996045 351871518824858710873517)
                    ·
                      rfl

theorem cell22_1027901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1027901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027901 prefixEnd_1027901 := by exact prefixLift 1027901
  have htrace : WordTrace (prefixWord ++ tailWord_1027901) baseStart_1027901 baseEnd_1027901 := by
    simpa [prefixWord, tailWord_1027901, baseEnd_1027901] using wordTrace_append hprefix tailTrace_1027901
  have hstable : (prefixWord ++ tailWord_1027901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027901).length < 2 ^ (prefixWord ++ tailWord_1027901).sum := by decide
  have hdescent : baseEnd_1027901 < baseStart_1027901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027903 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 4]
def baseStart_1027903 : Nat := 118140960795 + 1027903 * 2 ^ 59
def prefixEnd_1027903 : Nat := 4983230072969 + 3 ^ 40 * 1027903 * 2
def baseEnd_1027903 : Nat := 117290734488577124107837

theorem tailTrace_1027903 : CollatzResearch.WordTrace tailWord_1027903 prefixEnd_1027903 117290734488577124107837 := by
  unfold tailWord_1027903
  simp only [CollatzResearch.WordTrace]
  refine ⟨37490702395090457701112363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24993801596726971800741575 37490702395090457701112363)
  ·
    refine ⟨56236053592635686551668545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37490702395090457701112363 56236053592635686551668545)
    ·
      refine ⟨42177040194476764913751409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56236053592635686551668545 42177040194476764913751409)
      ·
        refine ⟨31632780145857573685313557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42177040194476764913751409 31632780145857573685313557)
        ·
          refine ⟨1482786569337073766499073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31632780145857573685313557 1482786569337073766499073)
          ·
            refine ⟨1112089927002805324874305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482786569337073766499073 1112089927002805324874305)
            ·
              refine ⟨834067445252103993655729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112089927002805324874305 834067445252103993655729)
              ·
                refine ⟨625550583939077995241797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834067445252103993655729 625550583939077995241797)
                ·
                  refine ⟨117290734488577124107837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625550583939077995241797 117290734488577124107837)
                  ·
                    rfl

theorem cell22_1027903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 4].length) (baseStart_1027903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027903 prefixEnd_1027903 := by exact prefixLift 1027903
  have htrace : WordTrace (prefixWord ++ tailWord_1027903) baseStart_1027903 baseEnd_1027903 := by
    simpa [prefixWord, tailWord_1027903, baseEnd_1027903] using wordTrace_append hprefix tailTrace_1027903
  have hstable : (prefixWord ++ tailWord_1027903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027903).length < 2 ^ (prefixWord ++ tailWord_1027903).sum := by decide
  have hdescent : baseEnd_1027903 < baseStart_1027903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027929 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_1027929 : Nat := 118140960795 + 1027929 * 2 ^ 59
def prefixEnd_1027929 : Nat := 4983230072969 + 3 ^ 40 * 1027929 * 2
def baseEnd_1027929 : Nat := 351881103797075971173431

theorem tailTrace_1027929 : CollatzResearch.WordTrace tailWord_1027929 prefixEnd_1027929 351881103797075971173431 := by
  unfold tailWord_1027929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491650692996264141558841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24994433795330842761039227 37491650692996264141558841)
  ·
    refine ⟨28118738019747198106169131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37491650692996264141558841 28118738019747198106169131)
    ·
      refine ⟨42178107029620797159253697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28118738019747198106169131 42178107029620797159253697)
      ·
        refine ⟨31633580272215597869440273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42178107029620797159253697 31633580272215597869440273)
        ·
          refine ⟨23725185204161698402080205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31633580272215597869440273 23725185204161698402080205)
          ·
            refine ⟨8896944451560636900780077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23725185204161698402080205 8896944451560636900780077)
            ·
              refine ⟨3336354169335238837792529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8896944451560636900780077 3336354169335238837792529)
              ·
                refine ⟨2502265627001429128344397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336354169335238837792529 2502265627001429128344397)
                ·
                  refine ⟨938349610125535923129149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2502265627001429128344397 938349610125535923129149)
                  ·
                    refine ⟨351881103797075971173431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938349610125535923129149 351881103797075971173431)
                    ·
                      rfl

theorem cell22_1027929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_1027929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1027929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1027929 prefixEnd_1027929 := by exact prefixLift 1027929
  have htrace : WordTrace (prefixWord ++ tailWord_1027929) baseStart_1027929 baseEnd_1027929 := by
    simpa [prefixWord, tailWord_1027929, baseEnd_1027929] using wordTrace_append hprefix tailTrace_1027929
  have hstable : (prefixWord ++ tailWord_1027929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027929).length < 2 ^ (prefixWord ++ tailWord_1027929).sum := by decide
  have hdescent : baseEnd_1027929 < baseStart_1027929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028014 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1028014 : Nat := 118140960795 + 1028014 * 2 ^ 59
def prefixEnd_1028014 : Nat := 4983230072969 + 3 ^ 40 * 1028014 * 2
def baseEnd_1028014 : Nat := 351910201034164082798171

theorem tailTrace_1028014 : CollatzResearch.WordTrace tailWord_1028014 prefixEnd_1028014 351910201034164082798171 := by
  unfold tailWord_1028014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686843862211040457300387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24996500598458882438935397 4686843862211040457300387)
  ·
    refine ⟨7030265793316560685950581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686843862211040457300387 7030265793316560685950581)
    ·
      refine ⟨659087418123427564307867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7030265793316560685950581 659087418123427564307867)
      ·
        refine ⟨988631127185141346461801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659087418123427564307867 988631127185141346461801)
        ·
          refine ⟨741473345388856009846351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988631127185141346461801 741473345388856009846351)
          ·
            refine ⟨1112210018083284014769527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741473345388856009846351 1112210018083284014769527)
            ·
              refine ⟨1668315027124926022154291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112210018083284014769527 1668315027124926022154291)
              ·
                refine ⟨2502472540687389033231437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668315027124926022154291 2502472540687389033231437)
                ·
                  refine ⟨938427202757770887461789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2502472540687389033231437 938427202757770887461789)
                  ·
                    refine ⟨351910201034164082798171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938427202757770887461789 351910201034164082798171)
                    ·
                      rfl

theorem cell22_1028014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1028014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028014 prefixEnd_1028014 := by exact prefixLift 1028014
  have htrace : WordTrace (prefixWord ++ tailWord_1028014) baseStart_1028014 baseEnd_1028014 := by
    simpa [prefixWord, tailWord_1028014, baseEnd_1028014] using wordTrace_append hprefix tailTrace_1028014
  have hstable : (prefixWord ++ tailWord_1028014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028014).length < 2 ^ (prefixWord ++ tailWord_1028014).sum := by decide
  have hdescent : baseEnd_1028014 < baseStart_1028014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028019 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 4, 3]
def baseStart_1028019 : Nat := 118140960795 + 1028019 * 2 ^ 59
def prefixEnd_1028019 : Nat := 4983230072969 + 3 ^ 40 * 1028019 * 2
def baseEnd_1028019 : Nat := 351911912636345736423155

theorem tailTrace_1028019 : CollatzResearch.WordTrace tailWord_1028019 prefixEnd_1028019 351911912636345736423155 := by
  unfold tailWord_1028019
  simp only [CollatzResearch.WordTrace]
  refine ⟨37494933262670209512335111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24996622175113473008223407 37494933262670209512335111)
  ·
    refine ⟨56242399894005314268502667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37494933262670209512335111 56242399894005314268502667)
    ·
      refine ⟨84363599841007971402754001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56242399894005314268502667 84363599841007971402754001)
      ·
        refine ⟨63272699880755978552065501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84363599841007971402754001 63272699880755978552065501)
        ·
          refine ⟨23727262455283491957024563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63272699880755978552065501 23727262455283491957024563)
          ·
            refine ⟨35590893682925237935536845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23727262455283491957024563 35590893682925237935536845)
            ·
              refine ⟨13346585131096964225826317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35590893682925237935536845 13346585131096964225826317)
              ·
                refine ⟨5004969424161361584684869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13346585131096964225826317 5004969424161361584684869)
                ·
                  refine ⟨938431767030255297128413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5004969424161361584684869 938431767030255297128413)
                  ·
                    refine ⟨351911912636345736423155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938431767030255297128413 351911912636345736423155)
                    ·
                      rfl

theorem cell22_1028019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].length) (baseStart_1028019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028019 prefixEnd_1028019 := by exact prefixLift 1028019
  have htrace : WordTrace (prefixWord ++ tailWord_1028019) baseStart_1028019 baseEnd_1028019 := by
    simpa [prefixWord, tailWord_1028019, baseEnd_1028019] using wordTrace_append hprefix tailTrace_1028019
  have hstable : (prefixWord ++ tailWord_1028019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028019).length < 2 ^ (prefixWord ++ tailWord_1028019).sum := by decide
  have hdescent : baseEnd_1028019 < baseStart_1028019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028021 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 6]
def baseStart_1028021 : Nat := 118140960795 + 1028021 * 2 ^ 59
def prefixEnd_1028021 : Nat := 4983230072969 + 3 ^ 40 * 1028021 * 2
def baseEnd_1028021 : Nat := 117304199092406132624383

theorem tailTrace_1028021 : CollatzResearch.WordTrace tailWord_1028021 prefixEnd_1028021 117304199092406132624383 := by
  unfold tailWord_1028021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37495006208662963853907917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24996670805775309235938611 37495006208662963853907917)
  ·
    refine ⟨14060627328248611445215469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37495006208662963853907917 14060627328248611445215469)
    ·
      refine ⟨5272735248093229291955801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14060627328248611445215469 5272735248093229291955801)
      ·
        refine ⟨3954551436069921968966851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272735248093229291955801 3954551436069921968966851)
        ·
          refine ⟨5931827154104882953450277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954551436069921968966851 5931827154104882953450277)
          ·
            refine ⟨1112217591394665553771927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5931827154104882953450277 1112217591394665553771927)
            ·
              refine ⟨1668326387091998330657891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112217591394665553771927 1668326387091998330657891)
              ·
                refine ⟨2502489580637997495986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668326387091998330657891 2502489580637997495986837)
                ·
                  refine ⟨117304199092406132624383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2502489580637997495986837 117304199092406132624383)
                  ·
                    rfl

theorem cell22_1028021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_1028021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028021 prefixEnd_1028021 := by exact prefixLift 1028021
  have htrace : WordTrace (prefixWord ++ tailWord_1028021) baseStart_1028021 baseEnd_1028021 := by
    simpa [prefixWord, tailWord_1028021, baseEnd_1028021] using wordTrace_append hprefix tailTrace_1028021
  have hstable : (prefixWord ++ tailWord_1028021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028021).length < 2 ^ (prefixWord ++ tailWord_1028021).sum := by decide
  have hdescent : baseEnd_1028021 < baseStart_1028021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028066 : List Nat := [3, 3, 3, 1, 2, 10]
def baseStart_1028066 : Nat := 118140960795 + 1028066 * 2 ^ 59
def prefixEnd_1028066 : Nat := 4983230072969 + 3 ^ 40 * 1028066 * 2
def baseEnd_1028066 : Nat := 4344790144405596055531

theorem tailTrace_1028066 : CollatzResearch.WordTrace tailWord_1028066 prefixEnd_1028066 4344790144405596055531 := by
  unfold tailWord_1028066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374161873374984134824013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24997764995666624359530701 9374161873374984134824013)
  ·
    refine ⟨3515310702515619050559005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9374161873374984134824013 3515310702515619050559005)
    ·
      refine ⟨1318241513443357143959627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3515310702515619050559005 1318241513443357143959627)
      ·
        refine ⟨1977362270165035715939441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318241513443357143959627 1977362270165035715939441)
        ·
          refine ⟨1483021702623776786954581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977362270165035715939441 1483021702623776786954581)
          ·
            refine ⟨4344790144405596055531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1483021702623776786954581 4344790144405596055531)
            ·
              rfl

theorem cell22_1028066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 10].length) (baseStart_1028066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028066 prefixEnd_1028066 := by exact prefixLift 1028066
  have htrace : WordTrace (prefixWord ++ tailWord_1028066) baseStart_1028066 baseEnd_1028066 := by
    simpa [prefixWord, tailWord_1028066, baseEnd_1028066] using wordTrace_append hprefix tailTrace_1028066
  have hstable : (prefixWord ++ tailWord_1028066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028066).length < 2 ^ (prefixWord ++ tailWord_1028066).sum := by decide
  have hdescent : baseEnd_1028066 < baseStart_1028066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028102 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1028102 : Nat := 118140960795 + 1028102 * 2 ^ 59
def prefixEnd_1028102 : Nat := 4983230072969 + 3 ^ 40 * 1028102 * 2
def baseEnd_1028102 : Nat := 351940325232561186597901

theorem tailTrace_1028102 : CollatzResearch.WordTrace tailWord_1028102 prefixEnd_1028102 351940325232561186597901 := by
  unfold tailWord_1028102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171811266292797333987705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24998640347579676458404373 1171811266292797333987705)
  ·
    refine ⟨878858449719598000490779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1171811266292797333987705 878858449719598000490779)
    ·
      refine ⟨1318287674579397000736169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878858449719598000490779 1318287674579397000736169)
      ·
        refine ⟨988715755934547750552127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318287674579397000736169 988715755934547750552127)
        ·
          refine ⟨1483073633901821625828191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988715755934547750552127 1483073633901821625828191)
          ·
            refine ⟨2224610450852732438742287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483073633901821625828191 2224610450852732438742287)
            ·
              refine ⟨3336915676279098658113431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224610450852732438742287 3336915676279098658113431)
              ·
                refine ⟨5005373514418647987170147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336915676279098658113431 5005373514418647987170147)
                ·
                  refine ⟨7508060271627971980755221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005373514418647987170147 7508060271627971980755221)
                  ·
                    refine ⟨351940325232561186597901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7508060271627971980755221 351940325232561186597901)
                    ·
                      rfl

theorem cell22_1028102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1028102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028102 prefixEnd_1028102 := by exact prefixLift 1028102
  have htrace : WordTrace (prefixWord ++ tailWord_1028102) baseStart_1028102 baseEnd_1028102 := by
    simpa [prefixWord, tailWord_1028102, baseEnd_1028102] using wordTrace_append hprefix tailTrace_1028102
  have hstable : (prefixWord ++ tailWord_1028102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028102).length < 2 ^ (prefixWord ++ tailWord_1028102).sum := by decide
  have hdescent : baseEnd_1028102 < baseStart_1028102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028169 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1028169 : Nat := 118140960795 + 1028169 * 2 ^ 59
def prefixEnd_1028169 : Nat := 4983230072969 + 3 ^ 40 * 1028169 * 2
def baseEnd_1028169 : Nat := 351963260701795345172695

theorem tailTrace_1028169 : CollatzResearch.WordTrace tailWord_1028169 prefixEnd_1028169 351963260701795345172695 := by
  unfold tailWord_1028169
  simp only [CollatzResearch.WordTrace]
  refine ⟨37500404212126785130295561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25000269474751190086863707 37500404212126785130295561)
  ·
    refine ⟨28125303159095088847721671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37500404212126785130295561 28125303159095088847721671)
    ·
      refine ⟨42187954738642633271582507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28125303159095088847721671 42187954738642633271582507)
      ·
        refine ⟨63281932107963949907373761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42187954738642633271582507 63281932107963949907373761)
        ·
          refine ⟨47461449080972962430530321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63281932107963949907373761 47461449080972962430530321)
          ·
            refine ⟨35596086810729721822897741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47461449080972962430530321 35596086810729721822897741)
            ·
              refine ⟨13348532554023645683586653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35596086810729721822897741 13348532554023645683586653)
              ·
                refine ⟨5005699707758867131344995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13348532554023645683586653 5005699707758867131344995)
                ·
                  refine ⟨7508549561638300697017493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005699707758867131344995 7508549561638300697017493)
                  ·
                    refine ⟨351963260701795345172695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7508549561638300697017493 351963260701795345172695)
                    ·
                      rfl

theorem cell22_1028169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1028169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028169 prefixEnd_1028169 := by exact prefixLift 1028169
  have htrace : WordTrace (prefixWord ++ tailWord_1028169) baseStart_1028169 baseEnd_1028169 := by
    simpa [prefixWord, tailWord_1028169, baseEnd_1028169] using wordTrace_append hprefix tailTrace_1028169
  have hstable : (prefixWord ++ tailWord_1028169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028169).length < 2 ^ (prefixWord ++ tailWord_1028169).sum := by decide
  have hdescent : baseEnd_1028169 < baseStart_1028169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028184 : List Nat := [2, 1, 2, 2, 1, 4, 10]
def baseStart_1028184 : Nat := 118140960795 + 1028184 * 2 ^ 59
def prefixEnd_1028184 : Nat := 4983230072969 + 3 ^ 40 * 1028184 * 2
def baseEnd_1028184 : Nat := 13035866500308900223987

theorem tailTrace_1028184 : CollatzResearch.WordTrace tailWord_1028184 prefixEnd_1028184 13035866500308900223987 := by
  unfold tailWord_1028184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18750475653536221346045803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25000634204714961794727737 18750475653536221346045803)
  ·
    refine ⟨28125713480304332019068705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18750475653536221346045803 28125713480304332019068705)
    ·
      refine ⟨21094285110228249014301529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28125713480304332019068705 21094285110228249014301529)
      ·
        refine ⟨15820713832671186760726147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21094285110228249014301529 15820713832671186760726147)
        ·
          refine ⟨23731070749006780141089221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820713832671186760726147 23731070749006780141089221)
          ·
            refine ⟨4449575765438771276454229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23731070749006780141089221 4449575765438771276454229)
            ·
              refine ⟨13035866500308900223987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4449575765438771276454229 13035866500308900223987)
              ·
                rfl

theorem cell22_1028184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 10].length) (baseStart_1028184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028184 prefixEnd_1028184 := by exact prefixLift 1028184
  have htrace : WordTrace (prefixWord ++ tailWord_1028184) baseStart_1028184 baseEnd_1028184 := by
    simpa [prefixWord, tailWord_1028184, baseEnd_1028184] using wordTrace_append hprefix tailTrace_1028184
  have hstable : (prefixWord ++ tailWord_1028184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028184).length < 2 ^ (prefixWord ++ tailWord_1028184).sum := by decide
  have hdescent : baseEnd_1028184 < baseStart_1028184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028186 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1028186 : Nat := 118140960795 + 1028186 * 2 ^ 59
def prefixEnd_1028186 : Nat := 4983230072969 + 3 ^ 40 * 1028186 * 2
def baseEnd_1028186 : Nat := 351969080149212967497643

theorem tailTrace_1028186 : CollatzResearch.WordTrace tailWord_1028186 prefixEnd_1028186 351969080149212967497643 := by
  unfold tailWord_1028186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375256063266299258416103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25000682835376798022442941 9375256063266299258416103)
  ·
    refine ⟨14062884094899448887624155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375256063266299258416103 14062884094899448887624155)
    ·
      refine ⟨21094326142349173331436233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062884094899448887624155 21094326142349173331436233)
      ·
        refine ⟨15820744606761879998577175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21094326142349173331436233 15820744606761879998577175)
        ·
          refine ⟨23731116910142819997865763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820744606761879998577175 23731116910142819997865763)
          ·
            refine ⟨35596675365214229996798645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23731116910142819997865763 35596675365214229996798645)
            ·
              refine ⟨3337188315488834062199873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35596675365214229996798645 3337188315488834062199873)
              ·
                refine ⟨2502891236616625546649905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337188315488834062199873 2502891236616625546649905)
                ·
                  refine ⟨1877168427462469159987429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2502891236616625546649905 1877168427462469159987429)
                  ·
                    refine ⟨351969080149212967497643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877168427462469159987429 351969080149212967497643)
                    ·
                      rfl

theorem cell22_1028186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1028186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028186 prefixEnd_1028186 := by exact prefixLift 1028186
  have htrace : WordTrace (prefixWord ++ tailWord_1028186) baseStart_1028186 baseEnd_1028186 := by
    simpa [prefixWord, tailWord_1028186, baseEnd_1028186] using wordTrace_append hprefix tailTrace_1028186
  have hstable : (prefixWord ++ tailWord_1028186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028186).length < 2 ^ (prefixWord ++ tailWord_1028186).sum := by decide
  have hdescent : baseEnd_1028186 < baseStart_1028186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028188 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1028188 : Nat := 118140960795 + 1028188 * 2 ^ 59
def prefixEnd_1028188 : Nat := 4983230072969 + 3 ^ 40 * 1028188 * 2
def baseEnd_1028188 : Nat := 351969764790085628947637

theorem tailTrace_1028188 : CollatzResearch.WordTrace tailWord_1028188 prefixEnd_1028188 351969764790085628947637 := by
  unfold tailWord_1028188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18750548599528975687618609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25000731466038634250158145 18750548599528975687618609)
  ·
    refine ⟨14062911449646731765713957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18750548599528975687618609 14062911449646731765713957)
    ·
      refine ⟨2636795896808762206071367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14062911449646731765713957 2636795896808762206071367)
      ·
        refine ⟨3955193845213143309107051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636795896808762206071367 3955193845213143309107051)
        ·
          refine ⟨5932790767819714963660577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955193845213143309107051 5932790767819714963660577)
          ·
            refine ⟨4449593075864786222745433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932790767819714963660577 4449593075864786222745433)
            ·
              refine ⟨3337194806898589667059075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449593075864786222745433 3337194806898589667059075)
              ·
                refine ⟨5005792210347884500588613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337194806898589667059075 5005792210347884500588613)
                ·
                  refine ⟨938586039440228343860365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5005792210347884500588613 938586039440228343860365)
                  ·
                    refine ⟨351969764790085628947637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938586039440228343860365 351969764790085628947637)
                    ·
                      rfl

theorem cell22_1028188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1028188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028188 prefixEnd_1028188 := by exact prefixLift 1028188
  have htrace : WordTrace (prefixWord ++ tailWord_1028188) baseStart_1028188 baseEnd_1028188 := by
    simpa [prefixWord, tailWord_1028188, baseEnd_1028188] using wordTrace_append hprefix tailTrace_1028188
  have hstable : (prefixWord ++ tailWord_1028188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028188).length < 2 ^ (prefixWord ++ tailWord_1028188).sum := by decide
  have hdescent : baseEnd_1028188 < baseStart_1028188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028216 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1028216 : Nat := 118140960795 + 1028216 * 2 ^ 59
def prefixEnd_1028216 : Nat := 4983230072969 + 3 ^ 40 * 1028216 * 2
def baseEnd_1028216 : Nat := 351979349762302889247551

theorem tailTrace_1028216 : CollatzResearch.WordTrace tailWord_1028216 prefixEnd_1028216 351979349762302889247551 := by
  unfold tailWord_1028216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751059221478256078628251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25001412295304341438171001 18751059221478256078628251)
  ·
    refine ⟨28126588832217384117942377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18751059221478256078628251 28126588832217384117942377)
    ·
      refine ⟨21094941624163038088456783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28126588832217384117942377 21094941624163038088456783)
      ·
        refine ⟨31642412436244557132685175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094941624163038088456783 31642412436244557132685175)
        ·
          refine ⟨47463618654366835699027763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31642412436244557132685175 47463618654366835699027763)
          ·
            refine ⟨71195427981550253548541645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47463618654366835699027763 71195427981550253548541645)
            ·
              refine ⟨26698285493081345080703117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71195427981550253548541645 26698285493081345080703117)
              ·
                refine ⟨10011857059905504405263669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26698285493081345080703117 10011857059905504405263669)
                ·
                  refine ⟨938611599366141037993469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10011857059905504405263669 938611599366141037993469)
                  ·
                    refine ⟨351979349762302889247551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938611599366141037993469 351979349762302889247551)
                    ·
                      rfl

theorem cell22_1028216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1028216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028216 prefixEnd_1028216 := by exact prefixLift 1028216
  have htrace : WordTrace (prefixWord ++ tailWord_1028216) baseStart_1028216 baseEnd_1028216 := by
    simpa [prefixWord, tailWord_1028216, baseEnd_1028216] using wordTrace_append hprefix tailTrace_1028216
  have hstable : (prefixWord ++ tailWord_1028216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028216).length < 2 ^ (prefixWord ++ tailWord_1028216).sum := by decide
  have hdescent : baseEnd_1028216 < baseStart_1028216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028261 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1028261 : Nat := 118140960795 + 1028261 * 2 ^ 59
def prefixEnd_1028261 : Nat := 4983230072969 + 3 ^ 40 * 1028261 * 2
def baseEnd_1028261 : Nat := 351994754181937771872413

theorem tailTrace_1028261 : CollatzResearch.WordTrace tailWord_1028261 prefixEnd_1028261 351994754181937771872413 := by
  unfold tailWord_1028261
  simp only [CollatzResearch.WordTrace]
  refine ⟨37503759727793484842644637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25002506485195656561763091 37503759727793484842644637)
  ·
    refine ⟨14063909897922556815991739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37503759727793484842644637 14063909897922556815991739)
    ·
      refine ⟨21095864846883835223987609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063909897922556815991739 21095864846883835223987609)
      ·
        refine ⟨15821898635162876417990707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21095864846883835223987609 15821898635162876417990707)
        ·
          refine ⟨23732847952744314626986061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821898635162876417990707 23732847952744314626986061)
          ·
            refine ⟨8899817982279117985119773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23732847952744314626986061 8899817982279117985119773)
            ·
              refine ⟨3337431743354669244419915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8899817982279117985119773 3337431743354669244419915)
              ·
                refine ⟨5006147615032003866629873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337431743354669244419915 5006147615032003866629873)
                ·
                  refine ⟨3754610711274002899972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006147615032003866629873 3754610711274002899972405)
                  ·
                    refine ⟨351994754181937771872413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3754610711274002899972405 351994754181937771872413)
                    ·
                      rfl

theorem cell22_1028261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1028261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028261 prefixEnd_1028261 := by exact prefixLift 1028261
  have htrace : WordTrace (prefixWord ++ tailWord_1028261) baseStart_1028261 baseEnd_1028261 := by
    simpa [prefixWord, tailWord_1028261, baseEnd_1028261] using wordTrace_append hprefix tailTrace_1028261
  have hstable : (prefixWord ++ tailWord_1028261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028261).length < 2 ^ (prefixWord ++ tailWord_1028261).sum := by decide
  have hdescent : baseEnd_1028261 < baseStart_1028261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028321 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1028321 : Nat := 118140960795 + 1028321 * 2 ^ 59
def prefixEnd_1028321 : Nat := 4983230072969 + 3 ^ 40 * 1028321 * 2
def baseEnd_1028321 : Nat := 352015293408117615372229

theorem tailTrace_1028321 : CollatzResearch.WordTrace tailWord_1028321 prefixEnd_1028321 352015293408117615372229 := by
  unfold tailWord_1028321
  simp only [CollatzResearch.WordTrace]
  refine ⟨37505948107576115089828817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25003965405050743393219211 37505948107576115089828817)
  ·
    refine ⟨28129461080682086317371613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37505948107576115089828817 28129461080682086317371613)
    ·
      refine ⟨10548547905255782369014355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28129461080682086317371613 10548547905255782369014355)
      ·
        refine ⟨15822821857883673553521533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548547905255782369014355 15822821857883673553521533)
        ·
          refine ⟨5933558196706377582570575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15822821857883673553521533 5933558196706377582570575)
          ·
            refine ⟨8900337295059566373855863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933558196706377582570575 8900337295059566373855863)
            ·
              refine ⟨13350505942589349560783795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900337295059566373855863 13350505942589349560783795)
              ·
                refine ⟨20025758913884024341175693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350505942589349560783795 20025758913884024341175693)
                ·
                  refine ⟨7509659592706509127940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20025758913884024341175693 7509659592706509127940885)
                  ·
                    refine ⟨352015293408117615372229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7509659592706509127940885 352015293408117615372229)
                    ·
                      rfl

theorem cell22_1028321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1028321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028321 prefixEnd_1028321 := by exact prefixLift 1028321
  have htrace : WordTrace (prefixWord ++ tailWord_1028321) baseStart_1028321 baseEnd_1028321 := by
    simpa [prefixWord, tailWord_1028321, baseEnd_1028321] using wordTrace_append hprefix tailTrace_1028321
  have hstable : (prefixWord ++ tailWord_1028321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028321).length < 2 ^ (prefixWord ++ tailWord_1028321).sum := by decide
  have hdescent : baseEnd_1028321 < baseStart_1028321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028338 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1028338 : Nat := 118140960795 + 1028338 * 2 ^ 59
def prefixEnd_1028338 : Nat := 4983230072969 + 3 ^ 40 * 1028338 * 2
def baseEnd_1028338 : Nat := 352021112855535237697177

theorem tailTrace_1028338 : CollatzResearch.WordTrace tailWord_1028338 prefixEnd_1028338 352021112855535237697177 := by
  unfold tailWord_1028338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376642037128631748299417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25004378765676351328798445 9376642037128631748299417)
  ·
    refine ⟨7032481527846473811224563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9376642037128631748299417 7032481527846473811224563)
    ·
      refine ⟨10548722291769710716836845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032481527846473811224563 10548722291769710716836845)
      ·
        refine ⟨3955770859413641518813817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10548722291769710716836845 3955770859413641518813817)
        ·
          refine ⟨2966828144560231139110363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3955770859413641518813817 2966828144560231139110363)
          ·
            refine ⟨4450242216840346708665545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966828144560231139110363 4450242216840346708665545)
            ·
              refine ⟨3337681662630260031499159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450242216840346708665545 3337681662630260031499159)
              ·
                refine ⟨5006522493945390047248739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337681662630260031499159 5006522493945390047248739)
                ·
                  refine ⟨7509783740918085070873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006522493945390047248739 7509783740918085070873109)
                  ·
                    refine ⟨352021112855535237697177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7509783740918085070873109 352021112855535237697177)
                    ·
                      rfl

theorem cell22_1028338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1028338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028338 prefixEnd_1028338 := by exact prefixLift 1028338
  have htrace : WordTrace (prefixWord ++ tailWord_1028338) baseStart_1028338 baseEnd_1028338 := by
    simpa [prefixWord, tailWord_1028338, baseEnd_1028338] using wordTrace_append hprefix tailTrace_1028338
  have hstable : (prefixWord ++ tailWord_1028338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028338).length < 2 ^ (prefixWord ++ tailWord_1028338).sum := by decide
  have hdescent : baseEnd_1028338 < baseStart_1028338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028359 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 4]
def baseStart_1028359 : Nat := 118140960795 + 1028359 * 2 ^ 59
def prefixEnd_1028359 : Nat := 4983230072969 + 3 ^ 40 * 1028359 * 2
def baseEnd_1028359 : Nat := 117342767194899394307371

theorem tailTrace_1028359 : CollatzResearch.WordTrace tailWord_1028359 prefixEnd_1028359 117342767194899394307371 := by
  unfold tailWord_1028359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37507334081438447579712131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25004889387625631719808087 37507334081438447579712131)
  ·
    refine ⟨56261001122157671369568197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37507334081438447579712131 56261001122157671369568197)
    ·
      refine ⟨10548937710404563381794037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56261001122157671369568197 10548937710404563381794037)
      ·
        refine ⟨988962910350427817043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10548937710404563381794037 988962910350427817043191)
        ·
          refine ⟨1483444365525641725564787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988962910350427817043191 1483444365525641725564787)
          ·
            refine ⟨2225166548288462588347181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483444365525641725564787 2225166548288462588347181)
            ·
              refine ⟨834437455608173470630193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225166548288462588347181 834437455608173470630193)
              ·
                refine ⟨625828091706130102972645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834437455608173470630193 625828091706130102972645)
                ·
                  refine ⟨117342767194899394307371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625828091706130102972645 117342767194899394307371)
                  ·
                    rfl

theorem cell22_1028359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 4].length) (baseStart_1028359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028359 prefixEnd_1028359 := by exact prefixLift 1028359
  have htrace : WordTrace (prefixWord ++ tailWord_1028359) baseStart_1028359 baseEnd_1028359 := by
    simpa [prefixWord, tailWord_1028359, baseEnd_1028359] using wordTrace_append hprefix tailTrace_1028359
  have hstable : (prefixWord ++ tailWord_1028359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028359).length < 2 ^ (prefixWord ++ tailWord_1028359).sum := by decide
  have hdescent : baseEnd_1028359 < baseStart_1028359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028428 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1028428 : Nat := 118140960795 + 1028428 * 2 ^ 59
def prefixEnd_1028428 : Nat := 4983230072969 + 3 ^ 40 * 1028428 * 2
def baseEnd_1028428 : Nat := 352051921694805002946901

theorem tailTrace_1028428 : CollatzResearch.WordTrace tailWord_1028428 prefixEnd_1028428 352051921694805002946901 := by
  unfold tailWord_1028428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18754925359094236181986969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25006567145458981575982625 18754925359094236181986969)
  ·
    refine ⟨14066194019320677136490227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18754925359094236181986969 14066194019320677136490227)
    ·
      refine ⟨21099291028981015704735341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066194019320677136490227 21099291028981015704735341)
      ·
        refine ⟨7912234135867880889275753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21099291028981015704735341 7912234135867880889275753)
        ·
          refine ⟨5934175601900910666956815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912234135867880889275753 5934175601900910666956815)
          ·
            refine ⟨8901263402851366000435223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934175601900910666956815 8901263402851366000435223)
            ·
              refine ⟨13351895104277049000652835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901263402851366000435223 13351895104277049000652835)
              ·
                refine ⟨20027842656415573500979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351895104277049000652835 20027842656415573500979253)
                ·
                  refine ⟨1877610249038960015716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20027842656415573500979253 1877610249038960015716805)
                  ·
                    refine ⟨352051921694805002946901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877610249038960015716805 352051921694805002946901)
                    ·
                      rfl

theorem cell22_1028428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1028428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028428 prefixEnd_1028428 := by exact prefixLift 1028428
  have htrace : WordTrace (prefixWord ++ tailWord_1028428) baseStart_1028428 baseEnd_1028428 := by
    simpa [prefixWord, tailWord_1028428, baseEnd_1028428] using wordTrace_append hprefix tailTrace_1028428
  have hstable : (prefixWord ++ tailWord_1028428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028428).length < 2 ^ (prefixWord ++ tailWord_1028428).sum := by decide
  have hdescent : baseEnd_1028428 < baseStart_1028428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1028473 : Nat := 118140960795 + 1028473 * 2 ^ 59
def prefixEnd_1028473 : Nat := 4983230072969 + 3 ^ 40 * 1028473 * 2
def baseEnd_1028473 : Nat := 352067326114439885571763

theorem tailTrace_1028473 : CollatzResearch.WordTrace tailWord_1028473 prefixEnd_1028473 352067326114439885571763 := by
  unfold tailWord_1028473
  simp only [CollatzResearch.WordTrace]
  refine ⟨37511492003025445049362073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25007661335350296699574715 37511492003025445049362073)
  ·
    refine ⟨28133619002269083787021555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37511492003025445049362073 28133619002269083787021555)
    ·
      refine ⟨42200428503403625680532333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28133619002269083787021555 42200428503403625680532333)
      ·
        refine ⟨15825160688776359630199625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42200428503403625680532333 15825160688776359630199625)
        ·
          refine ⟨11868870516582269722649719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15825160688776359630199625 11868870516582269722649719)
          ·
            refine ⟨17803305774873404583974579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868870516582269722649719 17803305774873404583974579)
            ·
              refine ⟨26704958662310106875961869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17803305774873404583974579 26704958662310106875961869)
              ·
                refine ⟨10014359498366290078485701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26704958662310106875961869 10014359498366290078485701)
                ·
                  refine ⟨1877692405943679389716069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10014359498366290078485701 1877692405943679389716069)
                  ·
                    refine ⟨352067326114439885571763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877692405943679389716069 352067326114439885571763)
                    ·
                      rfl

theorem cell22_1028473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1028473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028473 prefixEnd_1028473 := by exact prefixLift 1028473
  have htrace : WordTrace (prefixWord ++ tailWord_1028473) baseStart_1028473 baseEnd_1028473 := by
    simpa [prefixWord, tailWord_1028473, baseEnd_1028473] using wordTrace_append hprefix tailTrace_1028473
  have hstable : (prefixWord ++ tailWord_1028473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028473).length < 2 ^ (prefixWord ++ tailWord_1028473).sum := by decide
  have hdescent : baseEnd_1028473 < baseStart_1028473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028475 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 4, 3]
def baseStart_1028475 : Nat := 118140960795 + 1028475 * 2 ^ 59
def prefixEnd_1028475 : Nat := 4983230072969 + 3 ^ 40 * 1028475 * 2
def baseEnd_1028475 : Nat := 352068010755312547021757

theorem tailTrace_1028475 : CollatzResearch.WordTrace tailWord_1028475 prefixEnd_1028475 352068010755312547021757 := by
  unfold tailWord_1028475
  simp only [CollatzResearch.WordTrace]
  refine ⟨37511564949018199390934879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25007709966012132927289919 37511564949018199390934879)
  ·
    refine ⟨56267347423527299086402319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37511564949018199390934879 56267347423527299086402319)
    ·
      refine ⟨84401021135290948629603479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56267347423527299086402319 84401021135290948629603479)
      ·
        refine ⟨126601531702936422944405219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84401021135290948629603479 126601531702936422944405219)
        ·
          refine ⟨189902297554404634416607829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126601531702936422944405219 189902297554404634416607829)
          ·
            refine ⟨2225417549465679309569623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 189902297554404634416607829 2225417549465679309569623)
            ·
              refine ⟨3338126324198518964354435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225417549465679309569623 3338126324198518964354435)
              ·
                refine ⟨5007189486297778446531653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338126324198518964354435 5007189486297778446531653)
                ·
                  refine ⟨938848028680833458724685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5007189486297778446531653 938848028680833458724685)
                  ·
                    refine ⟨352068010755312547021757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938848028680833458724685 352068010755312547021757)
                    ·
                      rfl

theorem cell22_1028475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].length) (baseStart_1028475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028475 prefixEnd_1028475 := by exact prefixLift 1028475
  have htrace : WordTrace (prefixWord ++ tailWord_1028475) baseStart_1028475 baseEnd_1028475 := by
    simpa [prefixWord, tailWord_1028475, baseEnd_1028475] using wordTrace_append hprefix tailTrace_1028475
  have hstable : (prefixWord ++ tailWord_1028475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028475).length < 2 ^ (prefixWord ++ tailWord_1028475).sum := by decide
  have hdescent : baseEnd_1028475 < baseStart_1028475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028488 : List Nat := [2, 1, 3, 3, 1, 1, 2, 9]
def baseStart_1028488 : Nat := 118140960795 + 1028488 * 2 ^ 59
def prefixEnd_1028488 : Nat := 4983230072969 + 3 ^ 40 * 1028488 * 2
def baseEnd_1028488 : Nat := 39119162324553871827413

theorem tailTrace_1028488 : CollatzResearch.WordTrace tailWord_1028488 prefixEnd_1028488 39119162324553871827413 := by
  unfold tailWord_1028488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18756019548985551305579059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25008026065314068407438745 18756019548985551305579059)
  ·
    refine ⟨28134029323478326958368589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18756019548985551305579059 28134029323478326958368589)
    ·
      refine ⟨10550260996304372609388221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28134029323478326958368589 10550260996304372609388221)
      ·
        refine ⟨3956347873614139728520583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10550260996304372609388221 3956347873614139728520583)
        ·
          refine ⟨5934521810421209592780875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956347873614139728520583 5934521810421209592780875)
          ·
            refine ⟨8901782715631814389171313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934521810421209592780875 8901782715631814389171313)
            ·
              refine ⟨6676337036723860791878485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8901782715631814389171313 6676337036723860791878485)
              ·
                refine ⟨39119162324553871827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6676337036723860791878485 39119162324553871827413)
                ·
                  rfl

theorem cell22_1028488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_1028488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028488 prefixEnd_1028488 := by exact prefixLift 1028488
  have htrace : WordTrace (prefixWord ++ tailWord_1028488) baseStart_1028488 baseEnd_1028488 := by
    simpa [prefixWord, tailWord_1028488, baseEnd_1028488] using wordTrace_append hprefix tailTrace_1028488
  have hstable : (prefixWord ++ tailWord_1028488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028488).length < 2 ^ (prefixWord ++ tailWord_1028488).sum := by decide
  have hdescent : baseEnd_1028488 < baseStart_1028488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028537 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_1028537 : Nat := 118140960795 + 1028537 * 2 ^ 59
def prefixEnd_1028537 : Nat := 4983230072969 + 3 ^ 40 * 1028537 * 2
def baseEnd_1028537 : Nat := 352089234622365051971567

theorem tailTrace_1028537 : CollatzResearch.WordTrace tailWord_1028537 prefixEnd_1028537 352089234622365051971567 := by
  unfold tailWord_1028537
  simp only [CollatzResearch.WordTrace]
  refine ⟨37513826274793583979691865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25009217516529055986461243 37513826274793583979691865)
  ·
    refine ⟨28135369706095187984768899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37513826274793583979691865 28135369706095187984768899)
    ·
      refine ⟨42203054559142781977153349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28135369706095187984768899 42203054559142781977153349)
      ·
        refine ⟨7913072729839271620716253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42203054559142781977153349 7913072729839271620716253)
        ·
          refine ⟨2967402273689726857768595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7913072729839271620716253 2967402273689726857768595)
          ·
            refine ⟨4451103410534590286652893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967402273689726857768595 4451103410534590286652893)
            ·
              refine ⟨1669163778950471357494835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4451103410534590286652893 1669163778950471357494835)
              ·
                refine ⟨2503745668425707036242253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669163778950471357494835 2503745668425707036242253)
                ·
                  refine ⟨938904625659640138590845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2503745668425707036242253 938904625659640138590845)
                  ·
                    refine ⟨352089234622365051971567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938904625659640138590845 352089234622365051971567)
                    ·
                      rfl

theorem cell22_1028537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_1028537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028537 prefixEnd_1028537 := by exact prefixLift 1028537
  have htrace : WordTrace (prefixWord ++ tailWord_1028537) baseStart_1028537 baseEnd_1028537 := by
    simpa [prefixWord, tailWord_1028537, baseEnd_1028537] using wordTrace_append hprefix tailTrace_1028537
  have hstable : (prefixWord ++ tailWord_1028537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028537).length < 2 ^ (prefixWord ++ tailWord_1028537).sum := by decide
  have hdescent : baseEnd_1028537 < baseStart_1028537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028612 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1028612 : Nat := 118140960795 + 1028612 * 2 ^ 59
def prefixEnd_1028612 : Nat := 4983230072969 + 3 ^ 40 * 1028612 * 2
def baseEnd_1028612 : Nat := 117371636218363285448779

theorem tailTrace_1028612 : CollatzResearch.WordTrace tailWord_1028612 prefixEnd_1028612 117371636218363285448779 := by
  unfold tailWord_1028612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758280874760935894336045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25011041166347914525781393 18758280874760935894336045)
  ·
    refine ⟨7034355328035350960376017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18758280874760935894336045 7034355328035350960376017)
    ·
      refine ⟨5275766496026513220282013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7034355328035350960376017 5275766496026513220282013)
      ·
        refine ⟨1978412436009942457605755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5275766496026513220282013 1978412436009942457605755)
        ·
          refine ⟨2967618654014913686408633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978412436009942457605755 2967618654014913686408633)
          ·
            refine ⟨2225713990511185264806475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967618654014913686408633 2225713990511185264806475)
            ·
              refine ⟨3338570985766777897209713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225713990511185264806475 3338570985766777897209713)
              ·
                refine ⟨2503928239325083422907285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338570985766777897209713 2503928239325083422907285)
                ·
                  refine ⟨117371636218363285448779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2503928239325083422907285 117371636218363285448779)
                  ·
                    rfl

theorem cell22_1028612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1028612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028612 prefixEnd_1028612 := by exact prefixLift 1028612
  have htrace : WordTrace (prefixWord ++ tailWord_1028612) baseStart_1028612 baseEnd_1028612 := by
    simpa [prefixWord, tailWord_1028612, baseEnd_1028612] using wordTrace_append hprefix tailTrace_1028612
  have hstable : (prefixWord ++ tailWord_1028612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028612).length < 2 ^ (prefixWord ++ tailWord_1028612).sum := by decide
  have hdescent : baseEnd_1028612 < baseStart_1028612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028625 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1028625 : Nat := 118140960795 + 1028625 * 2 ^ 59
def prefixEnd_1028625 : Nat := 4983230072969 + 3 ^ 40 * 1028625 * 2
def baseEnd_1028625 : Nat := 352119358820762155771297

theorem tailTrace_1028625 : CollatzResearch.WordTrace tailWord_1028625 prefixEnd_1028625 352119358820762155771297 := by
  unfold tailWord_1028625
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517035898474775008895329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25011357265649850005930219 37517035898474775008895329)
  ·
    refine ⟨28137776923856081256671497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37517035898474775008895329 28137776923856081256671497)
    ·
      refine ⟨21103332692892060942503623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28137776923856081256671497 21103332692892060942503623)
      ·
        refine ⟨31654999039338091413755435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103332692892060942503623 31654999039338091413755435)
        ·
          refine ⟨47482498559007137120633153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31654999039338091413755435 47482498559007137120633153)
          ·
            refine ⟨35611873919255352840474865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47482498559007137120633153 35611873919255352840474865)
            ·
              refine ⟨26708905439441514630356149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35611873919255352840474865 26708905439441514630356149)
              ·
                refine ⟨2503959884947641996595889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26708905439441514630356149 2503959884947641996595889)
                ·
                  refine ⟨1877969913710731497446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503959884947641996595889 1877969913710731497446917)
                  ·
                    refine ⟨352119358820762155771297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877969913710731497446917 352119358820762155771297)
                    ·
                      rfl

theorem cell22_1028625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1028625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028625 prefixEnd_1028625 := by exact prefixLift 1028625
  have htrace : WordTrace (prefixWord ++ tailWord_1028625) baseStart_1028625 baseEnd_1028625 := by
    simpa [prefixWord, tailWord_1028625, baseEnd_1028625] using wordTrace_append hprefix tailTrace_1028625
  have hstable : (prefixWord ++ tailWord_1028625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028625).length < 2 ^ (prefixWord ++ tailWord_1028625).sum := by decide
  have hdescent : baseEnd_1028625 < baseStart_1028625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028672 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_1028672 : Nat := 118140960795 + 1028672 * 2 ^ 59
def prefixEnd_1028672 : Nat := 4983230072969 + 3 ^ 40 * 1028672 * 2
def baseEnd_1028672 : Nat := 352135447881269699846153

theorem tailTrace_1028672 : CollatzResearch.WordTrace tailWord_1028672 prefixEnd_1028672 352135447881269699846153 := by
  unfold tailWord_1028672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759375064652251017928135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25012500086203001357237513 18759375064652251017928135)
  ·
    refine ⟨28139062596978376526892203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18759375064652251017928135 28139062596978376526892203)
    ·
      refine ⟨42208593895467564790338305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139062596978376526892203 42208593895467564790338305)
      ·
        refine ⟨31656445421600673592753729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42208593895467564790338305 31656445421600673592753729)
        ·
          refine ⟨23742334066200505194565297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31656445421600673592753729 23742334066200505194565297)
          ·
            refine ⟨17806750549650378895923973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742334066200505194565297 17806750549650378895923973)
            ·
              refine ⟨3338765728059446042985745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17806750549650378895923973 3338765728059446042985745)
              ·
                refine ⟨2504074296044584532239309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338765728059446042985745 2504074296044584532239309)
                ·
                  refine ⟨939027861016719199589741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2504074296044584532239309 939027861016719199589741)
                  ·
                    refine ⟨352135447881269699846153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939027861016719199589741 352135447881269699846153)
                    ·
                      rfl

theorem cell22_1028672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_1028672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028672 prefixEnd_1028672 := by exact prefixLift 1028672
  have htrace : WordTrace (prefixWord ++ tailWord_1028672) baseStart_1028672 baseEnd_1028672 := by
    simpa [prefixWord, tailWord_1028672, baseEnd_1028672] using wordTrace_append hprefix tailTrace_1028672
  have hstable : (prefixWord ++ tailWord_1028672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028672).length < 2 ^ (prefixWord ++ tailWord_1028672).sum := by decide
  have hdescent : baseEnd_1028672 < baseStart_1028672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028813 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1028813 : Nat := 118140960795 + 1028813 * 2 ^ 59
def prefixEnd_1028813 : Nat := 4983230072969 + 3 ^ 40 * 1028813 * 2
def baseEnd_1028813 : Nat := 352183715062792332070721

theorem tailTrace_1028813 : CollatzResearch.WordTrace tailWord_1028813 prefixEnd_1028813 352183715062792332070721 := by
  unfold tailWord_1028813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523892821793683116739093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25015928547862455411159395 37523892821793683116739093)
  ·
    refine ⟨1758932476021578896097145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37523892821793683116739093 1758932476021578896097145)
    ·
      refine ⟨1319199357016184172072859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1758932476021578896097145 1319199357016184172072859)
      ·
        refine ⟨1978799035524276258109289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319199357016184172072859 1978799035524276258109289)
        ·
          refine ⟨1484099276643207193581967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978799035524276258109289 1484099276643207193581967)
          ·
            refine ⟨2226148914964810790372951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484099276643207193581967 2226148914964810790372951)
            ·
              refine ⟨3339223372447216185559427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226148914964810790372951 3339223372447216185559427)
              ·
                refine ⟨5008835058670824278339141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339223372447216185559427 5008835058670824278339141)
                ·
                  refine ⟨939156573500779552188589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5008835058670824278339141 939156573500779552188589)
                  ·
                    refine ⟨352183715062792332070721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939156573500779552188589 352183715062792332070721)
                    ·
                      rfl

theorem cell22_1028813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1028813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028813 prefixEnd_1028813 := by exact prefixLift 1028813
  have htrace : WordTrace (prefixWord ++ tailWord_1028813) baseStart_1028813 baseEnd_1028813 := by
    simpa [prefixWord, tailWord_1028813, baseEnd_1028813] using wordTrace_append hprefix tailTrace_1028813
  have hstable : (prefixWord ++ tailWord_1028813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028813).length < 2 ^ (prefixWord ++ tailWord_1028813).sum := by decide
  have hdescent : baseEnd_1028813 < baseStart_1028813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028824 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_1028824 : Nat := 118140960795 + 1028824 * 2 ^ 59
def prefixEnd_1028824 : Nat := 4983230072969 + 3 ^ 40 * 1028824 * 2
def baseEnd_1028824 : Nat := 352187480587591970045687

theorem tailTrace_1028824 : CollatzResearch.WordTrace tailWord_1028824 prefixEnd_1028824 352187480587591970045687 := by
  unfold tailWord_1028824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18762147012376915997694763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25016196016502554663593017 18762147012376915997694763)
  ·
    refine ⟨28143220518565373996542145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18762147012376915997694763 28143220518565373996542145)
    ·
      refine ⟨21107415388924030497406609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28143220518565373996542145 21107415388924030497406609)
      ·
        refine ⟨15830561541693022873054957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21107415388924030497406609 15830561541693022873054957)
        ·
          refine ⟨5936460578134883577395609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15830561541693022873054957 5936460578134883577395609)
          ·
            refine ⟨4452345433601162683046707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936460578134883577395609 4452345433601162683046707)
            ·
              refine ⟨6678518150401744024570061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452345433601162683046707 6678518150401744024570061)
              ·
                refine ⟨2504444306400654009213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6678518150401744024570061 2504444306400654009213773)
                ·
                  refine ⟨939166614900245253455165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2504444306400654009213773 939166614900245253455165)
                  ·
                    refine ⟨352187480587591970045687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939166614900245253455165 352187480587591970045687)
                    ·
                      rfl

theorem cell22_1028824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_1028824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028824 prefixEnd_1028824 := by exact prefixLift 1028824
  have htrace : WordTrace (prefixWord ++ tailWord_1028824) baseStart_1028824 baseEnd_1028824 := by
    simpa [prefixWord, tailWord_1028824, baseEnd_1028824] using wordTrace_append hprefix tailTrace_1028824
  have hstable : (prefixWord ++ tailWord_1028824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028824).length < 2 ^ (prefixWord ++ tailWord_1028824).sum := by decide
  have hdescent : baseEnd_1028824 < baseStart_1028824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_1028867 : Nat := 118140960795 + 1028867 * 2 ^ 59
def prefixEnd_1028867 : Nat := 4983230072969 + 3 ^ 40 * 1028867 * 2
def baseEnd_1028867 : Nat := 352202200366354191220555

theorem tailTrace_1028867 : CollatzResearch.WordTrace tailWord_1028867 prefixEnd_1028867 352202200366354191220555 := by
  unfold tailWord_1028867
  simp only [CollatzResearch.WordTrace]
  refine ⟨37525862363598050339204855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25017241575732033559469903 37525862363598050339204855)
  ·
    refine ⟨56288793545397075508807283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37525862363598050339204855 56288793545397075508807283)
    ·
      refine ⟨84433190318095613263210925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56288793545397075508807283 84433190318095613263210925)
      ·
        refine ⟨31662446369285854973704097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84433190318095613263210925 31662446369285854973704097)
        ·
          refine ⟨23746834776964391230278073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31662446369285854973704097 23746834776964391230278073)
          ·
            refine ⟨17810126082723293422708555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23746834776964391230278073 17810126082723293422708555)
            ·
              refine ⟨26715189124084940134062833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17810126082723293422708555 26715189124084940134062833)
              ·
                refine ⟨20036391843063705100547125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26715189124084940134062833 20036391843063705100547125)
                ·
                  refine ⟨1878411735287222353176293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20036391843063705100547125 1878411735287222353176293)
                  ·
                    refine ⟨352202200366354191220555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878411735287222353176293 352202200366354191220555)
                    ·
                      rfl

theorem cell22_1028867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_1028867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028867 prefixEnd_1028867 := by exact prefixLift 1028867
  have htrace : WordTrace (prefixWord ++ tailWord_1028867) baseStart_1028867 baseEnd_1028867 := by
    simpa [prefixWord, tailWord_1028867, baseEnd_1028867] using wordTrace_append hprefix tailTrace_1028867
  have hstable : (prefixWord ++ tailWord_1028867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028867).length < 2 ^ (prefixWord ++ tailWord_1028867).sum := by decide
  have hdescent : baseEnd_1028867 < baseStart_1028867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028912 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1028912 : Nat := 118140960795 + 1028912 * 2 ^ 59
def prefixEnd_1028912 : Nat := 4983230072969 + 3 ^ 40 * 1028912 * 2
def baseEnd_1028912 : Nat := 352217604785989073845417

theorem tailTrace_1028912 : CollatzResearch.WordTrace tailWord_1028912 prefixEnd_1028912 352217604785989073845417 := by
  unfold tailWord_1028912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763751824217511512296495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25018335765623348683061993 18763751824217511512296495)
  ·
    refine ⟨28145627736326267268444743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18763751824217511512296495 28145627736326267268444743)
    ·
      refine ⟨42218441604489400902667115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28145627736326267268444743 42218441604489400902667115)
      ·
        refine ⟨63327662406734101354000673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42218441604489400902667115 63327662406734101354000673)
        ·
          refine ⟨47495746805050576015500505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63327662406734101354000673 47495746805050576015500505)
          ·
            refine ⟨35621810103787932011625379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47495746805050576015500505 35621810103787932011625379)
            ·
              refine ⟨53432715155681898017438069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35621810103787932011625379 53432715155681898017438069)
              ·
                refine ⟨5009317045845177939134819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53432715155681898017438069 5009317045845177939134819)
                ·
                  refine ⟨7513975568767766908702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009317045845177939134819 7513975568767766908702229)
                  ·
                    refine ⟨352217604785989073845417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7513975568767766908702229 352217604785989073845417)
                    ·
                      rfl

theorem cell22_1028912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1028912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028912 prefixEnd_1028912 := by exact prefixLift 1028912
  have htrace : WordTrace (prefixWord ++ tailWord_1028912) baseStart_1028912 baseEnd_1028912 := by
    simpa [prefixWord, tailWord_1028912, baseEnd_1028912] using wordTrace_append hprefix tailTrace_1028912
  have hstable : (prefixWord ++ tailWord_1028912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028912).length < 2 ^ (prefixWord ++ tailWord_1028912).sum := by decide
  have hdescent : baseEnd_1028912 < baseStart_1028912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028914 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1028914 : Nat := 118140960795 + 1028914 * 2 ^ 59
def prefixEnd_1028914 : Nat := 4983230072969 + 3 ^ 40 * 1028914 * 2
def baseEnd_1028914 : Nat := 352218289426861735295411

theorem tailTrace_1028914 : CollatzResearch.WordTrace tailWord_1028914 prefixEnd_1028914 352218289426861735295411 := by
  unfold tailWord_1028914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381894148606944341541449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25018384396285184910777197 9381894148606944341541449)
  ·
    refine ⟨7036420611455208256156087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9381894148606944341541449 7036420611455208256156087)
    ·
      refine ⟨10554630917182812384234131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036420611455208256156087 10554630917182812384234131)
      ·
        refine ⟨15831946375774218576351197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10554630917182812384234131 15831946375774218576351197)
        ·
          refine ⟨5936979890915331966131699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15831946375774218576351197 5936979890915331966131699)
          ·
            refine ⟨8905469836372997949197549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936979890915331966131699 8905469836372997949197549)
            ·
              refine ⟨3339551188639874230949081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8905469836372997949197549 3339551188639874230949081)
              ·
                refine ⟨2504663391479905673211811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339551188639874230949081 2504663391479905673211811)
                ·
                  refine ⟨3756995087219858509817717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504663391479905673211811 3756995087219858509817717)
                  ·
                    refine ⟨352218289426861735295411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3756995087219858509817717 352218289426861735295411)
                    ·
                      rfl

theorem cell22_1028914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1028914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028914 prefixEnd_1028914 := by exact prefixLift 1028914
  have htrace : WordTrace (prefixWord ++ tailWord_1028914) baseStart_1028914 baseEnd_1028914 := by
    simpa [prefixWord, tailWord_1028914, baseEnd_1028914] using wordTrace_append hprefix tailTrace_1028914
  have hstable : (prefixWord ++ tailWord_1028914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028914).length < 2 ^ (prefixWord ++ tailWord_1028914).sum := by decide
  have hdescent : baseEnd_1028914 < baseStart_1028914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028927 : List Nat := [1, 1, 2, 2, 5, 11]
def baseStart_1028927 : Nat := 118140960795 + 1028927 * 2 ^ 59
def prefixEnd_1028927 : Nat := 4983230072969 + 3 ^ 40 * 1028927 * 2
def baseEnd_1028927 : Nat := 4348428883858444873091

theorem tailTrace_1028927 : CollatzResearch.WordTrace tailWord_1028927 prefixEnd_1028927 4348428883858444873091 := by
  unfold tailWord_1028927
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528050743380680586389035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25018700495587120390926023 37528050743380680586389035)
  ·
    refine ⟨56292076115071020879583553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528050743380680586389035 56292076115071020879583553)
    ·
      refine ⟨42219057086303265659687665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56292076115071020879583553 42219057086303265659687665)
      ·
        refine ⟨31664292814727449244765749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42219057086303265659687665 31664292814727449244765749)
        ·
          refine ⟨2968527451380698366696789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31664292814727449244765749 2968527451380698366696789)
          ·
            refine ⟨4348428883858444873091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2968527451380698366696789 4348428883858444873091)
            ·
              rfl

theorem cell22_1028927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 11].length) (baseStart_1028927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028927 prefixEnd_1028927 := by exact prefixLift 1028927
  have htrace : WordTrace (prefixWord ++ tailWord_1028927) baseStart_1028927 baseEnd_1028927 := by
    simpa [prefixWord, tailWord_1028927, baseEnd_1028927] using wordTrace_append hprefix tailTrace_1028927
  have hstable : (prefixWord ++ tailWord_1028927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028927).length < 2 ^ (prefixWord ++ tailWord_1028927).sum := by decide
  have hdescent : baseEnd_1028927 < baseStart_1028927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028931 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 2, 3]
def baseStart_1028931 : Nat := 118140960795 + 1028931 * 2 ^ 59
def prefixEnd_1028931 : Nat := 4983230072969 + 3 ^ 40 * 1028931 * 2
def baseEnd_1028931 : Nat := 352224108874279357620359

theorem tailTrace_1028931 : CollatzResearch.WordTrace tailWord_1028931 prefixEnd_1028931 352224108874279357620359 := by
  unfold tailWord_1028931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528196635366189269534647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25018797756910792846356431 37528196635366189269534647)
  ·
    refine ⟨56292294953049283904301971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528196635366189269534647 56292294953049283904301971)
    ·
      refine ⟨84438442429573925856452957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56292294953049283904301971 84438442429573925856452957)
      ·
        refine ⟨31664415911090222196169859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84438442429573925856452957 31664415911090222196169859)
        ·
          refine ⟨47496623866635333294254789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31664415911090222196169859 47496623866635333294254789)
          ·
            refine ⟨8905616974994124992672773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47496623866635333294254789 8905616974994124992672773)
            ·
              refine ⟨1669803182811398436126145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8905616974994124992672773 1669803182811398436126145)
              ·
                refine ⟨1252352387108548827094609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669803182811398436126145 1252352387108548827094609)
                ·
                  refine ⟨939264290331411620320957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1252352387108548827094609 939264290331411620320957)
                  ·
                    refine ⟨352224108874279357620359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939264290331411620320957 352224108874279357620359)
                    ·
                      rfl

theorem cell22_1028931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].length) (baseStart_1028931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1028931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1028931 prefixEnd_1028931 := by exact prefixLift 1028931
  have htrace : WordTrace (prefixWord ++ tailWord_1028931) baseStart_1028931 baseEnd_1028931 := by
    simpa [prefixWord, tailWord_1028931, baseEnd_1028931] using wordTrace_append hprefix tailTrace_1028931
  have hstable : (prefixWord ++ tailWord_1028931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028931).length < 2 ^ (prefixWord ++ tailWord_1028931).sum := by decide
  have hdescent : baseEnd_1028931 < baseStart_1028931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029004 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1029004 : Nat := 118140960795 + 1029004 * 2 ^ 59
def prefixEnd_1029004 : Nat := 4983230072969 + 3 ^ 40 * 1029004 * 2
def baseEnd_1029004 : Nat := 352249098266131500545135

theorem tailTrace_1029004 : CollatzResearch.WordTrace tailWord_1029004 prefixEnd_1029004 352249098266131500545135 := by
  unfold tailWord_1029004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765429582050861368471033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25020572776067815157961377 18765429582050861368471033)
  ·
    refine ⟨14074072186538146026353275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18765429582050861368471033 14074072186538146026353275)
    ·
      refine ⟨21111108279807219039529913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074072186538146026353275 21111108279807219039529913)
      ·
        refine ⟨15833331209855414279647435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21111108279807219039529913 15833331209855414279647435)
        ·
          refine ⟨23749996814783121419471153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833331209855414279647435 23749996814783121419471153)
          ·
            refine ⟨17812497611087341064603365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23749996814783121419471153 17812497611087341064603365)
            ·
              refine ⟨3339843302078876449613131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17812497611087341064603365 3339843302078876449613131)
              ·
                refine ⟨5009764953118314674419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339843302078876449613131 5009764953118314674419697)
                ·
                  refine ⟨3757323714838736005814773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009764953118314674419697 3757323714838736005814773)
                  ·
                    refine ⟨352249098266131500545135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3757323714838736005814773 352249098266131500545135)
                    ·
                      rfl

theorem cell22_1029004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1029004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029004 prefixEnd_1029004 := by exact prefixLift 1029004
  have htrace : WordTrace (prefixWord ++ tailWord_1029004) baseStart_1029004 baseEnd_1029004 := by
    simpa [prefixWord, tailWord_1029004, baseEnd_1029004] using wordTrace_append hprefix tailTrace_1029004
  have hstable : (prefixWord ++ tailWord_1029004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029004).length < 2 ^ (prefixWord ++ tailWord_1029004).sum := by decide
  have hdescent : baseEnd_1029004 < baseStart_1029004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029044 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1029044 : Nat := 118140960795 + 1029044 * 2 ^ 59
def prefixEnd_1029044 : Nat := 4983230072969 + 3 ^ 40 * 1029044 * 2
def baseEnd_1029044 : Nat := 352262791083584729545013

theorem tailTrace_1029044 : CollatzResearch.WordTrace tailWord_1029044 prefixEnd_1029044 352262791083584729545013 := by
  unfold tailWord_1029044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766159041978404784199093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25021545389304539712265457 18766159041978404784199093)
  ·
    refine ⟨1759327410185475448518665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18766159041978404784199093 1759327410185475448518665)
    ·
      refine ⟨1319495557639106586388999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1759327410185475448518665 1319495557639106586388999)
      ·
        refine ⟨1979243336458659879583499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319495557639106586388999 1979243336458659879583499)
        ·
          refine ⟨2968865004687989819375249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979243336458659879583499 2968865004687989819375249)
          ·
            refine ⟨2226648753515992364531437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968865004687989819375249 2226648753515992364531437)
            ·
              refine ⟨834993282568497136699289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226648753515992364531437 834993282568497136699289)
              ·
                refine ⟨626244961926372852524467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834993282568497136699289 626244961926372852524467)
                ·
                  refine ⟨939367442889559278786701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626244961926372852524467 939367442889559278786701)
                  ·
                    refine ⟨352262791083584729545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939367442889559278786701 352262791083584729545013)
                    ·
                      rfl

theorem cell22_1029044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1029044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029044 prefixEnd_1029044 := by exact prefixLift 1029044
  have htrace : WordTrace (prefixWord ++ tailWord_1029044) baseStart_1029044 baseEnd_1029044 := by
    simpa [prefixWord, tailWord_1029044, baseEnd_1029044] using wordTrace_append hprefix tailTrace_1029044
  have hstable : (prefixWord ++ tailWord_1029044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029044).length < 2 ^ (prefixWord ++ tailWord_1029044).sum := by decide
  have hdescent : baseEnd_1029044 < baseStart_1029044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029081 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1029081 : Nat := 118140960795 + 1029081 * 2 ^ 59
def prefixEnd_1029081 : Nat := 4983230072969 + 3 ^ 40 * 1029081 * 2
def baseEnd_1029081 : Nat := 352275456939728966369899

theorem tailTrace_1029081 : CollatzResearch.WordTrace tailWord_1029081 prefixEnd_1029081 352275456939728966369899 := by
  unfold tailWord_1029081
  simp only [CollatzResearch.WordTrace]
  refine ⟨37533667584822764887495097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25022445056548509924996731 37533667584822764887495097)
  ·
    refine ⟨28150250688617073665621323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37533667584822764887495097 28150250688617073665621323)
    ·
      refine ⟨42225376032925610498431985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28150250688617073665621323 42225376032925610498431985)
      ·
        refine ⟨31669032024694207873823989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42225376032925610498431985 31669032024694207873823989)
        ·
          refine ⟨2968971752315081988170999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31669032024694207873823989 2968971752315081988170999)
          ·
            refine ⟨4453457628472622982256499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968971752315081988170999 4453457628472622982256499)
            ·
              refine ⟨6680186442708934473384749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453457628472622982256499 6680186442708934473384749)
              ·
                refine ⟨2505069916015850427519281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6680186442708934473384749 2505069916015850427519281)
                ·
                  refine ⟨1878802437011887820639461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505069916015850427519281 1878802437011887820639461)
                  ·
                    refine ⟨352275456939728966369899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878802437011887820639461 352275456939728966369899)
                    ·
                      rfl

theorem cell22_1029081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1029081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029081 prefixEnd_1029081 := by exact prefixLift 1029081
  have htrace : WordTrace (prefixWord ++ tailWord_1029081) baseStart_1029081 baseEnd_1029081 := by
    simpa [prefixWord, tailWord_1029081, baseEnd_1029081] using wordTrace_append hprefix tailTrace_1029081
  have hstable : (prefixWord ++ tailWord_1029081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029081).length < 2 ^ (prefixWord ++ tailWord_1029081).sum := by decide
  have hdescent : baseEnd_1029081 < baseStart_1029081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029102 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_1029102 : Nat := 118140960795 + 1029102 * 2 ^ 59
def prefixEnd_1029102 : Nat := 4983230072969 + 3 ^ 40 * 1029102 * 2
def baseEnd_1029102 : Nat := 117427548556297303864945

theorem tailTrace_1029102 : CollatzResearch.WordTrace tailWord_1029102 prefixEnd_1029102 117427548556297303864945 := by
  unfold tailWord_1029102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691804189718335684251195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25022955678497790316006373 4691804189718335684251195)
  ·
    refine ⟨7037706284577503526376793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691804189718335684251195 7037706284577503526376793)
    ·
      refine ⟨5278279713433127644782595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7037706284577503526376793 5278279713433127644782595)
      ·
        refine ⟨7917419570149691467173893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278279713433127644782595 7917419570149691467173893)
        ·
          refine ⟨1484516169403067150095105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7917419570149691467173893 1484516169403067150095105)
          ·
            refine ⟨1113387127052300362571329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484516169403067150095105 1113387127052300362571329)
            ·
              refine ⟨835040345289225271928497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113387127052300362571329 835040345289225271928497)
              ·
                refine ⟨626280258966918953946373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835040345289225271928497 626280258966918953946373)
                ·
                  refine ⟨117427548556297303864945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626280258966918953946373 117427548556297303864945)
                  ·
                    rfl

theorem cell22_1029102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_1029102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029102 prefixEnd_1029102 := by exact prefixLift 1029102
  have htrace : WordTrace (prefixWord ++ tailWord_1029102) baseStart_1029102 baseEnd_1029102 := by
    simpa [prefixWord, tailWord_1029102, baseEnd_1029102] using wordTrace_append hprefix tailTrace_1029102
  have hstable : (prefixWord ++ tailWord_1029102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029102).length < 2 ^ (prefixWord ++ tailWord_1029102).sum := by decide
  have hdescent : baseEnd_1029102 < baseStart_1029102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029128 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1029128 : Nat := 118140960795 + 1029128 * 2 ^ 59
def prefixEnd_1029128 : Nat := 4983230072969 + 3 ^ 40 * 1029128 * 2
def baseEnd_1029128 : Nat := 352291546000236510444755

theorem tailTrace_1029128 : CollatzResearch.WordTrace tailWord_1029128 prefixEnd_1029128 352291546000236510444755 := by
  unfold tailWord_1029128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18767690907826245957228019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25023587877101661276304025 18767690907826245957228019)
  ·
    refine ⟨28151536361739368935842029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18767690907826245957228019 28151536361739368935842029)
    ·
      refine ⟨10556826135652263350940761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28151536361739368935842029 10556826135652263350940761)
      ·
        refine ⟨7917619601739197513205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10556826135652263350940761 7917619601739197513205571)
        ·
          refine ⟨11876429402608796269808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917619601739197513205571 11876429402608796269808357)
          ·
            refine ⟨2226830512989149300589067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11876429402608796269808357 2226830512989149300589067)
            ·
              refine ⟨3340245769483723950883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226830512989149300589067 3340245769483723950883601)
              ·
                refine ⟨2505184327112792963162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340245769483723950883601 2505184327112792963162701)
                ·
                  refine ⟨939444122667297361186013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2505184327112792963162701 939444122667297361186013)
                  ·
                    refine ⟨352291546000236510444755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939444122667297361186013 352291546000236510444755)
                    ·
                      rfl

theorem cell22_1029128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1029128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029128 prefixEnd_1029128 := by exact prefixLift 1029128
  have htrace : WordTrace (prefixWord ++ tailWord_1029128) baseStart_1029128 baseEnd_1029128 := by
    simpa [prefixWord, tailWord_1029128, baseEnd_1029128] using wordTrace_append hprefix tailTrace_1029128
  have hstable : (prefixWord ++ tailWord_1029128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029128).length < 2 ^ (prefixWord ++ tailWord_1029128).sum := by decide
  have hdescent : baseEnd_1029128 < baseStart_1029128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029139 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_1029139 : Nat := 118140960795 + 1029139 * 2 ^ 59
def prefixEnd_1029139 : Nat := 4983230072969 + 3 ^ 40 * 1029139 * 2
def baseEnd_1029139 : Nat := 352295311525036148419721

theorem tailTrace_1029139 : CollatzResearch.WordTrace tailWord_1029139 prefixEnd_1029139 352295311525036148419721 := by
  unfold tailWord_1029139
  simp only [CollatzResearch.WordTrace]
  refine ⟨37535783018612640793106471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25023855345741760528737647 37535783018612640793106471)
  ·
    refine ⟨56303674527918961189659707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37535783018612640793106471 56303674527918961189659707)
    ·
      refine ⟨84455511791878441784489561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56303674527918961189659707 84455511791878441784489561)
      ·
        refine ⟨63341633843908831338367171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84455511791878441784489561 63341633843908831338367171)
        ·
          refine ⟨95012450765863247007550757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63341633843908831338367171 95012450765863247007550757)
          ·
            refine ⟨17814834518599358813915767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95012450765863247007550757 17814834518599358813915767)
            ·
              refine ⟨26722251777899038220873651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17814834518599358813915767 26722251777899038220873651)
              ·
                refine ⟨40083377666848557331310477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26722251777899038220873651 40083377666848557331310477)
                ·
                  refine ⟨15031266625068208999241429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40083377666848557331310477 15031266625068208999241429)
                  ·
                    refine ⟨352295311525036148419721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15031266625068208999241429 352295311525036148419721)
                    ·
                      rfl

theorem cell22_1029139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_1029139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029139 prefixEnd_1029139 := by exact prefixLift 1029139
  have htrace : WordTrace (prefixWord ++ tailWord_1029139) baseStart_1029139 baseEnd_1029139 := by
    simpa [prefixWord, tailWord_1029139, baseEnd_1029139] using wordTrace_append hprefix tailTrace_1029139
  have hstable : (prefixWord ++ tailWord_1029139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029139).length < 2 ^ (prefixWord ++ tailWord_1029139).sum := by decide
  have hdescent : baseEnd_1029139 < baseStart_1029139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029201 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1029201 : Nat := 118140960795 + 1029201 * 2 ^ 59
def prefixEnd_1029201 : Nat := 4983230072969 + 3 ^ 40 * 1029201 * 2
def baseEnd_1029201 : Nat := 352316535392088653369531

theorem tailTrace_1029201 : CollatzResearch.WordTrace tailWord_1029201 prefixEnd_1029201 352316535392088653369531 := by
  unfold tailWord_1029201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37538044344388025381863457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25025362896258683587908971 37538044344388025381863457)
  ·
    refine ⟨28153533258291019036397593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37538044344388025381863457 28153533258291019036397593)
    ·
      refine ⟨21115149943718264277298195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28153533258291019036397593 21115149943718264277298195)
      ·
        refine ⟨31672724915577396415947293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21115149943718264277298195 31672724915577396415947293)
        ·
          refine ⟨11877271843341523655980235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31672724915577396415947293 11877271843341523655980235)
          ·
            refine ⟨17815907765012285483970353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877271843341523655980235 17815907765012285483970353)
            ·
              refine ⟨13361930823759214112977765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17815907765012285483970353 13361930823759214112977765)
              ·
                refine ⟨2505362029454852646183331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13361930823759214112977765 2505362029454852646183331)
                ·
                  refine ⟨3758043044182278969274997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505362029454852646183331 3758043044182278969274997)
                  ·
                    refine ⟨352316535392088653369531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3758043044182278969274997 352316535392088653369531)
                    ·
                      rfl

theorem cell22_1029201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1029201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029201 prefixEnd_1029201 := by exact prefixLift 1029201
  have htrace : WordTrace (prefixWord ++ tailWord_1029201) baseStart_1029201 baseEnd_1029201 := by
    simpa [prefixWord, tailWord_1029201, baseEnd_1029201] using wordTrace_append hprefix tailTrace_1029201
  have hstable : (prefixWord ++ tailWord_1029201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029201).length < 2 ^ (prefixWord ++ tailWord_1029201).sum := by decide
  have hdescent : baseEnd_1029201 < baseStart_1029201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029231 : List Nat := [1, 1, 2, 1, 3, 3, 4, 7]
def baseStart_1029231 : Nat := 118140960795 + 1029231 * 2 ^ 59
def prefixEnd_1029231 : Nat := 4983230072969 + 3 ^ 40 * 1029231 * 2
def baseEnd_1029231 : Nat := 39147422778353175013271

theorem tailTrace_1029231 : CollatzResearch.WordTrace tailWord_1029231 prefixEnd_1029231 39147422778353175013271 := by
  unfold tailWord_1029231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539138534279340505455547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25026092356186227003637031 37539138534279340505455547)
  ·
    refine ⟨56308707801419010758183321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37539138534279340505455547 56308707801419010758183321)
    ·
      refine ⟨42231530851064258068637491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56308707801419010758183321 42231530851064258068637491)
      ·
        refine ⟨63347296276596387102956237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42231530851064258068637491 63347296276596387102956237)
        ·
          refine ⟨23755236103723645163608589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63347296276596387102956237 23755236103723645163608589)
          ·
            refine ⟨8908213538896366936353221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23755236103723645163608589 8908213538896366936353221)
            ·
              refine ⟨1670290038543068800566229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8908213538896366936353221 1670290038543068800566229)
              ·
                refine ⟨39147422778353175013271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1670290038543068800566229 39147422778353175013271)
                ·
                  rfl

theorem cell22_1029231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 7].length) (baseStart_1029231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029231 prefixEnd_1029231 := by exact prefixLift 1029231
  have htrace : WordTrace (prefixWord ++ tailWord_1029231) baseStart_1029231 baseEnd_1029231 := by
    simpa [prefixWord, tailWord_1029231, baseEnd_1029231] using wordTrace_append hprefix tailTrace_1029231
  have hstable : (prefixWord ++ tailWord_1029231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029231).length < 2 ^ (prefixWord ++ tailWord_1029231).sum := by decide
  have hdescent : baseEnd_1029231 < baseStart_1029231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029282 : List Nat := [3, 3, 1, 3, 3, 1, 1, 7]
def baseStart_1029282 : Nat := 118140960795 + 1029282 * 2 ^ 59
def prefixEnd_1029282 : Nat := 4983230072969 + 3 ^ 40 * 1029282 * 2
def baseEnd_1029282 : Nat := 39149362594159049121587

theorem tailTrace_1029282 : CollatzResearch.WordTrace tailWord_1029282 prefixEnd_1029282 39149362594159049121587 := by
  unfold tailWord_1029282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385249664273644053890525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25027332438063050810374733 9385249664273644053890525)
  ·
    refine ⟨3519468624102616520208947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9385249664273644053890525 3519468624102616520208947)
    ·
      refine ⟨5279202936153924780313421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519468624102616520208947 5279202936153924780313421)
      ·
        refine ⟨1979701101057721792617533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5279202936153924780313421 1979701101057721792617533)
        ·
          refine ⟨742387912896645672231575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1979701101057721792617533 742387912896645672231575)
          ·
            refine ⟨1113581869344968508347363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742387912896645672231575 1113581869344968508347363)
            ·
              refine ⟨1670372804017452762521045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113581869344968508347363 1670372804017452762521045)
              ·
                refine ⟨39149362594159049121587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1670372804017452762521045 39149362594159049121587)
                ·
                  rfl

theorem cell22_1029282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_1029282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029282 prefixEnd_1029282 := by exact prefixLift 1029282
  have htrace : WordTrace (prefixWord ++ tailWord_1029282) baseStart_1029282 baseEnd_1029282 := by
    simpa [prefixWord, tailWord_1029282, baseEnd_1029282] using wordTrace_append hprefix tailTrace_1029282
  have hstable : (prefixWord ++ tailWord_1029282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029282).length < 2 ^ (prefixWord ++ tailWord_1029282).sum := by decide
  have hdescent : baseEnd_1029282 < baseStart_1029282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029353 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_1029353 : Nat := 118140960795 + 1029353 * 2 ^ 59
def prefixEnd_1029353 : Nat := 4983230072969 + 3 ^ 40 * 1029353 * 2
def baseEnd_1029353 : Nat := 352368568098410923569065

theorem tailTrace_1029353 : CollatzResearch.WordTrace tailWord_1029353 prefixEnd_1029353 352368568098410923569065 := by
  unfold tailWord_1029353
  simp only [CollatzResearch.WordTrace]
  refine ⟨37543588239837355341396713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25029058826558236894264475 37543588239837355341396713)
  ·
    refine ⟨28157691179878016506047535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37543588239837355341396713 28157691179878016506047535)
    ·
      refine ⟨42236536769817024759071303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28157691179878016506047535 42236536769817024759071303)
      ·
        refine ⟨63354805154725537138606955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42236536769817024759071303 63354805154725537138606955)
        ·
          refine ⟨95032207732088305707910433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63354805154725537138606955 95032207732088305707910433)
          ·
            refine ⟨71274155799066229280932825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95032207732088305707910433 71274155799066229280932825)
            ·
              refine ⟨53455616849299671960699619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71274155799066229280932825 53455616849299671960699619)
              ·
                refine ⟨80183425273949507941049429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53455616849299671960699619 80183425273949507941049429)
                ·
                  refine ⟨939649514929095796184173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 80183425273949507941049429 939649514929095796184173)
                  ·
                    refine ⟨352368568098410923569065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939649514929095796184173 352368568098410923569065)
                    ·
                      rfl

theorem cell22_1029353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_1029353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029353 prefixEnd_1029353 := by exact prefixLift 1029353
  have htrace : WordTrace (prefixWord ++ tailWord_1029353) baseStart_1029353 baseEnd_1029353 := by
    simpa [prefixWord, tailWord_1029353, baseEnd_1029353] using wordTrace_append hprefix tailTrace_1029353
  have hstable : (prefixWord ++ tailWord_1029353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029353).length < 2 ^ (prefixWord ++ tailWord_1029353).sum := by decide
  have hdescent : baseEnd_1029353 < baseStart_1029353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029357 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1029357 : Nat := 118140960795 + 1029357 * 2 ^ 59
def prefixEnd_1029357 : Nat := 4983230072969 + 3 ^ 40 * 1029357 * 2
def baseEnd_1029357 : Nat := 352369937380156246469053

theorem tailTrace_1029357 : CollatzResearch.WordTrace tailWord_1029357 prefixEnd_1029357 352369937380156246469053 := by
  unfold tailWord_1029357
  simp only [CollatzResearch.WordTrace]
  refine ⟨37543734131822864024542325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25029156087881909349694883 37543734131822864024542325)
  ·
    refine ⟨3519725074858393502300843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37543734131822864024542325 3519725074858393502300843)
    ·
      refine ⟨5279587612287590253451265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519725074858393502300843 5279587612287590253451265)
      ·
        refine ⟨3959690709215692690088449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5279587612287590253451265 3959690709215692690088449)
        ·
          refine ⟨2969768031911769517566337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3959690709215692690088449 2969768031911769517566337)
          ·
            refine ⟨2227326023933827138174753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969768031911769517566337 2227326023933827138174753)
            ·
              refine ⟨1670494517950370353631065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227326023933827138174753 1670494517950370353631065)
              ·
                refine ⟨1252870888462777765223299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670494517950370353631065 1252870888462777765223299)
                ·
                  refine ⟨1879306332694166647834949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252870888462777765223299 1879306332694166647834949)
                  ·
                    refine ⟨352369937380156246469053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879306332694166647834949 352369937380156246469053)
                    ·
                      rfl

theorem cell22_1029357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1029357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029357 prefixEnd_1029357 := by exact prefixLift 1029357
  have htrace : WordTrace (prefixWord ++ tailWord_1029357) baseStart_1029357 baseEnd_1029357 := by
    simpa [prefixWord, tailWord_1029357, baseEnd_1029357] using wordTrace_append hprefix tailTrace_1029357
  have hstable : (prefixWord ++ tailWord_1029357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029357).length < 2 ^ (prefixWord ++ tailWord_1029357).sum := by decide
  have hdescent : baseEnd_1029357 < baseStart_1029357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029432 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_1029432 : Nat := 118140960795 + 1029432 * 2 ^ 59
def prefixEnd_1029432 : Nat := 4983230072969 + 3 ^ 40 * 1029432 * 2
def baseEnd_1029432 : Nat := 352395611412881050843823

theorem tailTrace_1029432 : CollatzResearch.WordTrace tailWord_1029432 prefixEnd_1029432 352395611412881050843823 := by
  unfold tailWord_1029432
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773234803275575916761275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25030979737700767889015033 18773234803275575916761275)
  ·
    refine ⟨28159852204913363875141913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18773234803275575916761275 28159852204913363875141913)
    ·
      refine ⟨21119889153685022906356435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28159852204913363875141913 21119889153685022906356435)
      ·
        refine ⟨31679833730527534359534653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21119889153685022906356435 31679833730527534359534653)
        ·
          refine ⟨11879937648947825384825495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31679833730527534359534653 11879937648947825384825495)
          ·
            refine ⟨17819906473421738077238243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879937648947825384825495 17819906473421738077238243)
            ·
              refine ⟨26729859710132607115857365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819906473421738077238243 26729859710132607115857365)
              ·
                refine ⟨626481086956232979277907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26729859710132607115857365 626481086956232979277907)
                ·
                  refine ⟨939721630434349468916861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626481086956232979277907 939721630434349468916861)
                  ·
                    refine ⟨352395611412881050843823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939721630434349468916861 352395611412881050843823)
                    ·
                      rfl

theorem cell22_1029432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_1029432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029432 prefixEnd_1029432 := by exact prefixLift 1029432
  have htrace : WordTrace (prefixWord ++ tailWord_1029432) baseStart_1029432 baseEnd_1029432 := by
    simpa [prefixWord, tailWord_1029432, baseEnd_1029432] using wordTrace_append hprefix tailTrace_1029432
  have hstable : (prefixWord ++ tailWord_1029432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029432).length < 2 ^ (prefixWord ++ tailWord_1029432).sum := by decide
  have hdescent : baseEnd_1029432 < baseStart_1029432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029443 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_1029443 : Nat := 118140960795 + 1029443 * 2 ^ 59
def prefixEnd_1029443 : Nat := 4983230072969 + 3 ^ 40 * 1029443 * 2
def baseEnd_1029443 : Nat := 352399376937680688818789

theorem tailTrace_1029443 : CollatzResearch.WordTrace tailWord_1029443 prefixEnd_1029443 352399376937680688818789 := by
  unfold tailWord_1029443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37546870809511300712172983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25031247206340867141448655 37546870809511300712172983)
  ·
    refine ⟨56320306214266951068259475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37546870809511300712172983 56320306214266951068259475)
    ·
      refine ⟨84480459321400426602389213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56320306214266951068259475 84480459321400426602389213)
      ·
        refine ⟨31680172245525159975895955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84480459321400426602389213 31680172245525159975895955)
        ·
          refine ⟨47520258368287739963843933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31680172245525159975895955 47520258368287739963843933)
          ·
            refine ⟨17820096888107902486441475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47520258368287739963843933 17820096888107902486441475)
            ·
              refine ⟨26730145332161853729662213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17820096888107902486441475 26730145332161853729662213)
              ·
                refine ⟨5011902249780347574311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26730145332161853729662213 5011902249780347574311665)
                ·
                  refine ⟨3758926687335260680733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011902249780347574311665 3758926687335260680733749)
                  ·
                    refine ⟨352399376937680688818789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3758926687335260680733749 352399376937680688818789)
                    ·
                      rfl

theorem cell22_1029443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_1029443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029443 prefixEnd_1029443 := by exact prefixLift 1029443
  have htrace : WordTrace (prefixWord ++ tailWord_1029443) baseStart_1029443 baseEnd_1029443 := by
    simpa [prefixWord, tailWord_1029443, baseEnd_1029443] using wordTrace_append hprefix tailTrace_1029443
  have hstable : (prefixWord ++ tailWord_1029443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029443).length < 2 ^ (prefixWord ++ tailWord_1029443).sum := by decide
  have hdescent : baseEnd_1029443 < baseStart_1029443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029449 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_1029449 : Nat := 118140960795 + 1029449 * 2 ^ 59
def prefixEnd_1029449 : Nat := 4983230072969 + 3 ^ 40 * 1029449 * 2
def baseEnd_1029449 : Nat := 352401430860298673168771

theorem tailTrace_1029449 : CollatzResearch.WordTrace tailWord_1029449 prefixEnd_1029449 352401430860298673168771 := by
  unfold tailWord_1029449
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547089647489563736891401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25031393098326375824594267 37547089647489563736891401)
  ·
    refine ⟨28160317235617172802668551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37547089647489563736891401 28160317235617172802668551)
    ·
      refine ⟨42240475853425759204002827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28160317235617172802668551 42240475853425759204002827)
      ·
        refine ⟨63360713780138638806004241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42240475853425759204002827 63360713780138638806004241)
        ·
          refine ⟨47520535335103979104503181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63360713780138638806004241 47520535335103979104503181)
          ·
            refine ⟨17820200750663992164188693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47520535335103979104503181 17820200750663992164188693)
            ·
              refine ⟨835321910187374632696345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17820200750663992164188693 835321910187374632696345)
              ·
                refine ⟨626491432640530974522259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835321910187374632696345 626491432640530974522259)
                ·
                  refine ⟨939737148960796461783389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626491432640530974522259 939737148960796461783389)
                  ·
                    refine ⟨352401430860298673168771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939737148960796461783389 352401430860298673168771)
                    ·
                      rfl

theorem cell22_1029449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_1029449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029449 prefixEnd_1029449 := by exact prefixLift 1029449
  have htrace : WordTrace (prefixWord ++ tailWord_1029449) baseStart_1029449 baseEnd_1029449 := by
    simpa [prefixWord, tailWord_1029449, baseEnd_1029449] using wordTrace_append hprefix tailTrace_1029449
  have hstable : (prefixWord ++ tailWord_1029449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029449).length < 2 ^ (prefixWord ++ tailWord_1029449).sum := by decide
  have hdescent : baseEnd_1029449 < baseStart_1029449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029460 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1029460 : Nat := 118140960795 + 1029460 * 2 ^ 59
def prefixEnd_1029460 : Nat := 4983230072969 + 3 ^ 40 * 1029460 * 2
def baseEnd_1029460 : Nat := 352405196385098311143737

theorem tailTrace_1029460 : CollatzResearch.WordTrace tailWord_1029460 prefixEnd_1029460 352405196385098311143737 := by
  unfold tailWord_1029460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773745425224856307770917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25031660566966475077027889 18773745425224856307770917)
  ·
    refine ⟨3520077267229660557707047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18773745425224856307770917 3520077267229660557707047)
    ·
      refine ⟨5280115900844490836560571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520077267229660557707047 5280115900844490836560571)
      ·
        refine ⟨7920173851266736254840857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280115900844490836560571 7920173851266736254840857)
        ·
          refine ⟨5940130388450052191130643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920173851266736254840857 5940130388450052191130643)
          ·
            refine ⟨8910195582675078286695965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940130388450052191130643 8910195582675078286695965)
            ·
              refine ⟨3341323343503154357510987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8910195582675078286695965 3341323343503154357510987)
              ·
                refine ⟨5011985015254731536266481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341323343503154357510987 5011985015254731536266481)
                ·
                  refine ⟨3758988761441048652199861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011985015254731536266481 3758988761441048652199861)
                  ·
                    refine ⟨352405196385098311143737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3758988761441048652199861 352405196385098311143737)
                    ·
                      rfl

theorem cell22_1029460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1029460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029460 prefixEnd_1029460 := by exact prefixLift 1029460
  have htrace : WordTrace (prefixWord ++ tailWord_1029460) baseStart_1029460 baseEnd_1029460 := by
    simpa [prefixWord, tailWord_1029460, baseEnd_1029460] using wordTrace_append hprefix tailTrace_1029460
  have hstable : (prefixWord ++ tailWord_1029460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029460).length < 2 ^ (prefixWord ++ tailWord_1029460).sum := by decide
  have hdescent : baseEnd_1029460 < baseStart_1029460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029475 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_1029475 : Nat := 118140960795 + 1029475 * 2 ^ 59
def prefixEnd_1029475 : Nat := 4983230072969 + 3 ^ 40 * 1029475 * 2
def baseEnd_1029475 : Nat := 352410331191643272018691

theorem tailTrace_1029475 : CollatzResearch.WordTrace tailWord_1029475 prefixEnd_1029475 352410331191643272018691 := by
  unfold tailWord_1029475
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548037945395370177337879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25032025296930246784891919 37548037945395370177337879)
  ·
    refine ⟨56322056918093055266006819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37548037945395370177337879 56322056918093055266006819)
    ·
      refine ⟨84483085377139582899010229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56322056918093055266006819 84483085377139582899010229)
      ·
        refine ⟨7920289254106835896782209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84483085377139582899010229 7920289254106835896782209)
        ·
          refine ⟨5940216940580126922586657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920289254106835896782209 5940216940580126922586657)
          ·
            refine ⟨4455162705435095191939993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940216940580126922586657 4455162705435095191939993)
            ·
              refine ⟨3341372029076321393954995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455162705435095191939993 3341372029076321393954995)
              ·
                refine ⟨5012058043614482090932493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341372029076321393954995 5012058043614482090932493)
                ·
                  refine ⟨1879521766355430784099685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5012058043614482090932493 1879521766355430784099685)
                  ·
                    refine ⟨352410331191643272018691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879521766355430784099685 352410331191643272018691)
                    ·
                      rfl

theorem cell22_1029475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_1029475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029475 prefixEnd_1029475 := by exact prefixLift 1029475
  have htrace : WordTrace (prefixWord ++ tailWord_1029475) baseStart_1029475 baseEnd_1029475 := by
    simpa [prefixWord, tailWord_1029475, baseEnd_1029475] using wordTrace_append hprefix tailTrace_1029475
  have hstable : (prefixWord ++ tailWord_1029475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029475).length < 2 ^ (prefixWord ++ tailWord_1029475).sum := by decide
  have hdescent : baseEnd_1029475 < baseStart_1029475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029503 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1029503 : Nat := 118140960795 + 1029503 * 2 ^ 59
def prefixEnd_1029503 : Nat := 4983230072969 + 3 ^ 40 * 1029503 * 2
def baseEnd_1029503 : Nat := 352419916163860532318605

theorem tailTrace_1029503 : CollatzResearch.WordTrace tailWord_1029503 prefixEnd_1029503 352419916163860532318605 := by
  unfold tailWord_1029503
  simp only [CollatzResearch.WordTrace]
  refine ⟨37549059189293930959357163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25032706126195953972904775 37549059189293930959357163)
  ·
    refine ⟨56323588783940896439035745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37549059189293930959357163 56323588783940896439035745)
    ·
      refine ⟨42242691587955672329276809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56323588783940896439035745 42242691587955672329276809)
      ·
        refine ⟨31682018690966754246957607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42242691587955672329276809 31682018690966754246957607)
        ·
          refine ⟨47523028036450131370436411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31682018690966754246957607 47523028036450131370436411)
          ·
            refine ⟨71284542054675197055654617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47523028036450131370436411 71284542054675197055654617)
            ·
              refine ⟨53463406541006397791740963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71284542054675197055654617 53463406541006397791740963)
              ·
                refine ⟨80195109811509596687611445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53463406541006397791740963 80195109811509596687611445)
                ·
                  refine ⟨7518291544829024689463573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80195109811509596687611445 7518291544829024689463573)
                  ·
                    refine ⟨352419916163860532318605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7518291544829024689463573 352419916163860532318605)
                    ·
                      rfl

theorem cell22_1029503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1029503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029503 prefixEnd_1029503 := by exact prefixLift 1029503
  have htrace : WordTrace (prefixWord ++ tailWord_1029503) baseStart_1029503 baseEnd_1029503 := by
    simpa [prefixWord, tailWord_1029503, baseEnd_1029503] using wordTrace_append hprefix tailTrace_1029503
  have hstable : (prefixWord ++ tailWord_1029503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029503).length < 2 ^ (prefixWord ++ tailWord_1029503).sum := by decide
  have hdescent : baseEnd_1029503 < baseStart_1029503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029507 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 4]
def baseStart_1029507 : Nat := 118140960795 + 1029507 * 2 ^ 59
def prefixEnd_1029507 : Nat := 4983230072969 + 3 ^ 40 * 1029507 * 2
def baseEnd_1029507 : Nat := 117473761815201951739531

theorem tailTrace_1029507 : CollatzResearch.WordTrace tailWord_1029507 prefixEnd_1029507 117473761815201951739531 := by
  unfold tailWord_1029507
  simp only [CollatzResearch.WordTrace]
  refine ⟨37549205081279439642502775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25032803387519626428335183 37549205081279439642502775)
  ·
    refine ⟨56323807621919159463754163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37549205081279439642502775 56323807621919159463754163)
    ·
      refine ⟨84485711432878739195631245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56323807621919159463754163 84485711432878739195631245)
      ·
        refine ⟨31682141787329527198361717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84485711432878739195631245 31682141787329527198361717)
        ·
          refine ⟨2970200792562143174846411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31682141787329527198361717 2970200792562143174846411)
          ·
            refine ⟨4455301188843214762269617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970200792562143174846411 4455301188843214762269617)
            ·
              refine ⟨3341475891632411071702213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455301188843214762269617 3341475891632411071702213)
              ·
                refine ⟨626526729681077075944165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3341475891632411071702213 626526729681077075944165)
                ·
                  refine ⟨117473761815201951739531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626526729681077075944165 117473761815201951739531)
                  ·
                    rfl

theorem cell22_1029507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 4].length) (baseStart_1029507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029507 prefixEnd_1029507 := by exact prefixLift 1029507
  have htrace : WordTrace (prefixWord ++ tailWord_1029507) baseStart_1029507 baseEnd_1029507 := by
    simpa [prefixWord, tailWord_1029507, baseEnd_1029507] using wordTrace_append hprefix tailTrace_1029507
  have hstable : (prefixWord ++ tailWord_1029507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029507).length < 2 ^ (prefixWord ++ tailWord_1029507).sum := by decide
  have hdescent : baseEnd_1029507 < baseStart_1029507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029535 : List Nat := [1, 1, 2, 5, 1, 3, 1, 8]
def baseStart_1029535 : Nat := 118140960795 + 1029535 * 2 ^ 59
def prefixEnd_1029535 : Nat := 4983230072969 + 3 ^ 40 * 1029535 * 2
def baseEnd_1029535 : Nat := 39158985601980346168723

theorem tailTrace_1029535 : CollatzResearch.WordTrace tailWord_1029535 prefixEnd_1029535 39158985601980346168723 := by
  unfold tailWord_1029535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550226325178000424522059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25033484216785333616348039 37550226325178000424522059)
  ·
    refine ⟨56325339487767000636783089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37550226325178000424522059 56325339487767000636783089)
    ·
      refine ⟨42244004615825250477587317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56325339487767000636783089 42244004615825250477587317)
      ·
        refine ⟨3960375432733617232273811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42244004615825250477587317 3960375432733617232273811)
        ·
          refine ⟨5940563149100425848410717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960375432733617232273811 5940563149100425848410717)
          ·
            refine ⟨2227711180912659693154019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5940563149100425848410717 2227711180912659693154019)
            ·
              refine ⟨3341566771368989539731029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227711180912659693154019 3341566771368989539731029)
              ·
                refine ⟨39158985601980346168723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3341566771368989539731029 39158985601980346168723)
                ·
                  rfl

theorem cell22_1029535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 8].length) (baseStart_1029535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029535 prefixEnd_1029535 := by exact prefixLift 1029535
  have htrace : WordTrace (prefixWord ++ tailWord_1029535) baseStart_1029535 baseEnd_1029535 := by
    simpa [prefixWord, tailWord_1029535, baseEnd_1029535] using wordTrace_append hprefix tailTrace_1029535
  have hstable : (prefixWord ++ tailWord_1029535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029535).length < 2 ^ (prefixWord ++ tailWord_1029535).sum := by decide
  have hdescent : baseEnd_1029535 < baseStart_1029535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029565 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1029565 : Nat := 118140960795 + 1029565 * 2 ^ 59
def prefixEnd_1029565 : Nat := 4983230072969 + 3 ^ 40 * 1029565 * 2
def baseEnd_1029565 : Nat := 352441140030913037268415

theorem tailTrace_1029565 : CollatzResearch.WordTrace tailWord_1029565 prefixEnd_1029565 352441140030913037268415 := by
  unfold tailWord_1029565
  simp only [CollatzResearch.WordTrace]
  refine ⟨37551320515069315548114149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25034213676712877032076099 37551320515069315548114149)
  ·
    refine ⟨7040872596575496665271403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37551320515069315548114149 7040872596575496665271403)
    ·
      refine ⟨10561308894863244997907105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040872596575496665271403 10561308894863244997907105)
      ·
        refine ⟨7920981671147433748430329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10561308894863244997907105 7920981671147433748430329)
        ·
          refine ⟨5940736253360575311322747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920981671147433748430329 5940736253360575311322747)
          ·
            refine ⟨8911104380040862966984121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940736253360575311322747 8911104380040862966984121)
            ·
              refine ⟨6683328285030647225238091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911104380040862966984121 6683328285030647225238091)
              ·
                refine ⟨10024992427545970837857137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683328285030647225238091 10024992427545970837857137)
                ·
                  refine ⟨7518744320659478128392853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10024992427545970837857137 7518744320659478128392853)
                  ·
                    refine ⟨352441140030913037268415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7518744320659478128392853 352441140030913037268415)
                    ·
                      rfl

theorem cell22_1029565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1029565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029565 prefixEnd_1029565 := by exact prefixLift 1029565
  have htrace : WordTrace (prefixWord ++ tailWord_1029565) baseStart_1029565 baseEnd_1029565 := by
    simpa [prefixWord, tailWord_1029565, baseEnd_1029565] using wordTrace_append hprefix tailTrace_1029565
  have hstable : (prefixWord ++ tailWord_1029565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029565).length < 2 ^ (prefixWord ++ tailWord_1029565).sum := by decide
  have hdescent : baseEnd_1029565 < baseStart_1029565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029618 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1029618 : Nat := 118140960795 + 1029618 * 2 ^ 59
def prefixEnd_1029618 : Nat := 4983230072969 + 3 ^ 40 * 1029618 * 2
def baseEnd_1029618 : Nat := 352459283014038565693253

theorem tailTrace_1029618 : CollatzResearch.WordTrace tailWord_1029618 prefixEnd_1029618 352459283014038565693253 := by
  unfold tailWord_1029618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388313395969326399948377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25035502389251537066529005 9388313395969326399948377)
  ·
    refine ⟨7041235046976994799961283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9388313395969326399948377 7041235046976994799961283)
    ·
      refine ⟨10561852570465492199941925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7041235046976994799961283 10561852570465492199941925)
      ·
        refine ⟨1980347356962279787489111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10561852570465492199941925 1980347356962279787489111)
        ·
          refine ⟨2970521035443419681233667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980347356962279787489111 2970521035443419681233667)
          ·
            refine ⟨4455781553165129521850501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970521035443419681233667 4455781553165129521850501)
            ·
              refine ⟨835459041218461785346969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4455781553165129521850501 835459041218461785346969)
              ·
                refine ⟨626594280913846339010227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835459041218461785346969 626594280913846339010227)
                ·
                  refine ⟨939891421370769508515341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626594280913846339010227 939891421370769508515341)
                  ·
                    refine ⟨352459283014038565693253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939891421370769508515341 352459283014038565693253)
                    ·
                      rfl

theorem cell22_1029618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1029618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029618 prefixEnd_1029618 := by exact prefixLift 1029618
  have htrace : WordTrace (prefixWord ++ tailWord_1029618) baseStart_1029618 baseEnd_1029618 := by
    simpa [prefixWord, tailWord_1029618, baseEnd_1029618] using wordTrace_append hprefix tailTrace_1029618
  have hstable : (prefixWord ++ tailWord_1029618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029618).length < 2 ^ (prefixWord ++ tailWord_1029618).sum := by decide
  have hdescent : baseEnd_1029618 < baseStart_1029618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029625 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 6]
def baseStart_1029625 : Nat := 118140960795 + 1029625 * 2 ^ 59
def prefixEnd_1029625 : Nat := 4983230072969 + 3 ^ 40 * 1029625 * 2
def baseEnd_1029625 : Nat := 117487226419030960256077

theorem tailTrace_1029625 : CollatzResearch.WordTrace tailWord_1029625 prefixEnd_1029625 117487226419030960256077 := by
  unfold tailWord_1029625
  simp only [CollatzResearch.WordTrace]
  refine ⟨37553508894851945795298329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25035672596567963863532219 37553508894851945795298329)
  ·
    refine ⟨28165131671138959346473747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37553508894851945795298329 28165131671138959346473747)
    ·
      refine ⟨42247697506708439019710621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28165131671138959346473747 42247697506708439019710621)
      ·
        refine ⟨15842886565015664632391483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42247697506708439019710621 15842886565015664632391483)
        ·
          refine ⟨23764329847523496948587225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15842886565015664632391483 23764329847523496948587225)
          ·
            refine ⟨17823247385642622711440419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23764329847523496948587225 17823247385642622711440419)
            ·
              refine ⟨26734871078463934067160629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823247385642622711440419 26734871078463934067160629)
              ·
                refine ⟨2506394163605993818796309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26734871078463934067160629 2506394163605993818796309)
                ·
                  refine ⟨117487226419030960256077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2506394163605993818796309 117487226419030960256077)
                  ·
                    rfl

theorem cell22_1029625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_1029625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029625 prefixEnd_1029625 := by exact prefixLift 1029625
  have htrace : WordTrace (prefixWord ++ tailWord_1029625) baseStart_1029625 baseEnd_1029625 := by
    simpa [prefixWord, tailWord_1029625, baseEnd_1029625] using wordTrace_append hprefix tailTrace_1029625
  have hstable : (prefixWord ++ tailWord_1029625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029625).length < 2 ^ (prefixWord ++ tailWord_1029625).sum := by decide
  have hdescent : baseEnd_1029625 < baseStart_1029625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029642 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_1029642 : Nat := 118140960795 + 1029642 * 2 ^ 59
def prefixEnd_1029642 : Nat := 4983230072969 + 3 ^ 40 * 1029642 * 2
def baseEnd_1029642 : Nat := 117489166234836834364393

theorem tailTrace_1029642 : CollatzResearch.WordTrace tailWord_1029642 prefixEnd_1029642 117489166234836834364393 := by
  unfold tailWord_1029642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388532233947589424666795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25036085957193571799111453 9388532233947589424666795)
  ·
    refine ⟨14082798350921384137000193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9388532233947589424666795 14082798350921384137000193)
    ·
      refine ⟨10562098763191038102750145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14082798350921384137000193 10562098763191038102750145)
      ·
        refine ⟨7921574072393278577062609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10562098763191038102750145 7921574072393278577062609)
        ·
          refine ⟨5941180554294958932796957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921574072393278577062609 5941180554294958932796957)
          ·
            refine ⟨2227942707860609599798859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5941180554294958932796957 2227942707860609599798859)
            ·
              refine ⟨3341914061790914399698289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227942707860609599798859 3341914061790914399698289)
              ·
                refine ⟨2506435546343185799773717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341914061790914399698289 2506435546343185799773717)
                ·
                  refine ⟨117489166234836834364393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2506435546343185799773717 117489166234836834364393)
                  ·
                    rfl

theorem cell22_1029642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_1029642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029642 prefixEnd_1029642 := by exact prefixLift 1029642
  have htrace : WordTrace (prefixWord ++ tailWord_1029642) baseStart_1029642 baseEnd_1029642 := by
    simpa [prefixWord, tailWord_1029642, baseEnd_1029642] using wordTrace_append hprefix tailTrace_1029642
  have hstable : (prefixWord ++ tailWord_1029642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029642).length < 2 ^ (prefixWord ++ tailWord_1029642).sum := by decide
  have hdescent : baseEnd_1029642 < baseStart_1029642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029674 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1029674 : Nat := 118140960795 + 1029674 * 2 ^ 59
def prefixEnd_1029674 : Nat := 4983230072969 + 3 ^ 40 * 1029674 * 2
def baseEnd_1029674 : Nat := 352478452958473086293081

theorem tailTrace_1029674 : CollatzResearch.WordTrace tailWord_1029674 prefixEnd_1029674 352478452958473086293081 := by
  unfold tailWord_1029674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388824017918606790958019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25036864047782951442554717 9388824017918606790958019)
  ·
    refine ⟨14083236026877910186437029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9388824017918606790958019 14083236026877910186437029)
    ·
      refine ⟨2640606755039608159956943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14083236026877910186437029 2640606755039608159956943)
      ·
        refine ⟨3960910132559412239935415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640606755039608159956943 3960910132559412239935415)
        ·
          refine ⟨5941365198839118359903123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960910132559412239935415 5941365198839118359903123)
          ·
            refine ⟨8912047798258677539854685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941365198839118359903123 8912047798258677539854685)
            ·
              refine ⟨3342017924347004077445507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8912047798258677539854685 3342017924347004077445507)
              ·
                refine ⟨5013026886520506116168261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342017924347004077445507 5013026886520506116168261)
                ·
                  refine ⟨939942541222594896781549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5013026886520506116168261 939942541222594896781549)
                  ·
                    refine ⟨352478452958473086293081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939942541222594896781549 352478452958473086293081)
                    ·
                      rfl

theorem cell22_1029674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1029674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029674 prefixEnd_1029674 := by exact prefixLift 1029674
  have htrace : WordTrace (prefixWord ++ tailWord_1029674) baseStart_1029674 baseEnd_1029674 := by
    simpa [prefixWord, tailWord_1029674, baseEnd_1029674] using wordTrace_append hprefix tailTrace_1029674
  have hstable : (prefixWord ++ tailWord_1029674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029674).length < 2 ^ (prefixWord ++ tailWord_1029674).sum := by decide
  have hdescent : baseEnd_1029674 < baseStart_1029674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029732 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1029732 : Nat := 118140960795 + 1029732 * 2 ^ 59
def prefixEnd_1029732 : Nat := 4983230072969 + 3 ^ 40 * 1029732 * 2
def baseEnd_1029732 : Nat := 117499435847926756114301

theorem tailTrace_1029732 : CollatzResearch.WordTrace tailWord_1029732 prefixEnd_1029732 117499435847926756114301 := by
  unfold tailWord_1029732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778705752732151534721725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25038274336976202046295633 18778705752732151534721725)
  ·
    refine ⟨7042014657274556825520647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18778705752732151534721725 7042014657274556825520647)
    ·
      refine ⟨10563021985911835238280971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042014657274556825520647 10563021985911835238280971)
      ·
        refine ⟨15844532978867752857421457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10563021985911835238280971 15844532978867752857421457)
        ·
          refine ⟨11883399734150814643066093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15844532978867752857421457 11883399734150814643066093)
          ·
            refine ⟨4456274900306555491149785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11883399734150814643066093 4456274900306555491149785)
            ·
              refine ⟨3342206175229916618362339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456274900306555491149785 3342206175229916618362339)
              ·
                refine ⟨5013309262844874927543509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342206175229916618362339 5013309262844874927543509)
                ·
                  refine ⟨117499435847926756114301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5013309262844874927543509 117499435847926756114301)
                  ·
                    rfl

theorem cell22_1029732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1029732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029732 prefixEnd_1029732 := by exact prefixLift 1029732
  have htrace : WordTrace (prefixWord ++ tailWord_1029732) baseStart_1029732 baseEnd_1029732 := by
    simpa [prefixWord, tailWord_1029732, baseEnd_1029732] using wordTrace_append hprefix tailTrace_1029732
  have hstable : (prefixWord ++ tailWord_1029732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029732).length < 2 ^ (prefixWord ++ tailWord_1029732).sum := by decide
  have hdescent : baseEnd_1029732 < baseStart_1029732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029736 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1029736 : Nat := 118140960795 + 1029736 * 2 ^ 59
def prefixEnd_1029736 : Nat := 4983230072969 + 3 ^ 40 * 1029736 * 2
def baseEnd_1029736 : Nat := 352499676825525591242891

theorem tailTrace_1029736 : CollatzResearch.WordTrace tailWord_1029736 prefixEnd_1029736 352499676825525591242891 := by
  unfold tailWord_1029736
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778778698724905876294531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25038371598299874501726041 18778778698724905876294531)
  ·
    refine ⟨28168168048087358814441797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18778778698724905876294531 28168168048087358814441797)
    ·
      refine ⟨5281531509016379777707837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28168168048087358814441797 5281531509016379777707837)
      ·
        refine ⟨1980574315881142416640439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5281531509016379777707837 1980574315881142416640439)
        ·
          refine ⟨2970861473821713624960659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980574315881142416640439 2970861473821713624960659)
          ·
            refine ⟨4456292210732570437440989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970861473821713624960659 4456292210732570437440989)
            ·
              refine ⟨1671109579024713914040371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4456292210732570437440989 1671109579024713914040371)
              ·
                refine ⟨2506664368537070871060557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671109579024713914040371 2506664368537070871060557)
                ·
                  refine ⟨939999138201401576647709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2506664368537070871060557 939999138201401576647709)
                  ·
                    refine ⟨352499676825525591242891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 939999138201401576647709 352499676825525591242891)
                    ·
                      rfl

theorem cell22_1029736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1029736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029736 prefixEnd_1029736 := by exact prefixLift 1029736
  have htrace : WordTrace (prefixWord ++ tailWord_1029736) baseStart_1029736 baseEnd_1029736 := by
    simpa [prefixWord, tailWord_1029736, baseEnd_1029736] using wordTrace_append hprefix tailTrace_1029736
  have hstable : (prefixWord ++ tailWord_1029736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029736).length < 2 ^ (prefixWord ++ tailWord_1029736).sum := by decide
  have hdescent : baseEnd_1029736 < baseStart_1029736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029807 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1029807 : Nat := 118140960795 + 1029807 * 2 ^ 59
def prefixEnd_1029807 : Nat := 4983230072969 + 3 ^ 40 * 1029807 * 2
def baseEnd_1029807 : Nat := 352523981576505072717673

theorem tailTrace_1029807 : CollatzResearch.WordTrace tailWord_1029807 prefixEnd_1029807 352523981576505072717673 := by
  unfold tailWord_1029807
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560146980192590878423675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040097986795060585615783 37560146980192590878423675)
  ·
    refine ⟨56340220470288886317635513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37560146980192590878423675 56340220470288886317635513)
    ·
      refine ⟨42255165352716664738226635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56340220470288886317635513 42255165352716664738226635)
      ·
        refine ⟨63382748029074997107339953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255165352716664738226635 63382748029074997107339953)
        ·
          refine ⟨47537061021806247830504965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63382748029074997107339953 47537061021806247830504965)
          ·
            refine ⟨8913198941588671468219681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47537061021806247830504965 8913198941588671468219681)
            ·
              refine ⟨6684899206191503601164761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8913198941588671468219681 6684899206191503601164761)
              ·
                refine ⟨5013674404643627700873571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684899206191503601164761 5013674404643627700873571)
                ·
                  refine ⟨7520511606965441551310357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013674404643627700873571 7520511606965441551310357)
                  ·
                    refine ⟨352523981576505072717673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7520511606965441551310357 352523981576505072717673)
                    ·
                      rfl

theorem cell22_1029807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1029807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029807 prefixEnd_1029807 := by exact prefixLift 1029807
  have htrace : WordTrace (prefixWord ++ tailWord_1029807) baseStart_1029807 baseEnd_1029807 := by
    simpa [prefixWord, tailWord_1029807, baseEnd_1029807] using wordTrace_append hprefix tailTrace_1029807
  have hstable : (prefixWord ++ tailWord_1029807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029807).length < 2 ^ (prefixWord ++ tailWord_1029807).sum := by decide
  have hdescent : baseEnd_1029807 < baseStart_1029807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029830 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1029830 : Nat := 118140960795 + 1029830 * 2 ^ 59
def prefixEnd_1029830 : Nat := 4983230072969 + 3 ^ 40 * 1029830 * 2
def baseEnd_1029830 : Nat := 352531854946540679392603

theorem tailTrace_1029830 : CollatzResearch.WordTrace tailWord_1029830 prefixEnd_1029830 352531854946540679392603 := by
  unfold tailWord_1029830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173780808097164556453467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25040657239406177204340629 1173780808097164556453467)
  ·
    refine ⟨1760671212145746834680201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173780808097164556453467 1760671212145746834680201)
    ·
      refine ⟨1320503409109310126010151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760671212145746834680201 1320503409109310126010151)
      ·
        refine ⟨1980755113663965189015227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320503409109310126010151 1980755113663965189015227)
        ·
          refine ⟨2971132670495947783522841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980755113663965189015227 2971132670495947783522841)
          ·
            refine ⟨2228349502871960837642131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971132670495947783522841 2228349502871960837642131)
            ·
              refine ⟨3342524254307941256463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228349502871960837642131 3342524254307941256463197)
              ·
                refine ⟨1253446595365477971173699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342524254307941256463197 1253446595365477971173699)
                ·
                  refine ⟨1880169893048216956760549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253446595365477971173699 1880169893048216956760549)
                  ·
                    refine ⟨352531854946540679392603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880169893048216956760549 352531854946540679392603)
                    ·
                      rfl

theorem cell22_1029830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1029830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029830 prefixEnd_1029830 := by exact prefixLift 1029830
  have htrace : WordTrace (prefixWord ++ tailWord_1029830) baseStart_1029830 baseEnd_1029830 := by
    simpa [prefixWord, tailWord_1029830, baseEnd_1029830] using wordTrace_append hprefix tailTrace_1029830
  have hstable : (prefixWord ++ tailWord_1029830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029830).length < 2 ^ (prefixWord ++ tailWord_1029830).sum := by decide
  have hdescent : baseEnd_1029830 < baseStart_1029830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029944 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1029944 : Nat := 118140960795 + 1029944 * 2 ^ 59
def prefixEnd_1029944 : Nat := 4983230072969 + 3 ^ 40 * 1029944 * 2
def baseEnd_1029944 : Nat := 352570879476282382042253

theorem tailTrace_1029944 : CollatzResearch.WordTrace tailWord_1029944 prefixEnd_1029944 352570879476282382042253 := by
  unfold tailWord_1029944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18782571890348131638080443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25043429187130842184107257 18782571890348131638080443)
  ·
    refine ⟨28173857835522197457120665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18782571890348131638080443 28173857835522197457120665)
    ·
      refine ⟨21130393376641648092840499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28173857835522197457120665 21130393376641648092840499)
      ·
        refine ⟨31695590064962472139260749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21130393376641648092840499 31695590064962472139260749)
        ·
          refine ⟨11885846274360927052222781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31695590064962472139260749 11885846274360927052222781)
          ·
            refine ⟨4457192352885347644583543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11885846274360927052222781 4457192352885347644583543)
            ·
              refine ⟨6685788529328021466875315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457192352885347644583543 6685788529328021466875315)
              ·
                refine ⟨10028682793992032200312973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685788529328021466875315 10028682793992032200312973)
                ·
                  refine ⟨3760756047747012075117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10028682793992032200312973 3760756047747012075117365)
                  ·
                    refine ⟨352570879476282382042253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3760756047747012075117365 352570879476282382042253)
                    ·
                      rfl

theorem cell22_1029944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1029944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029944 prefixEnd_1029944 := by exact prefixLift 1029944
  have htrace : WordTrace (prefixWord ++ tailWord_1029944) baseStart_1029944 baseEnd_1029944 := by
    simpa [prefixWord, tailWord_1029944, baseEnd_1029944] using wordTrace_append hprefix tailTrace_1029944
  have hstable : (prefixWord ++ tailWord_1029944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029944).length < 2 ^ (prefixWord ++ tailWord_1029944).sum := by decide
  have hdescent : baseEnd_1029944 < baseStart_1029944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029991 : List Nat := [1, 1, 5, 1, 2, 1, 5, 6]
def baseStart_1029991 : Nat := 118140960795 + 1029991 * 2 ^ 59
def prefixEnd_1029991 : Nat := 4983230072969 + 3 ^ 40 * 1029991 * 2
def baseEnd_1029991 : Nat := 39176329837421102901901

theorem tailTrace_1029991 : CollatzResearch.WordTrace tailWord_1029991 prefixEnd_1029991 39176329837421102901901 := by
  unfold tailWord_1029991
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566858011525990303121827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25044572007683993535414551 37566858011525990303121827)
  ·
    refine ⟨56350287017288985454682741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37566858011525990303121827 56350287017288985454682741)
    ·
      refine ⟨5282839407870842386376507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56350287017288985454682741 5282839407870842386376507)
      ·
        refine ⟨7924259111806263579564761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5282839407870842386376507 7924259111806263579564761)
        ·
          refine ⟨5943194333854697684673571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7924259111806263579564761 5943194333854697684673571)
          ·
            refine ⟨8914791500782046527010357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943194333854697684673571 8914791500782046527010357)
            ·
              refine ⟨835761703198316861907221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8914791500782046527010357 835761703198316861907221)
              ·
                refine ⟨39176329837421102901901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835761703198316861907221 39176329837421102901901)
                ·
                  rfl

theorem cell22_1029991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 6].length) (baseStart_1029991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1029991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1029991 prefixEnd_1029991 := by exact prefixLift 1029991
  have htrace : WordTrace (prefixWord ++ tailWord_1029991) baseStart_1029991 baseEnd_1029991 := by
    simpa [prefixWord, tailWord_1029991, baseEnd_1029991] using wordTrace_append hprefix tailTrace_1029991
  have hstable : (prefixWord ++ tailWord_1029991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029991).length < 2 ^ (prefixWord ++ tailWord_1029991).sum := by decide
  have hdescent : baseEnd_1029991 < baseStart_1029991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030126 : List Nat := [4, 1, 2, 1, 3, 11]
def baseStart_1030126 : Nat := 118140960795 + 1030126 * 2 ^ 59
def prefixEnd_1030126 : Nat := 4983230072969 + 3 ^ 40 * 1030126 * 2
def baseEnd_1030126 : Nat := 4353496071551784864095

theorem tailTrace_1030126 : CollatzResearch.WordTrace tailWord_1030126 prefixEnd_1030126 4353496071551784864095 := by
  unfold tailWord_1030126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696472733254613544910779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25047854577357938906190821 4696472733254613544910779)
  ·
    refine ⟨7044709099881920317366169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696472733254613544910779 7044709099881920317366169)
    ·
      refine ⟨5283531824911440238024627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7044709099881920317366169 5283531824911440238024627)
      ·
        refine ⟨7925297737367160357036941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283531824911440238024627 7925297737367160357036941)
        ·
          refine ⟨2971986651512685133888853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7925297737367160357036941 2971986651512685133888853)
          ·
            refine ⟨4353496071551784864095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2971986651512685133888853 4353496071551784864095)
            ·
              rfl

theorem cell22_1030126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 11].length) (baseStart_1030126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030126 prefixEnd_1030126 := by exact prefixLift 1030126
  have htrace : WordTrace (prefixWord ++ tailWord_1030126) baseStart_1030126 baseEnd_1030126 := by
    simpa [prefixWord, tailWord_1030126, baseEnd_1030126] using wordTrace_append hprefix tailTrace_1030126
  have hstable : (prefixWord ++ tailWord_1030126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030126).length < 2 ^ (prefixWord ++ tailWord_1030126).sum := by decide
  have hdescent : baseEnd_1030126 < baseStart_1030126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030156 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1030156 : Nat := 118140960795 + 1030156 * 2 ^ 59
def prefixEnd_1030156 : Nat := 4983230072969 + 3 ^ 40 * 1030156 * 2
def baseEnd_1030156 : Nat := 352643451408784495741603

theorem tailTrace_1030156 : CollatzResearch.WordTrace tailWord_1030156 prefixEnd_1030156 352643451408784495741603 := by
  unfold tailWord_1030156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786438027964111741439161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25048584037285482321918881 18786438027964111741439161)
  ·
    refine ⟨14089828520973083806079371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18786438027964111741439161 14089828520973083806079371)
    ·
      refine ⟨21134742781459625709119057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14089828520973083806079371 21134742781459625709119057)
      ·
        refine ⟨15851057086094719281839293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21134742781459625709119057 15851057086094719281839293)
        ·
          refine ⟨5944146407285519730689735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15851057086094719281839293 5944146407285519730689735)
          ·
            refine ⟨8916219610928279596034603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944146407285519730689735 8916219610928279596034603)
            ·
              refine ⟨13374329416392419394051905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916219610928279596034603 13374329416392419394051905)
              ·
                refine ⟨10030747062294314545538929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13374329416392419394051905 10030747062294314545538929)
                ·
                  refine ⟨7523060296720735909154197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10030747062294314545538929 7523060296720735909154197)
                  ·
                    refine ⟨352643451408784495741603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7523060296720735909154197 352643451408784495741603)
                    ·
                      rfl

theorem cell22_1030156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1030156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030156 prefixEnd_1030156 := by exact prefixLift 1030156
  have htrace : WordTrace (prefixWord ++ tailWord_1030156) baseStart_1030156 baseEnd_1030156 := by
    simpa [prefixWord, tailWord_1030156, baseEnd_1030156] using wordTrace_append hprefix tailTrace_1030156
  have hstable : (prefixWord ++ tailWord_1030156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030156).length < 2 ^ (prefixWord ++ tailWord_1030156).sum := by decide
  have hdescent : baseEnd_1030156 < baseStart_1030156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030205 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 5]
def baseStart_1030205 : Nat := 118140960795 + 1030205 * 2 ^ 59
def prefixEnd_1030205 : Nat := 4983230072969 + 3 ^ 40 * 1030205 * 2
def baseEnd_1030205 : Nat := 117553408370054900422151

theorem tailTrace_1030205 : CollatzResearch.WordTrace tailWord_1030205 prefixEnd_1030205 117553408370054900422151 := by
  unfold tailWord_1030205
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574663232750704851412069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25049775488500469900941379 37574663232750704851412069)
  ·
    refine ⟨7045249356140757159639763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37574663232750704851412069 7045249356140757159639763)
    ·
      refine ⟨10567874034211135739459645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045249356140757159639763 10567874034211135739459645)
      ·
        refine ⟨3962952762829175902297367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10567874034211135739459645 3962952762829175902297367)
        ·
          refine ⟨5944429144243763853446051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962952762829175902297367 5944429144243763853446051)
          ·
            refine ⟨8916643716365645780169077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944429144243763853446051 8916643716365645780169077)
            ·
              refine ⟨835935348409279291890851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8916643716365645780169077 835935348409279291890851)
              ·
                refine ⟨1253903022613918937836277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835935348409279291890851 1253903022613918937836277)
                ·
                  refine ⟨117553408370054900422151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1253903022613918937836277 117553408370054900422151)
                  ·
                    rfl

theorem cell22_1030205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_1030205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030205 prefixEnd_1030205 := by exact prefixLift 1030205
  have htrace : WordTrace (prefixWord ++ tailWord_1030205) baseStart_1030205 baseEnd_1030205 := by
    simpa [prefixWord, tailWord_1030205, baseEnd_1030205] using wordTrace_append hprefix tailTrace_1030205
  have hstable : (prefixWord ++ tailWord_1030205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030205).length < 2 ^ (prefixWord ++ tailWord_1030205).sum := by decide
  have hdescent : baseEnd_1030205 < baseStart_1030205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030216 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_1030216 : Nat := 118140960795 + 1030216 * 2 ^ 59
def prefixEnd_1030216 : Nat := 4983230072969 + 3 ^ 40 * 1030216 * 2
def baseEnd_1030216 : Nat := 117554663544988113080473

theorem tailTrace_1030216 : CollatzResearch.WordTrace tailWord_1030216 prefixEnd_1030216 117554663544988113080473 := by
  unfold tailWord_1030216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787532217855426865031251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25050042957140569153375001 18787532217855426865031251)
  ·
    refine ⟨28181298326783140297546877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787532217855426865031251 28181298326783140297546877)
    ·
      refine ⟨10567986872543677611580079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28181298326783140297546877 10567986872543677611580079)
      ·
        refine ⟨15851980308815516417370119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567986872543677611580079 15851980308815516417370119)
        ·
          refine ⟨23777970463223274626055179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15851980308815516417370119 23777970463223274626055179)
          ·
            refine ⟨35666955694834911939082769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23777970463223274626055179 35666955694834911939082769)
            ·
              refine ⟨26750216771126183954312077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35666955694834911939082769 26750216771126183954312077)
              ·
                refine ⟨10031331289172318982867029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26750216771126183954312077 10031331289172318982867029)
                ·
                  refine ⟨117554663544988113080473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10031331289172318982867029 117554663544988113080473)
                  ·
                    rfl

theorem cell22_1030216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_1030216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030216 prefixEnd_1030216 := by exact prefixLift 1030216
  have htrace : WordTrace (prefixWord ++ tailWord_1030216) baseStart_1030216 baseEnd_1030216 := by
    simpa [prefixWord, tailWord_1030216, baseEnd_1030216] using wordTrace_append hprefix tailTrace_1030216
  have hstable : (prefixWord ++ tailWord_1030216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030216).length < 2 ^ (prefixWord ++ tailWord_1030216).sum := by decide
  have hdescent : baseEnd_1030216 < baseStart_1030216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030226 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1030226 : Nat := 118140960795 + 1030226 * 2 ^ 59
def prefixEnd_1030226 : Nat := 4983230072969 + 3 ^ 40 * 1030226 * 2
def baseEnd_1030226 : Nat := 352667413839327646491389

theorem tailTrace_1030226 : CollatzResearch.WordTrace tailWord_1030226 prefixEnd_1030226 352667413839327646491389 := by
  unfold tailWord_1030226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393857291418656359481633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25050286110449750291951021 9393857291418656359481633)
  ·
    refine ⟨7045392968563992269611225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9393857291418656359481633 7045392968563992269611225)
    ·
      refine ⟨5284044726422994202208419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7045392968563992269611225 5284044726422994202208419)
      ·
        refine ⟨7926067089634491303312629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284044726422994202208419 7926067089634491303312629)
        ·
          refine ⟨743068789653233559685559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7926067089634491303312629 743068789653233559685559)
          ·
            refine ⟨1114603184479850339528339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743068789653233559685559 1114603184479850339528339)
            ·
              refine ⟨1671904776719775509292509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114603184479850339528339 1671904776719775509292509)
              ·
                refine ⟨626964291269915815984691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671904776719775509292509 626964291269915815984691)
                ·
                  refine ⟨940446436904873723977037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626964291269915815984691 940446436904873723977037)
                  ·
                    refine ⟨352667413839327646491389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940446436904873723977037 352667413839327646491389)
                    ·
                      rfl

theorem cell22_1030226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1030226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030226 prefixEnd_1030226 := by exact prefixLift 1030226
  have htrace : WordTrace (prefixWord ++ tailWord_1030226) baseStart_1030226 baseEnd_1030226 := by
    simpa [prefixWord, tailWord_1030226, baseEnd_1030226] using wordTrace_append hprefix tailTrace_1030226
  have hstable : (prefixWord ++ tailWord_1030226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030226).length < 2 ^ (prefixWord ++ tailWord_1030226).sum := by decide
  have hdescent : baseEnd_1030226 < baseStart_1030226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030280 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1030280 : Nat := 118140960795 + 1030280 * 2 ^ 59
def prefixEnd_1030280 : Nat := 4983230072969 + 3 ^ 40 * 1030280 * 2
def baseEnd_1030280 : Nat := 352685899142889505641223

theorem tailTrace_1030280 : CollatzResearch.WordTrace tailWord_1030280 prefixEnd_1030280 352685899142889505641223 := by
  unfold tailWord_1030280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788699353739496330196147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25051599138319328440261529 18788699353739496330196147)
  ·
    refine ⟨28183049030609244495294221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18788699353739496330196147 28183049030609244495294221)
    ·
      refine ⟨10568643386478466685735333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28183049030609244495294221 10568643386478466685735333)
      ·
        refine ⟨1981620634964712503575375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10568643386478466685735333 1981620634964712503575375)
        ·
          refine ⟨2972430952447068755363063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981620634964712503575375 2972430952447068755363063)
          ·
            refine ⟨4458646428670603133044595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972430952447068755363063 4458646428670603133044595)
            ·
              refine ⟨6687969643005904699566893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458646428670603133044595 6687969643005904699566893)
              ·
                refine ⟨2507988616127214262337585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687969643005904699566893 2507988616127214262337585)
                ·
                  refine ⟨1880991462095410696753189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507988616127214262337585 1880991462095410696753189)
                  ·
                    refine ⟨352685899142889505641223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880991462095410696753189 352685899142889505641223)
                    ·
                      rfl

theorem cell22_1030280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1030280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030280 prefixEnd_1030280 := by exact prefixLift 1030280
  have htrace : WordTrace (prefixWord ++ tailWord_1030280) baseStart_1030280 baseEnd_1030280 := by
    simpa [prefixWord, tailWord_1030280, baseEnd_1030280] using wordTrace_append hprefix tailTrace_1030280
  have hstable : (prefixWord ++ tailWord_1030280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030280).length < 2 ^ (prefixWord ++ tailWord_1030280).sum := by decide
  have hdescent : baseEnd_1030280 < baseStart_1030280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
